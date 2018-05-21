//check for [TA]
//check for !!!
// Piterman.cpp : controller synthesis as in Piterman2006 article
#pragma comment(lib, "bdd.lib")	// BuDDy library
#include <vector>
#include "bdd.h"
#include <string>
#include <set>
#include <map>
#include <regex>
#include <fstream>
#include <ostream>
#include <sstream>
#include <time.h>

bdd p_e,//environment transition relation
	p_s,//system transition relation
	trans,//sythesised FDS
	init,//initial values
	obseq;//describes transitions where only jx strategy changes

std::ofstream out_strat;//[TA] temp!

std::vector<std::vector<std::vector<bdd>>> x_strat;//strategies for the system: leads the computation to J1-states
std::vector<std::vector<bdd>> y_strat;//strategy for the system: leads the computation to get closer to J2-states

std::vector<bdd>	J1,//vector of left-hand side (of the implication) boolean formulas. J1.size == m
					J2,//vector of right-hand side (of the implication) boolean formulas. J2.size == n
					fromjx,
					tojx;

//we code variables from X as {env1..env1+envCnt-1}: bdd_ithvarpp(env1), ..., bdd_ithvarpp(env1+envCnt-1) - these are environment variables
//we code variables from Y as {sys1..sys1+sysCnt-1}: bdd_ithvarpp(sys1), ..., bdd_ithvarpp(sys1+sysCnt-1) - these are system variables
unsigned env1,	//number of the first environment variable
		sys1,	//number of the first system variable
		env1_pr,//number of the first primed environment variable
		sys1_pr,//number of the first primed system variable
		envCnt,	//environment variables count
		sysCnt,	//system variables count
		//we code each jx (1..n) strategy in binary format using [log2(n)] binary variables:
		jx1,	//number of the first binary variable of jx
		jx1_pr,	//number of the first binary variable of primed jx
		jxCnt,	//jx binary variables count: jxCnt = log2(n)
		n,
		cox_cnt,
		gfpz_cnt,
		lfp_cnt,
		gfpx_cnt;//[TA]temp: delete this!!

long prevTime,time1, time1_1, time2, time2_2, time3, time4;//[TA]temp: delete this!!

int *env_sys_jx_arr,
	*primed_env_sys_jx_arr,
	*jx_pr_arr;

std::vector<std::string> varNames;

class State
{
private:
	bdd bddState;
	std::string name,	//unique and compact name for each state, e.g. s01101
				title;	//[TA]!!!!!
	
	bool initial;

	void setName() {
		name = "s";
		for (unsigned i = env1; i < env1 + envCnt; i++)
			name += ((bddState & bdd_ithvarpp(i)) != bddfalsepp) ? "1" : "0";
		for (unsigned i = sys1; i < sys1 + sysCnt; i++)
			name += ((bddState & bdd_ithvarpp(i)) != bddfalsepp) ? "1" : "0";
		for (unsigned i = jx1; i < jx1 + jxCnt; i++)
			name += ((bddState & bdd_ithvarpp(i)) != bddfalsepp) ? "1" : "0";
	}
	void setTitle() {
		title = "";
		
		for (unsigned i = env1; i < env1 + envCnt; i++)
			title += ithVarTitle(i) + ",";
		for (unsigned i = sys1; i < sys1 + sysCnt; i++)
			title += ithVarTitle(i) + ",";
		
		title += " ";
		title += ithJxTitle();
	}
	std::string ithVarTitle(unsigned i) {
		if (varNames.size() <= i) {//if environment and system variable names were not initialized
			return (name.size() > i) ? ""+name[i] : "";
		}

		return ((bddState & bdd_ithvarpp(i)) != bddfalsepp) ?
			varNames[i] :
			((bddState & !bdd_ithvarpp(i)) != bddfalsepp) ?
				"<O>" + varNames[i] + "</O>" :
				"";
	}
	std::string ithJxTitle() {
		int jx_ind = 0;
		for (unsigned i = jx1; i < jx1 + jxCnt; i++) {
			jx_ind *= 2;
			if ((bddState & bdd_ithvarpp(i)) != bddfalsepp)
				jx_ind += 1;
		}
		return "jx" + std::to_string(jx_ind + 1);
	}

public:
	State() {
		bddState = bddfalsepp;
		setName();
		setTitle();
	}
    State(bdd allVarsBDD, bool ifFrom) {
		bddState = allVarsBDD;
		if (ifFrom) {//we receive transition BDD, if we should take from-state, we delete all primed variables
			bddState = bdd_exist(bddState, bdd_makeset(primed_env_sys_jx_arr, envCnt + sysCnt + jxCnt));
		} else {//we receive transition BDD, if we should take to-state, we delete all unprimed variables (from-states)
				//and unprime other (primed) variables - we convert to-states into from-states
			bddState = bdd_exist(bddState, bdd_makeset(env_sys_jx_arr, envCnt + sysCnt + jxCnt));
			
			bddPair *pairs = bdd_newpair();
			for (unsigned i = 0; i < envCnt; i++)
				bdd_setpair(pairs, env1_pr + i, env1 + i);
			for (unsigned i = 0; i < sysCnt; i++)
				bdd_setpair(pairs, sys1_pr + i, sys1 + i);
			for (unsigned i = 0; i < jxCnt; i++)
				bdd_setpair(pairs, jx1_pr + i, jx1 + i);
			bddState = bdd_replace(bddState, pairs);
		}
		
		setName();
		setTitle();
		initial = ((init & bddState) != bddfalsepp) ? true : false;
    }
	std::string getName() { return name; }

	std::string getTitle() { return title; }

	bool ifInitial() { return initial; }
};//end class State

class Variable;
class SMVModule;//check - may be delete!!!

class Variable {
private:
	std::string name;
	int id;

	unsigned log2(int k) {
		unsigned log = 0;
		while (k >>= 1) log++;
		return log;
	}// end log2

public:
	//constructors:
	Variable(std::string name_str) {
		name = name_str;
		id = bdd_varnum();
		bdd_extvarnum(2);
	}
	Variable(std::string var_name, int var_id) {//if we just want to create a copy of variable
		name = var_name;
		id = var_id;
	}
	Variable(std::string name_str, std::vector<std::string> values) {
		name = name_str;
		id = bdd_varnum();//??!!!
		bdd_extvarnum(log2(values.size()) * 2);
	}
	// end constructors
	std::string Name() { return name; }
	int Id() { return id; }
	int NextId() { return id + 1; }
	bdd varBDD() { return bdd_ithvar(id); }
	bdd next() { return bdd_ithvar(id + 1); }// возможно, удалить этот метод
};

class SMVModule {
private:
	std::string moduleName;
	std::vector<Variable> vars;
	std::vector<Variable> externalVars;

	bdd initial;
	bdd transition;
	bdd justice;
public:
	SMVModule() {
		moduleName = "";
		initial = bddfalsepp;
		transition = bddtruepp;
		justice = bddtruepp;
	}
	SMVModule(std::string name) {
		moduleName = name;
		initial = bddfalsepp;
		transition = bddtruepp;
		justice = bddtruepp;
	}

	std::string GetName() { return moduleName; }

	void SetName(std::string name) { moduleName = name; }
	
	bdd GetInitial() { return initial; }

	void SetInitial(bdd ini) { initial = ini; }
	
	bool check_ifVariableExist(std::string varName) {
		for (unsigned i = 0; i < vars.size(); i++)
			if (varName == vars[i].Name()) return true;
		for (unsigned i = 0; i < externalVars.size(); i++)
			if (varName == externalVars[i].Name()) return true;
		//else
		return false;
	}

	Variable GetVariable(std::string varName) {
		for (unsigned i = 0; i < vars.size(); i++)
			if (varName == vars[i].Name()) return vars[i];
		for (unsigned i = 0; i < externalVars.size(); i++)
			if (varName == externalVars[i].Name()) return externalVars[i];
		//else
		return NULL;
	}

	std::vector<Variable> GetInternalVariables() { return vars; }

	/*std::set<Variable> GetAllVariables() {
		return vars !!! also add external vars;
	}*/

	std::vector<int> VariablesIds() { 
		std::vector<int> res;

		for (unsigned i = 0; i < vars.size(); i++) {
			res.push_back(vars[i].Id());
		}
		return res;
	}// change to static definition!!!

	std::vector<int> VariablesNextIds() { 
		std::vector<int> res;

		for (unsigned i = 0; i < vars.size(); i++) {
			res.push_back(vars[i].NextId());
		}
		return res;
	}// change to static definition!!!
	
	bool AddVariable(std::string varName) {
		for (unsigned i = 0; i < vars.size(); i++)
			if (varName == vars[i].Name()) return false;

		vars.push_back(Variable (varName));
		return true;
	}

	void AddExternalVariable(Variable ext_var) {
		externalVars.push_back(ext_var);
	}

	void SetTransition(bdd trans) {
		transition = trans;
	}

	bdd primeModuleVariables(bdd func) {
		static bddPair *modulePrimePairs = bdd_newpair();
		// !!!!!!!!!!!!!!!!!!!!!!! prime variables
		static bool b = true;
		if (b) { //[TA] change this condition!!!
			b = false;

			for (unsigned i = 0; i < vars.size(); i++)
				bdd_setpair(modulePrimePairs, vars[i].Id(), vars[i].NextId());
			for (unsigned i = 0; i < externalVars.size(); i++)
				bdd_setpair(modulePrimePairs, externalVars[i].Id(), externalVars[i].NextId());
		}

		return bdd_replace(func, modulePrimePairs);
	}// end primeModuleVariables
};//end class SMVModule

class FileText {
private:
	std::vector<std::string> text;
	std::vector<std::string> tokenText;
	std::vector<std::string> delims;
	std::vector<SMVModule*> allModules;

	std::pair<int, unsigned> getFirstDelimiterPos(std::vector<std::string> delims, std::string val) {
		std::pair<int, unsigned> min_index(val.size() + 1, delims.size());

		for (unsigned i = 0; i < delims.size(); i++) {//[TA] !!! need some optimisation
			int index = val.find(delims[i]);
			if ((index >= 0) && (index < min_index.first)) {
				min_index.first = index;
				min_index.second = i;
			}
		}

		return min_index;
	}
	
	std::pair<std::string, std::string> getToken(std::string str) {
		while ((str.size() > 0) && ((str[0] == ' ') || (str[0] == '\t'))) {
			str.erase(0, 1);
		}
		std::pair<int, unsigned> pos = getFirstDelimiterPos(delims, str);
		if ((pos.first == 0) && (pos.second < delims.size())) {
			return std::make_pair(delims[pos.second], str.erase(0, delims[pos.second].size()));
		} else {
			std::string part1 = str.substr(0, pos.first);
			return std::make_pair(part1, str.erase(0, pos.first));
		}
	}

	/* !!!!!!!!!!!!!!!!!!!!!!! prime variables*/bdd next(bdd func) {
		static bddPair *sysEnv_primePair = bdd_newpair();
		
		static bool b = true;
		bdd res = bddtruepp;//[TA] temp!!!!
		if (b) { //[TA] change this condition!!!
			b = false;
			for (unsigned i = 0; i < allModules.size(); i++) {
				std::vector<Variable> vars_ithSet = allModules[i]->GetInternalVariables();

				for (unsigned i = 0; i < vars_ithSet.size(); i++) {
					bdd_setpair(sysEnv_primePair, vars_ithSet[i].Id(), vars_ithSet[i].NextId());
				}
			}
		}

		return bdd_replace(func, sysEnv_primePair);
	}// end next

	SMVModule* GetModule(std::string moduleName) {
		for (unsigned i = 0; i < allModules.size(); i++)
			if (allModules[i]->GetName() == moduleName) return allModules[i];
		//else
		return NULL;//throw Exception
	}

	std::pair<int, bdd> getBDD(int i, std::string stop_sym, SMVModule* module) {
		bdd res = bddtrue;
		int prev_operator = bddop_and;

		std::map<std::string, int> operatorsMap;
			operatorsMap[")"] = -1;
			operatorsMap[";"] = -1;
			operatorsMap["&"] = bddop_and;
			operatorsMap["|"] = bddop_or;
			operatorsMap["->"] = bddop_imp;
			operatorsMap["="] = bddop_biimp;
			operatorsMap["!="] = bddop_xor; // ???!!!

		std::map<std::string, int> statesMap;
			statesMap["("] = 1;
			statesMap[")"] = 2;
			statesMap["!"] = 3;
			statesMap["next"] = 4;
			statesMap[";"] = 5;

		while(tokenText[i] != stop_sym) {//or until other special word
			switch(statesMap[tokenText[i]]) {
				case 1: {
					std::pair<int, bdd> temp = getBDD(++i, ")", module);
					i = temp.first;
					res = bdd_apply(res, temp.second, prev_operator);
					break;
				}
				case 2: {
					i++;
					break;
				}
				case 3: {
					if (tokenText[++i] == "(") {
						std::pair<int, bdd> temp = getBDD(++i, ")", module);
						i = temp.first;
						res = bdd_apply(res, bdd_not(temp.second), prev_operator);
					} else {
						res = bdd_apply(res, bdd_not(module->GetVariable(tokenText[i]).varBDD()), prev_operator);
					}
				}
				case 4: {
					if (tokenText[++i] != "(") { break; }// throw Exception!!!
					std::string a = tokenText[++i];
					/*
					Variable var = module.GetVariable(a);
					if (tokenText[++i] != ")") break; // throw Exception!!!
					res = bdd_apply(res, var.next(), prev_operator); // !!!!!!!!! check if here we prime the variables correct!
				*/}
				case 5: break;//throw Exception
				default: {//variable name by default
					if (module->check_ifVariableExist(tokenText[i])) {
						res = bdd_apply(res, module->GetVariable(tokenText[i]).varBDD(), prev_operator);
					} else {
						//throw Exception!!!
					}
				}
			}
			if (operatorsMap[tokenText[++i]] == -1) {//can be also ")" or ";"
				break;
			} else if (operatorsMap[tokenText[i]] > 0) {
				if (tokenText[i] == "!") {
					if (tokenText[i] == "=")
						prev_operator = bddop_xor;
				} else {
					prev_operator = operatorsMap[tokenText[i]];
				}
			} else break;// !!! throw Exception!
		}
		return std::pair<int, bdd>(i,res);
		// (!(r1 = g1) | (g1 = next(g1))) & (!(r2 = g2) | (g2 = next(g2))) & !(next(g1) & next(g2)) & ((t1 = 1) -> next(t1 = 1));
		//p_e = (bdd_xor(r1, g1) >> bdd_biimp(r1, r1_)) & (bdd_xor(r2, g2) >> bdd_biimp(r2, r2_));
		//p_s = !( g1_ & g2_) & (bdd_biimp(r1, g1) >> bdd_biimp(g1, g1_)) & (bdd_biimp(r2, g2) >> bdd_biimp(g2, g2_));
	}// end getBDD
public:
	FileText(std::string fileName) {
		std::ifstream file(fileName);

		//вызывается функция file.open();
		//file.open(filename); !!! удалить, если не нужно

		if (!file.is_open())
			std::cout << "File can not be opened!\n";//!!! use throw
		else {
			//getline(istream & is, string &s,char c='\n'),читает из потока is, в строку s пока не встретит символ c (без этого символа до новой строки)
			// возвращает свой объект istream, в условии проверяется состояние iostate флагa, значение этого флага будет ложным, если достигнет конца файла, или будет ошибка ввода или читаемого типа
			std::string tmp;
			while (getline(file,tmp))
				text.push_back(tmp + "\n");
		}
		file.close();

		delims.push_back(" "); delims.push_back("\t"); delims.push_back("\n"); delims.push_back("("); delims.push_back(".");
		delims.push_back(")"); delims.push_back("{"); delims.push_back("}"); delims.push_back("//"); delims.push_back("!");
		delims.push_back("/*"); delims.push_back("*/"); delims.push_back(","); delims.push_back(";"); delims.push_back(":=");

		tokenize();
	}
	
	void tokenize() {
		tokenText.clear();
		std::pair<std::string, std::string> token;
		for (unsigned i = 0; i < text.size(); i++) {
			token = getToken(text[i]);
			while(token.first != "") {
				tokenText.push_back(token.first);
				token = getToken(token.second);
			}
		}
	}
	
	std::vector<std::string> getModuleNames() {
		std::vector<std::string> res;
		return res;
	}

	void removeExtraData() {
		std::vector<std::string> tokens_clear;
		for (unsigned i = 0; i < tokenText.size(); i++) {
			if (tokenText[i] == "//") {
				while((tokenText[i] != "\n") && (tokenText[i] != "")) {
					i++;
				}
			}
			if (tokenText[i] == "/*") {
				while(tokenText[i++] != "*/")
					if (tokenText[i] == "") throw("Comment is not closed");
			}
			if ((tokenText[i] != "*/") && (tokenText[i] != "\n")) tokens_clear.push_back(tokenText[i]);
		}
		tokenText = tokens_clear;
	}

	void readMainSMVModule() {
		bool mainModuleExist = false;
		for (unsigned i = 0; i < tokenText.size(); i++) {
			if (tokenText[i] == "MODULE") {
				if (tokenText[++i] != "main") { continue; }
				mainModuleExist = true;
				if (tokenText[++i] != "VAR") mainModuleExist = false;//throw Exception!!!

				std::map<std::string, SMVModule*> modules;

				for (int j = i; tokenText[j] != "MODULE"; j++) {//read all modules names
					if (tokenText[j] == "VAR") j++;

					std::string module_temporary_name = tokenText[j];
					if (tokenText[++j] != ":") mainModuleExist = false;//throw Exception!!!
					std::string module_primary_name = tokenText[++j];

					// ?? may be add the test if moduleName is good?
					SMVModule newModule(module_primary_name);
					modules[module_temporary_name] = &newModule;
					allModules.push_back(&newModule);
					while(tokenText[++j] != ";") {}
				}
				SMVModule* otherModule;
				for (int j = i; tokenText[j] != "MODULE"; j++) {
					if (tokenText[j] == "VAR") j++;

					std::string module_temporary_name = tokenText[j];
					++j;//tokenText[++j] == ":"
					std::string module_primary_name = tokenText[++j];

					if (tokenText[++j] == "(") {
						while(tokenText[j] != ")") {
							std::string otherModuleName = tokenText[++j];// not needed for the first time.
							otherModule = modules[otherModuleName];
							if (tokenText[++j] != ".") mainModuleExist = false;// throw Exception!!!

							std::string varName = tokenText[++j];
							if (!otherModule->AddVariable(varName)) mainModuleExist = false;// throw Exception!!!

							GetModule(module_primary_name)->AddExternalVariable(otherModule->GetVariable(varName));
							if (tokenText[++j] == ",") continue;
						}
					}
					if (tokenText[j] != ";") {break;} // throw Exception!!!
				}
			}
		}
		if (!mainModuleExist) return;//throw Exception!!!
	}

	void getSMVModules() {
		bdd_init(10000000,1000000);//[TA] what to set here?
		bdd_setcacheratio(10);
		bdd_enable_reorder();

		readMainSMVModule();// здесь читается, какие будут модули, создаются пустые модули-элементы класса, описываются переменные.

		//!!!!!! 1st: getModuleVariables!
		SMVModule *module = NULL;
		for (unsigned i = 0; i < tokenText.size(); i++) {
			if (tokenText[i] == "MODULE") {
				for (unsigned j = 0; j < allModules.size(); j++) {
					if (allModules[j]->GetName() == tokenText[++i]) {
						module = allModules[j];
					}
				}// check if no module was found !!!

				if (tokenText[++i] == "(") {
					while(tokenText[++i] != ")") {}//later check if all external variables were defined earlier !!!
				}
				while (tokenText[++i] != "VAR") {
					if (i > tokenText.size()) break;
				}

				if (tokenText[i] == "VAR") {
					while ((tokenText[++i] != "INITIAL") && (tokenText[i] != "TRANS") && (tokenText[i] != "MODULE") && (tokenText[i] != "JUSTICE")) {
						// read MODULE variables
						std::string name = tokenText[i];
						if (tokenText[++i] != ":") { break; } // throw exception!!!
						std::string type = tokenText[++i];
						if (type == "boolean") {
							if (module == NULL) break;
							module->AddVariable(name);
						}

						if (tokenText[++i] != ";") { break; } // throw exception!!!
						//!!!add the case when variable has enumerable values
					}
				}
			}
		}

		for (unsigned m = 0; m < allModules.size(); m++) {
			//======================
			// Main parser!
			//======================
			//2nd: get initial values, transitions and Justice requirements
			int state = 0;
			std::string part;
			std::map<std::string, int> statesMap;
				statesMap["MODULE"] = -1; // not zero because if we read "MODULE" token while reading our module, this means our module description is ended
				statesMap["VAR"] = 3;
				statesMap["ASSIGN"] = 4;
				statesMap["TRANS"] = 5;
				statesMap["JUSTICE"] = 6;
				//statesMap[""]= 8;
		
			for (unsigned i = 0; i < tokenText.size(); i++) {
				switch(state) {
					//0: read module with requested name
					//1: read MODULE agruments
					//2: 
					//3: read MODULE variables
					//4: read MODULE initial values
					//5: read MODULE transition rules
					//: read MODULE justice requirements
					case 0: { // read MODULE with requested name
						//if (tmp.first == "") throw("NoSuchModuleException");//check how to throw exceptions!!!
						if (tokenText[i++] == "MODULE") {
							if (tokenText[i++] != allModules[m]->GetName()) { break; }//throw Exception!!!
							if (tokenText[i] == "(") { state = 1; i++; break; }
							state = 1;// ? think about it! зачем еще и здесь присваивать state=1? такие ситуации будут?
						}
						break;
					}
					case 1: { // read MODULE agruments
						//!!! temp:
						while(tokenText[++i] != ")") {
						}

						state = 2;
						part = tokenText[i++];
						break;
					}
					case 2: { // 
						state = statesMap[tokenText[i]];
						if (state > 0) { break; }
						// else
						//throw Exception!!!
						state = -1;
					}
					case 3: { // all MODULE variables were read earlier
						while (statesMap.find(tokenText[i]) == statesMap.end()) { i++; }
						break;
					}
					case 4: { // read MODULE initial values
						std::string token = tokenText[++i];
						if (statesMap[token] > 0) { state = statesMap[token]; break; }

						if (token != "init") { state = -1; break; } // throw exception!!!
						if (tokenText[++i] != "(") { state = -1; break; } // throw exception!!!
						std::string name = tokenText[++i];
						if (tokenText[++i] != ")") { state = -1; break; } // throw exception!!!
						if (tokenText[++i] != ":=") { state = -1; break; } // throw exception!!!
						std::string val = tokenText[++i];
						if (tokenText[++i] != ";") { state = -1; break; } // throw exception!!! check, may be we don't need it sometimes
						// !!! add initial values creating!!!
					}
					case 5: { // read MODULE transition rules
						std::string token = tokenText[++i];
						if (statesMap[token] > 0) { state = statesMap[token]; break; }
						std::pair<int, bdd> temp = getBDD(0, ";", allModules[m]);
						allModules[m]->SetTransition(temp.second);
					}
					case 6: { // read MODULE justice requirements
						std::string token = tokenText[++i];
					}
				}// end switch
			}
		}	
		//bdd_init(10000000,1000000);//[TA] what to set here?
		//bdd_setcacheratio(10);
	}
	
	void printFile(std::ostream& stream) {
		for (unsigned i = 0; i < text.size(); i++) {
			stream << text[i];
		}
	}
	void printFileTokens(std::ostream& stream) {
		for (unsigned i = 0; i < tokenText.size(); i++) {
			stream << tokenText[i] << " ";
		}
	}
};// end class FileText

class GRGame {
private:
	SMVModule sys;
	SMVModule env;
	std::vector<std::vector<std::vector<bdd>>> x_strat;//strategies for the system: leads the computation to J1-states
	std::vector<std::vector<bdd>> y_strat;//strategy for the system: leads the computation to get closer to J2-states

	bdd primeVariables_SysEnv(bdd vars) {
		static bddPair *sysEnv_primePair = bdd_newpair();
		static bool b = true;
		bdd res = bddtruepp;//[TA] temp!!!!
		if (b) { //[TA] change this condition!!!
			b = false;
			std::vector<Variable> sys_vars = sys.GetInternalVariables();
			std::vector<Variable> env_vars = sys.GetInternalVariables();
			for (unsigned i = 0; i < sys_vars.size(); i++)
				bdd_setpair(sysEnv_primePair, sys_vars[i].Id(), sys_vars[i].NextId());
			for (unsigned i = 0; i < env_vars.size(); i++)
				bdd_setpair(sysEnv_primePair, env_vars[i].Id(), env_vars[i].NextId());
		}

		return bdd_replace(vars, sysEnv_primePair);
	}// end primeVariables_SysEnv

	bdd step(bdd phi) { // function is named cox in the article
		static bdd p_s1 = p_s;
		static bdd p_e1 = p_e;
		static bdd sys_pr_arr_bdd = bddtruepp;//[TA] check: may be bddfalsepp
		if (sys_pr_arr_bdd == bddtruepp) {//[TA] this condition is to initialise sys_pr_arr_bdd only once
			int* sys_pr_arr = new int[sysCnt];
			for (unsigned i = 0; i < sysCnt; i++)
				sys_pr_arr[i] = sys1_pr + i;
			sys_pr_arr_bdd = bdd_makeset(sys_pr_arr, sysCnt);
			//sys_pr_arr_bdd = bdd_makeset();
		}

		//p_e => \exist y' such that (p_s and phi(x',y'))
		bdd res = bdd_imp(p_e1, bdd_exist(p_s1 & primeVariables_SysEnv(phi), sys_pr_arr_bdd));

		//\foreach x'
		for (unsigned i = env1_pr; i < env1_pr + envCnt; i++)
			res = bdd_forall(res, bdd_ithvarpp(i));
	
		return res;
	}// end step(cox)
	
public:
	GRGame(SMVModule env, SMVModule sys) {}
	void WinningRegion() {}
	void Synthesise() {}
	void Minimize() {}
};// end class GRGame

void readArbiter2Data(std::string filename) {
	//variables positions:
	//	0	1	2	3	4	5	6	7	8	9
	//	r1	r2	g1	g2	r1'	r2'	g1'	g2'	jx1	jx2
/*
	bdd_init(10000,1000);
	init = bddtrue;
	FileText env(), sys();
	for(int i = 0; i < file.size; i++) {
		tmp = getToken(file[i]);
		if (tmp.first != "MODULE") continue;
		//else
		if (getToken(tmp.second).first == "env") {
			env.push_back(file[i++]);
			while((i < file.size) && (getToken(file[i]).first != "MODULE"))
				env.push_back(file[i++]);
		}
		if (getToken(tmp.second).first == "sys") {
			sys.push_back(file[i++]);
			while((i < file.size) && (getToken(file[i]).first != "MODULE"))
				sys.push_back(file[i++]);
		}
		varNames.resize(4);
	}
	varNames[0] = "r1"; varNames[1] = "r2"; varNames[2] = "g1"; varNames[3] = "g2";
	
	env1 = 0;//r1, r2
	sys1 = 2;//g1, g2
	env1_pr = 4;//r1', r2'
	sys1_pr = 6;//g1', g2'
	envCnt = 2;
	sysCnt = 2;
	
	bdd_setvarnum(envCnt * 2 + sysCnt * 2);

	bdd r1 = bdd_ithvarpp(0);
	bdd r2 = bdd_ithvarpp(1);
	bdd g1 = bdd_ithvarpp(2);
	bdd g2 = bdd_ithvarpp(3);
	bdd r1_ = bdd_ithvarpp(4);
	bdd r2_ = bdd_ithvarpp(5);
	bdd g1_ = bdd_ithvarpp(6);
	bdd g2_ = bdd_ithvarpp(7);
	
	p_e = (bdd_xor(r1, g1) >> bdd_biimp(r1, r1_))
		& (bdd_xor(r2, g2) >> bdd_biimp(r2, r2_));
	
	p_s = !( g1_ & g2_) 
		& (bdd_biimp(r1, g1) >> bdd_biimp(g1, g1_))
		& (bdd_biimp(r2, g2) >> bdd_biimp(g2, g2_));

	J1.resize(2);
	J2.resize(2);
	J1[0] = !(r1 & g1);
	J1[1] = !(r2 & g2);
	J2[0] = bdd_biimp(r1, g1);
	J2[1] = bdd_biimp(r2, g2);

	x_strat.resize(2);
	y_strat.resize(2);

	init = !r1 & !g1 & !r2 & !g2;*/
}// end readArbiter2Data

unsigned log2(int k) {
	unsigned log = 0;
	while (k >>= 1) log++;
	return log;
}// end log2

bdd bdd_ithfun(int f_num, int fromVar, unsigned varCnt) {
	//we code jx  variables as [sysCnt+envCnt			...		sysCnt+envCnt+ log2(n)-1]
	//we code jx_ variables as [sysCnt+envCnt+log2(n)	...		sysCnt+envCnt+2log2(n)-1]
	//if fromVar == jx1:	jx1 , jx2 , jx3 , ...
	//if fromVar == jx1_:	jx1', jx2', jx3', ...
	bdd fun = bddtruepp;
	for (unsigned i = 0; i < varCnt; i++)
		fun &= ((f_num >> i) & 1) ? bdd_ithvarpp(i + fromVar) : bdd_nithvarpp(i + fromVar);
	return fun;
}// end bdd_ithfun

bdd bdd_nithfun(int f_num, int from, int varCnt) {
	return bdd_ithfun(~f_num, from, varCnt);
}// end bdd_nithfunFromVar

bdd primeVariables_SysEnv(bdd vars) {
	static bddPair *sysEnv_primePair = bdd_newpair();
	static bool b = true;
	bdd res = bddtruepp;//[TA] temp!!!!
	if (b) { //[TA] change this condition!!!
		b = false;
		for (unsigned i = 0; i < sysCnt; i++)
			bdd_setpair(sysEnv_primePair, sys1 + i, sys1_pr + i);
		for (unsigned i = 0; i < envCnt; i++)
			bdd_setpair(sysEnv_primePair, env1 + i, env1_pr + i);
	}
	
	
	res = bdd_replace(vars, sysEnv_primePair);//[TA] temp!!
	
	return res;//[TA] temporary;
}// end primeVariables_SysEnv

bdd primeAllVariables(bdd vars) {
	static bddPair *allVars_primePair = bdd_newpair();

	static bool b = true;
	if (b) { //[TA] change this condition!!!
		b = false;

		for (unsigned i = 0; i < sysCnt; i++)
			bdd_setpair(allVars_primePair, sys1 + i, sys1_pr + i);
		for (unsigned i = 0; i < envCnt; i++)
			bdd_setpair(allVars_primePair, env1 + i, env1_pr + i);
		for (unsigned i = 0; i < jxCnt; i++)
			bdd_setpair(allVars_primePair, jx1 + i, jx1_pr + i);
	}
	return bdd_replace(vars, allVars_primePair);
}// end primeAllVariables

bdd unPrimeAllVariables(bdd vars) {
	bddPair *pairs = bdd_newpair();
	for (unsigned i = 0; i < sysCnt; i++)
		bdd_setpair(pairs, sys1_pr + i, sys1 + i);
	for (unsigned i = 0; i < envCnt; i++)
		bdd_setpair(pairs, env1_pr + i, env1 + i);
	for (unsigned i = 0; i < jxCnt; i++)
		bdd_setpair(pairs, jx1_pr + i, jx1 + i);
	
	return bdd_replace(vars, pairs);
}// end unPrimeAllVariables


/*bdd cox(bdd phi) {
	//p_e => \exist y' such that (p_s and phi(x',y'))
	bdd res = bdd_imp(p_e, bdd_exist(p_s & bdd_replace(phi, sysEnv_primePair), sys_pr_arr_bdd));
	//\foreach x'
	for (unsigned i = env1_pr; i < env1_pr + envCnt; i++)
		res = bdd_forall(res, bdd_ithvarpp(i));
	++cnt;
	return res;
}// end cox
*/
bdd cox(bdd phi) {
	static bdd p_s1 = p_s;
	static bdd p_e1 = p_e;
	static bdd sys_pr_arr_bdd = bddtruepp;//[TA] check: may be bddfalsepp
	if (sys_pr_arr_bdd == bddtruepp) {//[TA] this condition is to initialise sys_pr_arr_bdd only once
		int* sys_pr_arr = new int[sysCnt];
		for (unsigned i = 0; i < sysCnt; i++)
			sys_pr_arr[i] = sys1_pr + i;
		sys_pr_arr_bdd = bdd_makeset(sys_pr_arr, sysCnt);
	}

	//p_e => \exist y' such that (p_s and phi(x',y'))
	
	bdd temp1 = primeVariables_SysEnv(phi);
	time1 += clock() - prevTime;
	prevTime = clock();//[TA] delete this!!

	bdd temp1_1 = !temp1;////[TA] time: 14
	time1_1 += clock() - prevTime;
	prevTime = clock();//[TA] delete this!!
	
	bdd temp2_2 = p_s1 >> temp1;//[TA] time: 3000; 22914
	
	bdd temp2 = p_s1 & temp1;//[TA] time: 15289; 21385
	
	bdd temp3 = bdd_exist(temp2, sys_pr_arr_bdd);//[TA] time: ; 183
	
	bdd res = bdd_imp(p_e1, temp3);//[TA] time: ; 3348

	//\foreach x'
	for (unsigned i = env1_pr; i < env1_pr + envCnt; i++)
		res = bdd_forall(res, bdd_ithvarpp(i));
	
	return res;
}// end cox

bdd greatestFixPoint(bdd & z, bdd & start, int i) {
	bdd x = z,
		x_old;
	do {
		x_old = x;
		x = !J1[i] & cox (x) | start;
		cox_cnt++;//[TA] temp
		gfpx_cnt++;//[TA]temp!!!!
	} while(x_old != x);
	return x;
}// end greatestFixPoint

bdd leastFixPoint(bdd & z, int j) {
	bdd y = bddfalse,
		y_old,
		start,
		x;

	int r = 0;
	do {
		y_strat[j].resize(r + 1);
		x_strat[j].resize(r + 1);
		x_strat[j][r].resize(J1.size());

		y_old = y;
		start = J2[j] & cox(z) | cox(y);
		cox_cnt+=2;
		y = bddfalse;
		for (unsigned i = 0; i < J1.size(); i++) {
			x = greatestFixPoint(z, start, i);

			x_strat[j][r][i] = x;
			//[TA] temp! I used x[j][i][r] instead of x[j][r][i] to compare data with jtlv
			out_strat << "x[" << j << "][" << i << "][" << r << "]: " << x << std::endl;
			y |= x;
		}
		lfp_cnt++;//[TA]temp!!!!
		y_strat[j][r] = y;
		r++;
	} while (y_old != y);
	return y;
}// end leastFixPoint

bdd winm() {
	bdd z = bddtrue,
		z_old;

	do {//GratestFixPoint(z)
		z_old = z;
		gfpz_cnt++;//[TA]temp!!!!
		for (unsigned j = 0; j < J2.size(); j++)
			z = leastFixPoint(z, j);
	} while(z != z_old);
	return z;
}// end winm

void set_env_sys_jx_arr() {
	env_sys_jx_arr = new int[envCnt + sysCnt + jxCnt];
	
	for (unsigned i = 0; i < envCnt; i++)
		env_sys_jx_arr[i] = env1 + i;
	for (unsigned i = 0; i < sysCnt; i++)
		env_sys_jx_arr[envCnt + i] = sys1 + i;
	for (unsigned i = 0; i < jxCnt; i++)
		env_sys_jx_arr[envCnt + sysCnt + i] = jx1 + i;
}// end set_env_sys_jx_arr

void set_primed_env_sys_jx_arr() {
	primed_env_sys_jx_arr = new int[envCnt + sysCnt + jxCnt];
	
	for (unsigned i = 0; i < envCnt; i++)
		primed_env_sys_jx_arr[i] = env1_pr + i;
	for (unsigned i = 0; i < sysCnt; i++)
		primed_env_sys_jx_arr[envCnt + i] = sys1_pr + i;
	for (unsigned i = 0; i < jxCnt; i++)
		primed_env_sys_jx_arr[envCnt + sysCnt + i] = jx1_pr + i;
}// end set_primed_env_sys_jx_arr

void set_jx_pr_arr() {
	jx_pr_arr = new int[jxCnt];
	for (unsigned i = 0; i < jxCnt; i++)
		jx_pr_arr[i] = jx1_pr + i;
}// end set_jx_pr_arr

void setShoshminaTestData() {
	//[TA] variables position:
	//	0	1	2	3	4	5	
	//	p	q	p'	q'	jx1	jx1'
	varNames.resize(2);
	varNames[0] = "p"; varNames[1] = "q";
	
	env1 = 0;//p
	sys1 = 1;//q
	env1_pr = 2;//p'
	sys1_pr = 3;//q'
	envCnt = 1;
	sysCnt = 1;
	
	bdd_init(10000,1000);
	bdd_setvarnum(envCnt * 2 + sysCnt * 2);

	bdd p = bdd_ithvarpp(0);
	bdd q = bdd_ithvarpp(1);
	bdd p_ = bdd_ithvarpp(2);
	bdd q_ = bdd_ithvarpp(3);
	
	p_e = bddtruepp;
	p_s = bddtruepp;

	J1.resize(1);
	J2.resize(1);
	J1[0] = p;
	J2[0] = q;

	x_strat.resize(1);
	y_strat.resize(1);

	init = bddtruepp;
}// end setShoshminaTestData

void setArbter1Data() {
	//[TA] variables position:
	//	0	1	2	3	4	5	
	//	r	g	r'	g'	jx1	jx1'
	varNames.resize(2);
	varNames[0] = "r"; varNames[1] = "g";
	
	env1 = 0;//r
	sys1 = 1;//g
	env1_pr = 2;//r'
	sys1_pr = 3;//g'
	envCnt = 1;
	sysCnt = 1;
	
	bdd_init(10000,1000);
	bdd_setvarnum(envCnt * 2 + sysCnt * 2);

	bdd r = bdd_ithvarpp(0);
	bdd g = bdd_ithvarpp(1);
	bdd r_ = bdd_ithvarpp(2);
	bdd g_ = bdd_ithvarpp(3);
	
	p_e = bdd_xor(r, g) >> bdd_biimp(r, r_);
	p_s = bdd_biimp(r, g) >> bdd_biimp(g, g_);

	J1.resize(1);
	J2.resize(1);
	J1[0] = !(r & g);
	J2[0] = bdd_biimp(r, g);

	x_strat.resize(1);
	y_strat.resize(1);

	init = !r & !g;
}// end setArbter1Data

void setArbiter2Data() {
	//variables positions:
	//	0	1	2	3	4	5	6	7	8	9
	//	r1	r2	g1	g2	r1'	r2'	g1'	g2'	jx1	jx2
	varNames.resize(4); 
	varNames[0] = "r1"; varNames[1] = "r2"; varNames[2] = "g1"; varNames[3] = "g2";
	
	env1 = 0;//r1, r2
	sys1 = 2;//g1, g2
	env1_pr = 4;//r1', r2'
	sys1_pr = 6;//g1', g2'
	envCnt = 2;
	sysCnt = 2;
	
	bdd_init(10000,1000);
	bdd_setvarnum(envCnt * 2 + sysCnt * 2);

	bdd r1 = bdd_ithvarpp(0);
	bdd r2 = bdd_ithvarpp(1);
	bdd g1 = bdd_ithvarpp(2);
	bdd g2 = bdd_ithvarpp(3);
	bdd r1_ = bdd_ithvarpp(4);
	bdd r2_ = bdd_ithvarpp(5);
	bdd g1_ = bdd_ithvarpp(6);
	bdd g2_ = bdd_ithvarpp(7);
	
	p_e = (bdd_xor(r1, g1) >> bdd_biimp(r1, r1_))
		& (bdd_xor(r2, g2) >> bdd_biimp(r2, r2_));
	
	p_s = !( g1_ & g2_) 
		& (bdd_biimp(r1, g1) >> bdd_biimp(g1, g1_))
		& (bdd_biimp(r2, g2) >> bdd_biimp(g2, g2_));

	J1.resize(2);
	J2.resize(2);
	J1[0] = !(r1 & g1);
	J1[1] = !(r2 & g2);
	J2[0] = bdd_biimp(r1, g1);
	J2[1] = bdd_biimp(r2, g2);

	x_strat.resize(2);
	y_strat.resize(2);

	init = !r1 & !g1 & !r2 & !g2;
}// end setArbiter2Data

void universal_Arbiter_setData(unsigned N) {
	env1 = 0;//r_1, r_2, ..., r_N
	sys1 = N;//g_1, g_2, ..., g_N
	env1_pr = 2 * N;//r_1', r_2', ..., r_N'
	sys1_pr = 3 * N;//g_1', g_2', ..., g_N'
	envCnt = N;
	sysCnt = N;

	bdd_init(10000000,1000000);//[TA] what to set here?
	bdd_setcacheratio(10);
	bdd_setmaxincrease(100);
	bdd_enable_reorder();
	bdd_autoreorder(BDD_REORDER_WIN2);

	bdd_setvarnum(envCnt * 2 + sysCnt * 2);
	
	bdd ri, gi, ri_, gi_;
	p_e = bddtruepp;
	p_s = bddtruepp;
	init = bddtruepp;
	bdd p_s_part = bddtruepp;// added in order to reduce computational complexity of p_e
	
	J1.resize(N);
	J2.resize(N);

	//[TA] we go from N-1 to 0 in order to reduce computational complexity of p_e
	for (unsigned i = N; i > 0; i--) {
		ri = bdd_ithvarpp(env1 + i - 1);
		gi = bdd_ithvarpp(sys1 + i - 1);
		ri_ = bdd_ithvarpp(env1_pr + i - 1);
		gi_ = bdd_ithvarpp(sys1_pr + i - 1);
		
		p_e &= (bdd_xor(ri, gi) >> bdd_biimp(ri, ri_));

		p_s &= (!gi | p_s_part);
		p_s_part &= !gi;
		
		p_s &= (bdd_biimp(ri, gi) >> bdd_biimp(gi, gi_));

		init &= (!ri & !gi);

		J1[i - 1] = !(ri & gi);
		J2[i - 1] = bdd_biimp(ri, gi);
	}
	
	x_strat.resize(N);
	y_strat.resize(N);
}// end universal_Arbiter_setData

bdd toSymbStrategy(bdd z) {
	bdd trans = bddfalse;

	n = J2.size();
	jxCnt = log2(n);
	jx1 = bdd_varnum();//jx1 position
	jx1_pr = jx1 + jxCnt;//jx1' position

	set_env_sys_jx_arr();
	set_primed_env_sys_jx_arr();
	set_jx_pr_arr();

	unsigned m = J1.size();

	bdd_extvarnum(jxCnt * 2);//we extend variables count in order to use jx and jx'(jx_) variables additionally
	//set jx Codes
	fromjx.resize(n);
	tojx.resize(n);
	
	for (unsigned i = 0; i < n; i++) {
		fromjx[i] = bdd_ithfun(i, jx1, log2(n));
		tojx[i] = bdd_ithfun(i, jx1_pr, log2(n));
	}
	for (unsigned j = 0; j < n; j++) {
		trans |= fromjx[j] & tojx[(j + 1) % n] & z & J2[j] & p_e & p_s & primeVariables_SysEnv(z);
	}
	for (unsigned j = 0; j < n; j++) {
		bdd low = y_strat[j][0];
		for (unsigned r = 1; r < y_strat[j].size(); r++) {//maxr[j] == y_strat[j].size()
			trans |= fromjx[j] & tojx[j] & y_strat[j][r] & !low & p_e & p_s & primeVariables_SysEnv(low);
			low |= y_strat[j][r];
		}
	}
	for (unsigned j = 0; j < n; j++) {
		bdd low = bddfalse;
		for (unsigned r = 0; r < y_strat[j].size(); r++) {//maxr[j] == y_strat[j].size()
			for (unsigned i = 0; i < m; i++) {
				trans |= fromjx[j] & tojx[j] & x_strat[j][r][i] & !low & !J1[i] & p_e & p_s & primeVariables_SysEnv(x_strat[j][r][i]);
				low |= x_strat[j][r][i];
			}
		}
	}
	return trans;
}// end toSymbStrategy

bdd forsome_V(bdd fun) {
	//exist v' from V: env_pr, sys_pr or jx_pr
	return bdd_exist(fun, bdd_makeset(env_sys_jx_arr, envCnt + sysCnt + jxCnt));
}// end forsome_V

bdd forsome_next_V(bdd fun) {
	//exist v' from V: env_pr, sys_pr or jx_pr
	return bdd_exist(fun, bdd_makeset(primed_env_sys_jx_arr, envCnt + sysCnt + jxCnt));
}// end forsome_next_V

bdd forsome_next_jx(bdd fun) {
	//exist some primed jx
	return bdd_exist(fun, bdd_makeset(jx_pr_arr, jxCnt));
}// end forsome_next_jx

void reduce(int j, int k) {
	bdd states = forsome_next_V(trans & obseq & fromjx[j] & tojx[k]);
	bdd add_trans = forsome_next_jx(trans & primeAllVariables(states)) & tojx[k];
	bdd add_init = forsome_next_jx(init & states) & fromjx[k];
	trans = (trans & !(primeAllVariables(states) | states)) | add_trans;
	init = (init & !(states & fromjx[j])) | add_init;
}// end reduce

void minimize() {
	obseq = bddtrue;//obseq variable: describes transitions where only jx strategy changes
	for (unsigned i = 0; i < n; i++)
		obseq &= ! (fromjx[i] & tojx[i]);
	//and other variables doesn't change
	for (unsigned i = 0; i < envCnt; i++)
		obseq &= bdd_biimp(bdd_ithvarpp(env1 + i), bdd_ithvarpp(env1_pr + i));
	for (unsigned i = 0; i < sysCnt; i++)
		obseq &= bdd_biimp(bdd_ithvarpp(sys1 + i), bdd_ithvarpp(sys1_pr + i));

	//n == jxCnt
	std::ofstream out;
	for (unsigned j = 0; j < n; j++)
		reduce(j, (j + 1) % n);
	for (unsigned j = 0; j < n - 1; j++)
		reduce(n - 1, j);
}

void deleteStutteringTransitions(bdd & bddtrans) {
	//[TA] when should I implement this?
	//tmp: only stuttering transitions (from states to themselves)
	bdd stutter = bddtruepp;
	for (unsigned i = 0; i < jxCnt; i++)
		stutter &= bdd_biimp(bdd_ithvarpp(jx1 + i), bdd_ithvarpp(jx1_pr + i));
	for (unsigned i = 0; i < envCnt; i++)
		stutter &= bdd_biimp(bdd_ithvarpp(env1 + i), bdd_ithvarpp(env1_pr + i));
	for (unsigned i = 0; i < sysCnt; i++)
		stutter &= bdd_biimp(bdd_ithvarpp(sys1 + i), bdd_ithvarpp(sys1_pr + i));

	bddtrans &= !stutter;
}// end deleteStutteringTransitions

bool ifSingleDifferedTransition(bdd trans_fullsat) {//[TA] check if we need this?! Assumption: it is included in Piterman algorithm, but not specified in the article
	bool differs = false;
	//these checks are for arbiter problem: here we assume that envCnt == sysCnt
	for (unsigned i = 0; i < envCnt; i++) {
		if ((trans_fullsat & bdd_ithvarpp(env1 + i)) != (trans_fullsat & bdd_ithvarpp(env1_pr + i))) {
			if ((trans_fullsat & bdd_ithvarpp(sys1 + i)) == (trans_fullsat & bdd_ithvarpp(sys1_pr + i))) {
				if (differs) return false;
				differs = true;
			}
		}
	}
	for (unsigned i = 0; i < sysCnt; i++) {
		if ((trans_fullsat & bdd_ithvarpp(sys1 + i)) != (trans_fullsat & bdd_ithvarpp(sys1_pr + i))) {
			if (differs) return false;
			differs = true;
		}
	}
	return true;
}// end ifSingleDifferedTransition

bdd leaveOnlySingleDifferedTransitions(bdd bddtrans) {//[TA] check if we need this?! Assumption: it is included in Piterman algorithm, but not specified in the article
	bdd res = bddtrans,//[TA] change all names and check if it is right!!!!!!
		notPrinted = bddtrans,
		trans_curr_bdd;
	while(notPrinted != bddfalsepp) {
		trans_curr_bdd = bdd_fullsatone(notPrinted);
		if (!ifSingleDifferedTransition(trans_curr_bdd)) {
			res &= !trans_curr_bdd;
		}
		notPrinted &= !trans_curr_bdd;
	}
	deleteStutteringTransitions(res);
	return res;
}// end leaveOnlySingleDifferedTransitions

bdd allReachableTrans(bdd & bddTrans) {
	bdd res = init & bddTrans,
		res_old;
	do {
		res_old = res;
		res = res | (unPrimeAllVariables(forsome_V(res)) & bddTrans);
	} while(res_old != res);
	return res;
}// end allReachableTrans

int printDot(std::ostream &out, bdd & bddtrans)
{
	bdd nonPrinted_trans = allReachableTrans(bddtrans);
	bdd trans_curr_bdd;
	
	out<<"digraph G {"<<std::endl;
	std::set<std::string> printedNames;
	std::string color;
	
	out<<"init [shape = point, color = red];"<<std::endl;//[TA] проверить, почему точно будет init & trans != bddfalse
	while(nonPrinted_trans != bddfalsepp) {
		trans_curr_bdd = bdd_fullsatone(nonPrinted_trans);
		State	from(trans_curr_bdd, true),
				to(trans_curr_bdd, false);

		if (printedNames.count(from.getName()) == 0) {
			color = from.ifInitial() ? "red" : "black";
			out<<from.getName() << " [label=<" << from.getTitle() << ">, color = " << color << "];"<<std::endl;
			printedNames.insert(from.getName());
			if (from.ifInitial())
				out<<"init -> " + from.getName() + " [color = red];"<<std::endl;
		}
		if (printedNames.count(to.getName()) == 0) {
			color = to.ifInitial() ? "red" : "black";
			out<<to.getName()<<" [label=<"<< to.getTitle() + ">, color = " << color << "];"<<std::endl;
			printedNames.insert(to.getName());
			if (to.ifInitial())
				out<<"init -> " + to.getName() + " [color = red];"<<std::endl;
		}
		out<<"\""<<from.getName()<<"\" -> \""<<to.getName()<<"\";"<<std::endl;

		nonPrinted_trans &= !trans_curr_bdd;
	}
	out<<"}"<<std::endl;
	
	return 1;
}// end printDot

int main(void)
{
	FileText file("arbiter2.smv");

	file.removeExtraData();//remove all comments
	//проверить: если создаем элемент класса, кладем его в массив, потом забираем обратно в новую переменную и меняем эту переменную - изменится ли значение того?
	file.getSMVModules();
	//setArbiter2Data();
	cox_cnt = 0; gfpz_cnt = 0; lfp_cnt = 0; gfpx_cnt = 0; time1 = 0; time1_1 = 0; time2 = 0; time2_2 = 0; time3 = 0; time4 = 0;//[TA] delete!!!
	/*
	prevTime = clock();
	long t1 = clock();
	universal_Arbiter_setData(2);
	
	out_strat.open("outStrategy.txt");
	
	//[TA] check bdd_printdot!!!!
	std::cout << "Time0 : " << clock() - t1 << std::endl;
	out_strat << "p_e:  " << p_e << std::endl;
	out_strat << "p_s:  " << p_s << std::endl;
	out_strat << "init:  " << init << std::endl;
	out_strat << "J1[0]:  " << J1[0] << std::endl;
	out_strat << "J2[0]:  " << J2[0] << std::endl;
 	bdd temp = winm();
	/*std::cout << "time1_var : " << time1 << std::endl;
	std::cout << "time11_var : " << time1_1 << std::endl;
	std::cout << "time2_var : " << time2 << std::endl;
	std::cout << "time2_2_var : " << time2_2 << std::endl;
	std::cout << "time3_var : " << time3 << std::endl;
	std::cout << "time4_var : " << time4 << std::endl;
	std::cout << "cox_cnt: " << cox_cnt << std::endl;
	std::cout << "gfpz_cnt: " << gfpz_cnt << std::endl;
	std::cout << "lfp_cnt: " << lfp_cnt << std::endl;
	std::cout << "gfpx_cnt: " << gfpx_cnt << std::endl;
	std::cout << "Time1 : " << clock() - t1 << std::endl;
	out_strat.close();//[TA] temp!
	/*
	trans = toSymbStrategy(temp);
	std::cout << "Time2 : " << clock() - t1 << std::endl;
	minimize();
	std::cout << "Time3 : " << clock() - t1 << std::endl;
	
	std::ofstream out;
	out.open("outGraph.dot");
	printDot(out, trans);
	out.close();
	deleteStutteringTransitions(trans);

	*/
	system("pause");
	return 0;
}


	/*
	std::ofstream out;
	out.open("sizes.txt");
	out << "Time : " << clock() - t1 << std::endl;
	out << "SAT count : " << bdd_satcount(trans) << std::endl;
	out << "Node count: " << bdd_nodecount(trans) << std::endl;
	out << "Controller nodes count: " << bdd_satcount(forsome_next_V(allReachableTrans(trans)) & bdd_ithfun(0, env1_pr, envCnt) & bdd_ithfun(0, sys1_pr, sysCnt) & tojx[0]) << std::endl;
	out.close();*/
