//check for [TA]
//check for !!!
//delete coxCnt
// Piterman.cpp : controller synthesis as in Piterman2006 article
#pragma comment(lib, "bdd.lib")	// BuDDy library
//#include "stdafx.h"
#include <vector>
#include "bdd.h"

#include <string>
#include <set>
#include <map>
#include <fstream>
#include <ostream>
#include <sstream>
#include <time.h>

bdd trans,//sythesised FDS
	init,//initial values
	obseq;//describes transitions where only jx strategy changes

std::ofstream out_strat;//[TA] temp!

std::vector<bdd>	J1,//vector of left-hand side (of the implication) boolean formulas. J1.size == m
					J2;//vector of right-hand side (of the implication) boolean formulas. J2.size == n

//we code variables from X as {env1..env1+envCnt-1}: bdd_ithvarpp(env1), ..., bdd_ithvarpp(env1+envCnt-1) - these are environment variables
//we code variables from Y as {sys1..sys1+sysCnt-1}: bdd_ithvarpp(sys1), ..., bdd_ithvarpp(sys1+sysCnt-1) - these are system variables

std::vector<std::string> varNames;

class Variable {
private:
	std::string name;
	std::map<std::string, bdd> valuesBDD;
	std::map<std::string, bdd> nextValuesBDD;
	unsigned varBDDCnt;// count of BDD variables used to encode this Variable
	int id0;

	unsigned log2(int k) {
		unsigned log = 0;
		while (k >>= 1) log++;
		return log;
	}// end log2

	bdd bdd_ithfun(int f_num, int fromVar, unsigned varCnt) {
		//if fromVar == jx1:	jx1 , jx2 , jx3 , ...
		//if fromVar == jx1_:	jx1', jx2', jx3', ...
		bdd fun = bddtruepp;
		for (unsigned i = 0; i < varCnt; i++)
			fun &= ((f_num >> i) & 1) ? bdd_ithvarpp(i + fromVar) : bdd_nithvarpp(i + fromVar);
		return fun;
	}// end bdd_ithfun

public:
	//constructors:
	Variable() {}

	Variable(std::string name_str) {
		name = name_str;
		id0 = bdd_varnum();
		varBDDCnt = 1;
		bdd_extvarnum(2); // because we use second var to encode next(var)
		valuesBDD["TRUE"] = bdd_ithvar(id0);
		valuesBDD["FALSE"] = bdd_nithvar(id0);
	}

	Variable(std::string name_str, std::vector<std::string> var_values) {
		name = name_str;
		id0 = bdd_varnum();//[TA] may be we don't need this?
		varBDDCnt = log2(var_values.size());
		bdd_extvarnum(varBDDCnt * 2);// because we use second vars set to encode next(var)

		for (unsigned i = 0; i < varBDDCnt; i++) {
			valuesBDD[var_values[i]] = bdd_ithfun(i, id0, varBDDCnt);
			nextValuesBDD[var_values[i]] = bdd_ithfun(i, id0 + varBDDCnt, varBDDCnt);
		}	
	}
	
	Variable(const Variable& other) {
		name = other.name;
		id0 = other.id0;
		valuesBDD = other.valuesBDD;
		nextValuesBDD = other.nextValuesBDD;
		varBDDCnt = other.varBDDCnt;
	}
	// end constructors
	~Variable() {
		name.clear();
		valuesBDD.clear();
	}

	std::string Name() { return name; }
	
	int Id() { return id0; }

	int* IDs() {//we use array of int because we can also use enumerable variables
		int *res = new int[varBDDCnt];
		for (unsigned i = 0; i < varBDDCnt; i++)
			res[i] = id0 + i;

		return res;
	}
	
	int NextId() { return id0 + 1; }
	
	int* NextIDs() {
		int *res = new int[varBDDCnt];
		for (unsigned i = 0; i < varBDDCnt; i++)
			res[i] = id0 + varBDDCnt + i;

		return res;
	}
	
	bdd varBDD() { return bdd_ithvar(id0); }

	unsigned GetVarBDDCnt() { return varBDDCnt; }

	bdd varValueBDD(std::string value) {
		return (valuesBDD.find(value) == valuesBDD.end()) ? bddfalsepp : valuesBDD[value];
	}
	
	bdd nextBDD() { return bdd_ithvar(NextId()); }

	bdd nextVarValueBDD(std::string value) {
		return (nextValuesBDD.find(value) == nextValuesBDD.end()) ? bddfalsepp : nextValuesBDD[value];
	}
};

class SMVModule {
private:
	std::string moduleName;
	std::vector<Variable> vars;
	std::vector<Variable> externalVars;

	bdd initial;
	bdd transition;
	std::vector<bdd> justice;
public:
	SMVModule() {
		moduleName = "";
		initial = bddtruepp;
		transition = bddtruepp;
	}
	
	SMVModule(std::string name) {
		moduleName = name;
		initial = bddtruepp;
		transition = bddtruepp;
	}
	
	SMVModule(const SMVModule& other) {// copying constructor
		vars = other.vars;
		externalVars = other.externalVars;
		moduleName = other.moduleName;
		initial = other.initial;
		transition = other.transition;
		justice = other.justice;
	}
	// end constructors
	~SMVModule() {
		moduleName.clear();
		vars.clear();
		externalVars.clear();
		justice.clear();
    }

	std::string GetName() { return moduleName; }

	void SetName(std::string name) { moduleName = name; }
	
	bdd GetInitial() { return initial; }

	void SetInitial(bdd ini) { initial = ini; }
	
	void AddInitial(bdd ini) { initial = initial & ini; }

	void AddInitial(std::string varName, std::string val_ini) {
		Variable v(GetVariable(varName));
		initial = initial & v.varValueBDD(val_ini);
	}
	
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
		return NULL;//[TA] or may be return new Variable(varName)?
	}

	std::vector<Variable> GetInternalVariables() { return vars; }

	std::vector<Variable> GetAllVariables() {
		std::vector<Variable> res;
		res.insert(res.end(), vars.begin(), vars.end());
		res.insert(res.end(), externalVars.begin(), externalVars.end());
		return res;
	}

	std::vector<int> GetVariablesIds() {
		std::vector<int> res;
		for (unsigned i = 0; i < vars.size(); i++)
			for (unsigned j = 0; j < vars[i].GetVarBDDCnt(); j++)
				res.push_back(vars[i].IDs()[j]);

		return res;
	}// change to static definition!!!

	std::vector<int> GetVariablesNextIds() {
		std::vector<int> res;
		for (unsigned i = 0; i < vars.size(); i++)
			for (unsigned j = 0; j < vars[i].GetVarBDDCnt(); j++)
				res.push_back(vars[i].NextIDs()[j]);

		return res;
	}// change to static definition!!!

	std::vector<int> AllVariablesIds() { //[TA] may be don't need this
		std::vector<int> res;

		for (unsigned i = 0; i < vars.size(); i++) {
			res.push_back(vars[i].Id());
		}
		for (unsigned i = 0; i < externalVars.size(); i++) {
			res.push_back(externalVars[i].Id());
		}
		return res;
	}// change to static definition!!!

	std::vector<int> AllVariablesNextIds() { //[TA] may be don't need this
		std::vector<int> res;

		for (unsigned i = 0; i < vars.size(); i++) {
			res.push_back(vars[i].NextId());
		}
		for (unsigned i = 0; i < externalVars.size(); i++) {
			res.push_back(externalVars[i].NextId());
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

	bdd GetTransition() { return transition; }

	void AddJustice(bdd justice_new) {
		justice.push_back(justice_new);
	}

	std::vector<bdd> GetJustice() { return justice; }
};//end class SMVModule

class FileText {
private:
	std::vector<std::string> text;
	std::vector<std::string> tokenText;
	std::vector<std::string> delims;
	std::vector<SMVModule> allModules;

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

	bdd next(bdd func) {
		static bddPair *sysEnv_primePair = bdd_newpair();
		
		static bool b = true;

		if (b) { //[TA] change this condition!!!
			b = false;
			for (unsigned i = 0; i < allModules.size(); i++) {
				std::vector<Variable> vars_ithSet = allModules[i].GetInternalVariables();

				for (unsigned i = 0; i < vars_ithSet.size(); i++) {
					bdd_setpair(sysEnv_primePair, vars_ithSet[i].Id(), vars_ithSet[i].NextId());
				}
			}
		}

		return bdd_replace(func, sysEnv_primePair);
	}// end next

	SMVModule* FindModule(std::string moduleName) {
		for (unsigned i = 0; i < allModules.size(); i++)
			if (allModules[i].GetName() == moduleName) return &allModules[i];
		//else
		return NULL;//throw Exception
	}

	bdd getBDD(unsigned &i, std::string stop_sym, SMVModule* module) {
		bdd res = bddtrue;
		int prev_operator = bddop_and;
		// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! �������� ���������� ����������!
		// !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! �������� ����������� �������, ����� �� ��������� map ������ ���
		std::map<std::string, int> operatorsMap;
			operatorsMap[")"] = -1;
			operatorsMap[";"] = -1;
			operatorsMap["&"] = bddop_and;
			operatorsMap["|"] = bddop_or;
			operatorsMap["->"] = bddop_imp;
			operatorsMap["="] = bddop_biimp;

		std::map<std::string, int> statesMap;
			statesMap["("] = 1;
			statesMap[")"] = 2;
			statesMap["!"] = 3;
			statesMap["next"] = 4;
			statesMap[";"] = 5;

		while(tokenText[i] != stop_sym) {//or until other special word
			switch(statesMap[tokenText[i]]) {
				case 1: {
					bdd temp = getBDD(++i, ")", module);

					res = bdd_apply(res, temp, prev_operator);
					break;
				}
				case 2: {
					i++;
					break;//throw exception: we can not reach this case
				}
				case 3: {
					if (tokenText[++i] == "(") {
						bdd temp = getBDD(++i, ")", module);
						res = bdd_apply(res, bdd_not(temp), prev_operator);
					} else {
						res = bdd_apply(res, bdd_not(module->GetVariable(tokenText[i]).varBDD()), prev_operator);
					}
					break;
				}
				case 4: {
					if (tokenText[++i] != "(") { break; }// throw Exception!!!
					//bdd temp = getBDD(++i, ")", module); [TA] we can try to use grammar: next(expr) instead of next(var). But I will ignore it for first time
					std::string varName = tokenText[++i];

					Variable var = module->GetVariable(varName);
					if (tokenText[++i] != ")") break; // throw Exception! NO!!! here can be "= value" code.
					res = bdd_apply(res, var.nextBDD(), prev_operator);
					break;
				}
				case 5: break;//throw Exception
				default: {//variable name by default
					if (module->check_ifVariableExist(tokenText[i])) {
						res = bdd_apply(res, module->GetVariable(tokenText[i]).varBDD(), prev_operator);
					} else {
						//throw Exception!!!
					}
				}
			}
			i++;
			if (operatorsMap[tokenText[i]] == -1) {//can be also ")" or ";"
				continue;
			} else if (operatorsMap[tokenText[i]] >= 0) {
				if (tokenText[i] == "!") {
					if (tokenText[++i] == "=")
						prev_operator = bddop_xor;
				} else {
					prev_operator = operatorsMap[tokenText[i]];
				}
				i++;
			} else break;// !!! throw Exception!
		}
		return res;
		// (!(r1 = g1) | (g1 = next(g1))) & (!(r2 = g2) | (g2 = next(g2))) & !(next(g1) & next(g2)) & ((t1 = 1) -> next(t1 = 1));
		//p_e = (bdd_xor(r1, g1) >> bdd_biimp(r1, r1_)) & (bdd_xor(r2, g2) >> bdd_biimp(r2, r2_));
		//p_s = !( g1_ & g2_) & (bdd_biimp(r1, g1) >> bdd_biimp(g1, g1_)) & (bdd_biimp(r2, g2) >> bdd_biimp(g2, g2_));
	}// end getBDD

public:
	FileText(std::string fileName) {
		std::ifstream file(fileName);

		if (!file.is_open())
			std::cout << "File can not be opened!\n";//!!! throw Exception
		else {
			//getline(istream & is, string &s,char c='\n'),������ �� ������ is, � ������ s ���� �� �������� ������ c (��� ����� ������� �� ����� ������)
			// ���������� ���� ������ istream, � ������� ����������� ��������� iostate ����a, �������� ����� ����� ����� ������, ���� ��������� ����� �����, ��� ����� ������ ����� ��� ��������� ����
			std::string tmp;
			while (getline(file,tmp))
				text.push_back(tmp + "\n");
		}
		file.close();

		delims.push_back(" "); delims.push_back("\t"); delims.push_back("\n"); delims.push_back("("); delims.push_back(".");
		delims.push_back(")"); delims.push_back("{"); delims.push_back("}"); delims.push_back("//"); delims.push_back("!");
		delims.push_back("/*"); delims.push_back("*/"); delims.push_back(","); delims.push_back(";"); delims.push_back(":=");
		//delims.push_back("=");

		tokenize();
	}
	
    FileText(const FileText& other) {// ����������� �����������
		allModules = other.allModules;
		delims = other.delims;
		text = other.text;
		tokenText = other.tokenText;
    }
	
	/*~FileText() {
		text.clear();
		tokenText.clear();
		delims.clear();
		allModules.clear();
    }*/
	
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
		for (unsigned i = 0; (i < tokenText.size()) && !mainModuleExist; i++) {
			if (tokenText[i] == "MODULE") {
				if (tokenText[++i] != "main") { continue; }
				mainModuleExist = true;
				if (tokenText[++i] != "VAR") mainModuleExist = false;//throw Exception!!!

				std::map<std::string, int> modulePositions;//added to map temporary variable name to its position in allModules vector

				for (int j = i; tokenText[j] != "MODULE"; j++) {//read all modules names
					if (tokenText[j] == "VAR") j++;

					std::string module_temporary_name = tokenText[j];
					if (tokenText[++j] != ":") mainModuleExist = false;//throw Exception!!!
					std::string module_primary_name = tokenText[++j];

					// ?? may be add the test if moduleName is good?
					allModules.push_back(SMVModule(module_primary_name));
					modulePositions[module_temporary_name] = allModules.size() - 1;
					
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
							otherModule = &allModules[modulePositions[otherModuleName]];
							if (tokenText[++j] != ".") mainModuleExist = false;// throw Exception!!!

							std::string varName = tokenText[++j];
							if (!otherModule->AddVariable(varName)) mainModuleExist = false;// throw Exception!!!

							FindModule(module_primary_name)->AddExternalVariable(otherModule->GetVariable(varName));
							if (tokenText[++j] == ",") continue;
						}
					}
					if (tokenText[++j] != ";") {break;} // throw Exception!!!
				}
			}
		}
		if (!mainModuleExist) return;//throw Exception!!!
	}

	void readSMVModules() {
		bdd_init(10000000,1000000);//[TA] what to set here?
		bdd_setcacheratio(10);
		bdd_enable_reorder();

		readMainSMVModule();// ����� ��������, ����� ����� ������, ��������� ������ ������-�������� ������, ����������� ����������.

		//======================
		// Main parser!
		//======================
		// 1st part: here we create all MODULE's variables (for all modules)
		SMVModule *module = NULL;
		for (unsigned i = 0; i < tokenText.size(); i++) {
			if (tokenText[i] == "MODULE") {
				if (tokenText[++i] == "main") continue;
				for (unsigned j = 0; j < allModules.size(); j++) {
					if (allModules[j].GetName() == tokenText[i]) {
						module = &allModules[j];
					}
				}
				if (module == NULL) {
				}// check if no module was found !!!

				if (tokenText[++i] == "(") {
					while(tokenText[++i] != ")") {}//later check if all external variables were defined earlier !!!
				}
				while (tokenText[++i] != "VAR") {
					if (i > tokenText.size()) break;
				}

				if (tokenText[i] == "VAR") {
					std::string next = tokenText[++i];
					while ((next != "TRANS") && (next != "MODULE") && (next != "JUSTICE") && (next != "ASSIGN")) {
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

		// 2nd part: here we get initial values, transitions and Justice requirements
		for (unsigned m = 0; m < allModules.size(); m++) {
			int state = 0;
			std::string part;
			std::map<std::string, int> statesMap;
			// check if we read "MODULE" token while reading our module, this means our module description is ended
				statesMap["MODULE"] = 1;
				statesMap["VAR"] = 2;
				statesMap["ASSIGN"] = 3;
				statesMap["TRANS"] = 4;
				statesMap["JUSTICE"] = 5;

			for (unsigned i = 0; i < tokenText.size(); i++) {
				if (tokenText[i] == "MODULE") {
					if (state > 0) break;
					state = 1;
					i++;
				}
				if ((state > 0) && (statesMap.find(tokenText[i]) != statesMap.end()))
					state = statesMap[tokenText[i++]];

				if (state < 0) break; //delete later: we will throw Exceptions in other place

				switch(state) {
					//0: try to find "MODULE" text
					//1: read module with requested name, and it's arguments
					//2: read MODULE variables
					//3: read MODULE initial values
					//4: read MODULE transition rules
					//5: read MODULE justice requirements
					case 0: break;
					case 1: { // read MODULE with requested name
						if (tokenText[i++] != allModules[m].GetName()) { state = 0; break; }//throw Exception!!!
						if (tokenText[i] == "(") {
							// read MODULE agruments
							//!!! temp:
							while(tokenText[++i] != ")") { }
						}

						if (statesMap.find(tokenText[i + 1]) == statesMap.end()) state = -1;//throw Exception!!!
						break;
					}
					case 2: { 
						// all MODULE external variables were read earlier, so we skip this case
						state = 2;
						break;
					}
					case 3: { // read MODULE initial values
						if (tokenText[i] != "init") { state = -1; break; } // throw exception!!!
						if (tokenText[++i] != "(") { state = -1; break; } // throw exception!!!
						std::string varName = tokenText[++i];
						if (tokenText[++i] != ")") { state = -1; break; } // throw exception!!!
						if (tokenText[++i] != ":=") { state = -1; break; } // throw exception!!!
						std::string val_ini = tokenText[++i];

						allModules[m].AddInitial(varName, val_ini);

						if (tokenText[++i] != ";") { state = -1; break; } // throw exception!!! check, may be we don't need it sometimes
						break;
					}
					case 4: { // read MODULE transition rules
						bdd temp = getBDD(i, ";", &allModules[m]);
						allModules[m].SetTransition(temp);
						break;
					}
					case 5: { // read MODULE justice requirements
						bdd temp = getBDD(i, ";", &allModules[m]);
						allModules[m].AddJustice(temp);
						break;
					}
					default: {std::cout<<"ERROR!!!!!!!!!!!!!!!!!!!!!!!!!!!\n";}//throw exception
				}// end switch
			}
		}
	}

	SMVModule GetModule(std::string moduleName) {
		for (unsigned i = 0; i < allModules.size(); i++)
			if (allModules[i].GetName() == moduleName) return allModules[i];
		//else
		return SMVModule(moduleName);
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
	Variable jx;
	int coxCnt;
	std::vector<std::vector<std::vector<bdd>>> x_strat;//strategies for the system: leads the computation to J1-states
	std::vector<std::vector<bdd>> y_strat;//strategy for the system: leads the computation to get closer to J2-states

	std::vector<bdd> fromjx, tojx;//may be use it not as private variable?!!!

	unsigned log2(int k) {
		unsigned log = 0;
		while (k >>= 1) log++;
		return log;
	}// end log2

	bdd Next(bdd vars) {
		static bddPair *sysEnv_Pairs = bdd_newpair();
		static bool b = true;

		if (b) { //[TA] change this condition!!!
			b = false;

			std::vector<Variable> sys_vars = sys.GetInternalVariables();
			std::vector<Variable> env_vars = env.GetInternalVariables();

			for (unsigned i = 0; i < sys_vars.size(); i++)
				bdd_setpairs(sysEnv_Pairs, sys_vars[i].IDs(), sys_vars[i].NextIDs(), 1);//!!! ������� �� 1, � ���������� � ����� ������
			for (unsigned i = 0; i < env_vars.size(); i++)
				bdd_setpairs(sysEnv_Pairs, env_vars[i].IDs(), env_vars[i].NextIDs(), 1);//!!! ������� �� 1, � ���������� � ����� ������
		}

		return bdd_replace(vars, sysEnv_Pairs);
	}// end Next

	bdd NextAll(bdd vars) {
		static bddPair *allVars_Pairs = bdd_newpair();

		static bool b = true;
		if (b) { //[TA] change this condition!!!
			b = false;

			std::vector<Variable> sys_vars = sys.GetInternalVariables();
			std::vector<Variable> env_vars = env.GetInternalVariables();

			for (unsigned i = 0; i < sys_vars.size(); i++)
				bdd_setpairs(allVars_Pairs, sys_vars[i].IDs(), sys_vars[i].NextIDs(), 1);//!!! ������� �� 1, � ���������� � ����� ������
			for (unsigned i = 0; i < env_vars.size(); i++)
				bdd_setpairs(allVars_Pairs, env_vars[i].IDs(), env_vars[i].NextIDs(), 1);//!!! ������� �� 1, � ���������� � ����� ������
			for (unsigned i = 0; i < jx.GetVarBDDCnt(); i++)
				bdd_setpair(allVars_Pairs, jx.IDs()[i], jx.NextIDs()[i]);
		}
		return bdd_replace(vars, allVars_Pairs);
	}// end NextAll

	/*bdd unPrimeAllVariables(bdd vars) {
		bddPair *pairs = bdd_newpair();
		for (unsigned i = 0; i < sysCnt; i++)
			bdd_setpair(pairs, sys1_pr + i, sys1 + i);
		for (unsigned i = 0; i < envCnt; i++)
			bdd_setpair(pairs, env1_pr + i, env1 + i);
		for (unsigned i = 0; i < jxCnt; i++)
			bdd_setpair(pairs, jx1_pr + i, jx1 + i);
	
		return bdd_replace(vars, pairs);
	}// end unPrimeAllVariables*/

	//[TA] check one more time!!!
	bdd step(bdd phi) { // function is named cox in the article
		coxCnt++;
		std::vector<Variable> sys_vars = sys.GetInternalVariables();

		static bdd sys_next_bdd = bddtruepp;//[TA] check: may be bddfalsepp
		if (sys_next_bdd == bddtruepp) {//[TA] this condition is to initialise sys_pr_arr_bdd only once
			int sys_allVarBDDcnt = 0;
			for (unsigned i = 0; i < sys_vars.size(); i++) {
				sys_allVarBDDcnt += sys_vars[i].GetVarBDDCnt();
			}
			int* sys_next_arr = new int[sys_allVarBDDcnt];
			
			for (unsigned i = 0; i < sys_vars.size(); i++) {
				int* nextIDs_i = sys_vars[i].NextIDs();
				for (unsigned j = 0; j < sys_vars[i].GetVarBDDCnt(); j++) {
					sys_next_arr[i] = nextIDs_i[j];
				}
			}

			sys_next_bdd = bdd_makeset(sys_next_arr, sys_vars.size());
//			delete[] sys_next_arr;
		}
		//p_e => \exist y' such that (p_s and phi(x',y'))

		bdd res = bdd_imp(env.GetTransition(), bdd_exist(sys.GetTransition() & Next(phi), sys_next_bdd));

		//\foreach x'
		std::vector<int> env_next_IDs = env.GetVariablesNextIds();
		for (unsigned i = 0; i < env_next_IDs.size(); i++)
			res = bdd_forall(res, bdd_ithvarpp(env_next_IDs[i]));
	
		return res;
	}// end step(cox)

	bdd greatestFixPoint(bdd & z, bdd & start, int i) {
		bdd x = z,
			x_old;
		do {
			x_old = x;
			x = !env.GetJustice()[i] & step(x) | start;
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
			x_strat[j][r].resize(env.GetJustice().size());

			y_old = y;

			start = sys.GetJustice()[j] & step(z) | step(y);
			y = bddfalsepp;
			for (unsigned i = 0; i < env.GetJustice().size(); i++) {
				x = greatestFixPoint(z, start, i);

				x_strat[j][r][i] = x;
				y |= x;
			}
			y_strat[j][r++] = y;
		} while (y_old != y);
		return y;
	}// end leastFixPoint

	//[TA] may be we don't need this later..
	bdd bdd_ithfun(int f_num, int fromVar, unsigned varCnt) {
		//if fromVar == jx1:	jx1 , jx2 , jx3 , ...
		//if fromVar == jx1_:	jx1', jx2', jx3', ...
		bdd fun = bddtruepp;
		for (unsigned i = 0; i < varCnt; i++)
			fun &= ((f_num >> i) & 1) ? bdd_ithvarpp(i + fromVar) : bdd_nithvarpp(i + fromVar);
		return fun;
	}// end bdd_ithfun

	void reduce(bdd &trans, int j, int k) {
		bdd obseq = bddtrue;
		//describes transitions where only jx strategy changes:
		for (unsigned i = 0; i < sys.GetJustice().size(); i++)
			obseq &= ! (fromjx[i] & tojx[i]);
		//and other variables doesn't change
		std::vector<Variable> env_vars = env.GetInternalVariables();
		std::vector<Variable> sys_vars = sys.GetInternalVariables();

		for (unsigned i = 0; i < env_vars.size(); i++)
			obseq &= bdd_biimp(env_vars[i].varBDD(), env_vars[i].nextBDD());//[TA] this will not work with enumerable variables!!!
		for (unsigned i = 0; i < sys_vars.size(); i++)
			obseq &= bdd_biimp(sys_vars[i].varBDD(), sys_vars[i].nextBDD());//[TA] this will not work with enumerable variables!!!

		bdd states = forsome_next_V(trans & obseq & fromjx[j] & tojx[k]);
		bdd add_trans = forsome_next_jx(trans & NextAll(states)) & tojx[k];
		bdd add_init = forsome_next_jx(init & states) & fromjx[k];
		trans = (trans & !(NextAll(states) | states)) | add_trans;
		init = (init & !(states & fromjx[j])) | add_init;
	}// end reduce
public:
	GRGame() {}

	GRGame(SMVModule environment, SMVModule system) {
		env = SMVModule(environment);
		sys = SMVModule(system);
		y_strat.resize(sys.GetJustice().size());
		x_strat.resize(sys.GetJustice().size());
		coxCnt = 0;
	}
	
	~GRGame() {
		x_strat.clear();
		y_strat.clear();
	}
	
	bdd WinningRegion() {
		bdd z = bddtruepp,
			z_old;

		do {//GratestFixPoint(z)
			z_old = z;
			for (unsigned j = 0; j < sys.GetJustice().size(); j++)
				z = leastFixPoint(z, j);
		} while(z != z_old);
		std::cout<<"\n"<<coxCnt<<"\n";
		return z;
	}// end WinningRegion

	bdd getConroller(bdd z) {
		std::vector<bdd> fromjx, tojx;
		bdd trans = bddfalse;

		unsigned sysJ_cnt = sys.GetJustice().size();
		unsigned jx1 = bdd_varnum();//jx1 position
		//����� ��������� ���������� ���������� jx � ������������� � ���������, ���������� �� �����.

		std::vector<std::string> from0toN;
		for (unsigned i = 0; i < sysJ_cnt; i++)
			from0toN.push_back(""+i);
		jx = Variable(" jx", from0toN);//I give such name (" jx") because it can not be assigned for the other variables (parser doesn't allow to create the names like this).

		for (unsigned i = 0; i < sysJ_cnt; i++) {
			fromjx[i] = jx.varValueBDD(from0toN[i]);
			tojx[i] = jx.nextVarValueBDD(from0toN[i]);
		}

		unsigned envJ_cnt = env.GetJustice().size();

		for (unsigned j = 0; j < envJ_cnt; j++) {
			trans |= fromjx[j] & tojx[(j + 1) % sysJ_cnt] & z & sys.GetJustice()[j] & env.GetTransition() & sys.GetTransition() & Next(z);
		}
		for (unsigned j = 0; j < sysJ_cnt; j++) {
			bdd low = y_strat[j][0];
			for (unsigned r = 1; r < y_strat[j].size(); r++) {//maxr[j] == y_strat[j].size()
				trans |= fromjx[j] & tojx[j] & y_strat[j][r] & !low & env.GetTransition() & sys.GetTransition() & Next(low);
				low |= y_strat[j][r];
			}
		}
		for (unsigned j = 0; j < sysJ_cnt; j++) {
			bdd low = bddfalse;
			for (unsigned r = 0; r < y_strat[j].size(); r++) {//maxr[j] == y_strat[j].size()
				for (unsigned i = 0; i < envJ_cnt; i++) {
					trans |= fromjx[j] & tojx[j] & x_strat[j][r][i] & !low & !env.GetJustice()[i] & env.GetTransition() & sys.GetTransition() & Next(x_strat[j][r][i]);
					low |= x_strat[j][r][i];
				}
			}
		}
		return trans;
	}// end getConroller

	void Minimize(bdd &trans) {
		//n == jxCnt
		std::ofstream out;
		for (unsigned j = 0; j < sys.GetJustice().size(); j++)
			reduce(trans, j, (j + 1) % sys.GetJustice().size());
		for (unsigned j = 0; j < sys.GetJustice().size() - 1; j++)
			reduce(trans, sys.GetJustice().size() - 1, j);
	}

	bdd forsome_V(bdd fun) {
		std::vector<int> sys_vars_ids = sys.GetVariablesIds();
		std::vector<int> env_vars_ids = env.GetVariablesIds();

		int *env_sys_jx_arr = new int[sys_vars_ids.size() + env_vars_ids.size() + jx.GetVarBDDCnt()];

		for (unsigned i = 0; i < sys_vars_ids.size(); i++)
			 env_sys_jx_arr[i] = sys_vars_ids[i];
		for (unsigned i = 0; i < env_vars_ids.size(); i++)
			env_sys_jx_arr[sys_vars_ids.size() + i] = env_vars_ids[i];
		for (unsigned i = 0; i < jx.GetVarBDDCnt(); i++) {
			env_sys_jx_arr[sys_vars_ids.size() + env_vars_ids.size() + i] = jx.IDs()[i];
		}

		//exist v from V: env, sys or jx
		bdd v_BDDset = bdd_makeset(env_sys_jx_arr, sys_vars_ids.size() + env_vars_ids.size() + jx.GetVarBDDCnt());
		return bdd_exist(fun, v_BDDset);
	}// end forsome_V

	bdd forsome_next_V(bdd fun) {
		std::vector<int> sys_vars_ids = sys.GetVariablesNextIds();
		std::vector<int> env_vars_ids = env.GetVariablesNextIds();

		int *primed_env_sys_jx_arr = new int[sys_vars_ids.size() + env_vars_ids.size() + jx.GetVarBDDCnt()];

		for (unsigned i = 0; i < sys_vars_ids.size(); i++)
			 primed_env_sys_jx_arr[i] = sys_vars_ids[i];
		for (unsigned i = 0; i < env_vars_ids.size(); i++)
			primed_env_sys_jx_arr[sys_vars_ids.size() + i] = env_vars_ids[i];
		for (unsigned i = 0; i < jx.GetVarBDDCnt(); i++) {
			primed_env_sys_jx_arr[sys_vars_ids.size() + env_vars_ids.size() + i] = jx.NextIDs()[i];
		}

		//exist v' from V: env_pr, sys_pr or jx_pr
		bdd nextV_BDDset = bdd_makeset(primed_env_sys_jx_arr, sys_vars_ids.size() + env_vars_ids.size() + jx.GetVarBDDCnt());
		return bdd_exist(fun, nextV_BDDset);
	}// end forsome_next_V

	bdd forsome_next_jx(bdd fun) {
		//exist some primed jx
		bdd nextJx_BDDset = bdd_makeset(jx.NextIDs(), jx.GetVarBDDCnt());
		return bdd_exist(fun, nextJx_BDDset);
	}// end forsome_next_jx

};// end class GRGame

class State {
private:
	bdd bddState;
	std::string name,	//unique and compact name for each state, e.g. s01101
				title;	//[TA]!!!!!
	GRGame game;
	unsigned env1, envCnt, sys1, sysCnt, jx1, jxCnt;
	
	bool initial;

	void setName() {
		unsigned varCnt = bdd_varnum();
		name = "s";
		for (unsigned i = 0; i < varCnt; i++)
			name += ((bddState & bdd_ithvarpp(i)) != bddfalsepp) ? "1" : "0";
	}
	void setTitle() {
		title = "";
		
		for (unsigned i = env1; i < env1 + envCnt; i++)
			title += "<O>" + varNames[i] + "</O>" + ",";
		for (unsigned i = sys1; i < sys1 + sysCnt; i++)
			title += "<O>" + varNames[i] + "</O>" + ",";
		
		title += " ";
		title += ithJxTitle();
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

	State(bdd allVarsBDD, GRGame gr_game, bool ifFrom) {
		game = GRGame(gr_game);
		bddState = allVarsBDD;
		if (ifFrom) {//we receive transition BDD, if we should take from-state, we delete all primed variables
			bddState = game.forsome_next_V(bddState);
			//bddState = bdd_exist(bddState, bdd_makeset(primed_env_sys_jx_arr, envCnt + sysCnt + jxCnt));
		} else {//we receive transition BDD, if we should take to-state, we delete all unprimed variables (from-states)
				//and unprime other (primed) variables - we convert to-states into from-states
			bddState = game.forsome_V(bddState);
				//bdd_exist(bddState, bdd_makeset(env_sys_jx_arr, envCnt + sysCnt + jxCnt));
			
			bddPair *pairs = bdd_newpair();
			// !!!!!!!!!! unprime all variables!!!!!!!!! ���� �� next ������� ������ ����������, ������ ��� jx - ����
			bddState = bdd_replace(bddState, pairs);
		}
		
		setName();
		setTitle();
		initial = ((init & bddState) != bddfalsepp) ? true : false;
    }
	
	~State() {
		name.clear();
		title.clear();
	}
	std::string getName() { return name; }

	std::string getTitle() { return title; }

	bool ifInitial() { return initial; }
};//end class State

int main(void)
{
	long t0 = clock();
	FileText file("arbiter9.smv");

	file.removeExtraData();//remove all comments
	int test = bdd_varnum();
	file.readSMVModules();
	test = bdd_varnum();
	SMVModule sys(file.GetModule("sys"));
	SMVModule env(file.GetModule("env"));
	test = bdd_varnum();
	long t1 = clock();
	GRGame arbiter2(env, sys);
	test = bdd_varnum();
	out_strat.open("new_winreg.txt");
	bdd temp = arbiter2.WinningRegion();
	test = bdd_varnum();
	//bdd temp2 = arbiter2.getConroller(temp);
	//arbiter2.Minimize(temp2);
	
	out_strat<<temp<<std::endl;
	out_strat.close();

	std::cout << "Time0 : " << t1 - t0 << std::endl;
	std::cout << "WinReg : " << clock() - t1 << std::endl;
	/*
	prevTime = clock();
	long t1 = clock();
	
	out_strat.open("outStrategy.txt");
	
	//[TA] check bdd_printdot!!!!
	std::cout << "Time0 : " << clock() - t1 << std::endl;
	out_strat << "p_e:  " << p_e << std::endl;
	out_strat << "p_s:  " << p_s << std::endl;
	out_strat << "init:  " << init << std::endl;
	out_strat << "J1[0]:  " << J1[0] << std::endl;
	out_strat << "J2[0]:  " << J2[0] << std::endl;
 	bdd temp = winm();
	std::cout << "time1_var : " << time1 << std::endl;
	out_strat.close();//[TA] temp!
	
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







//================================================================
//				OLD FUNCTIONS, PUT THEM TO GRGame class
//================================================================
/*
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

int printDot(std::ostream &out, bdd & bddtrans) {
	bdd nonPrinted_trans = allReachableTrans(bddtrans);
	bdd trans_curr_bdd;
	
	out<<"digraph G {"<<std::endl;
	std::set<std::string> printedNames;
	std::string color;
	
	out<<"init [shape = point, color = red];"<<std::endl;//[TA] ���������, ������ ����� ����� init & trans != bddfalse
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
*/


	/*
			bdd r1 = env.GetVariable("r1").varBDD();
		bdd r1_ = env.GetVariable("r1").next();
		bdd r2 = env.GetVariable("r2").varBDD();
		bdd r2_ = env.GetVariable("r2").next();
		bdd g1 = env.GetVariable("g1").varBDD();
		bdd g2 = env.GetVariable("g2").varBDD();
*/