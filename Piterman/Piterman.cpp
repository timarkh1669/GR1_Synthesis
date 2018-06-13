/*
Piterman.cpp : controller synthesis for GR(1) requirements

Was developed while master's work.

Distributed Computing and Network department,
	Institute of Computer Science and Technology,
		Peter the Great St.Petersburg Polytechnic University, 
			Saint-Petersburg, Russia.

Timofey Arkhipov,
tim_arkh@mail.ru
Last modified: June 2018
*/

//check for [TA]
//check for !!!
//change "static"
//check if extra ")"

#pragma comment(lib, "Debug/bdd.lib")	// BuDDy library
#include "bdd.h"

#include <vector>
#include <string>
#include <set>
#include <map>
#include <fstream>
#include <ostream>
#include <sstream>
#include <time.h>

int cox_cnt;
struct State {
	std::string name;
	std::string title;
	bool initial;
};

class Variable {
private:
	std::string name;
	std::map<std::string, bdd> valuesBDD;
	std::map<std::string, bdd> nextValuesBDD;
	unsigned varBDDCnt;// count of BDD variables used to encode this Variable
	int id0;

	unsigned log2(int val) {
		if (val == 0) return UINT_MAX;
		unsigned log = 0;
		while (val > 1) {
			val = val / 2 + val % 2;
			log++;
		}
		return log;
	}// end log2

	bdd bdd_ithfun(int f_num, int fromVar, unsigned varCnt) {
		bdd fun = bddtruepp;
		for (unsigned i = 0; i < varCnt; i++)
			fun &= ((f_num >> (varCnt - i) - 1) & 1) ? bdd_ithvarpp(i + fromVar) : bdd_nithvarpp(i + fromVar);
		return fun;
	}// end bdd_ithfun

public:
	//constructors:
	Variable() {}

	Variable(std::string name_str) {
		name = name_str;
		id0 = -1;
		varBDDCnt = 0;
	}

	Variable(std::string name_str, std::vector<std::string> var_values) {
		name = name_str;
		id0 = bdd_varnum();
		varBDDCnt = log2(var_values.size());
		bdd_extvarnum(varBDDCnt * 2);// because we use second vars set to encode next(var)

		for (unsigned i = 0; i < var_values.size(); i++) {
			valuesBDD[var_values[i]] = bdd_ithfun(i, id0, varBDDCnt);
			nextValuesBDD[var_values[i]] = bdd_ithfun(i, id0 + varBDDCnt, varBDDCnt);
		}	
	}
	
	Variable(std::string name_str, std::vector<int> var_values) {
		name = name_str;
		id0 = bdd_varnum();
		varBDDCnt = log2(var_values.size());
		bdd_extvarnum(varBDDCnt * 2);// because we use second vars set to encode next(var)

		for (unsigned i = 0; i < var_values.size(); i++) {
			valuesBDD[std::to_string(var_values[i])] = bdd_ithfun(i, id0, varBDDCnt);
			nextValuesBDD[std::to_string(var_values[i])] = bdd_ithfun(i, id0 + varBDDCnt, varBDDCnt);
		}
	}

	Variable(const Variable& other) {
		name = other.name;
		id0 = other.id0;
		valuesBDD = other.valuesBDD;
		nextValuesBDD = other.nextValuesBDD;
		varBDDCnt = other.varBDDCnt;
	}

	Variable& operator=(const Variable& other) {
		if (this != &other) {
			name = other.name;
			id0 = other.id0;
			valuesBDD = other.valuesBDD;
			nextValuesBDD = other.nextValuesBDD;
			varBDDCnt = other.varBDDCnt;
        }
        return *this;
    }
	// end constructors
	~Variable() {
		name.clear();
		valuesBDD.clear();
	}

	std::string Name() { return name; }

	bool SetBooleanValues() {
		if (varBDDCnt > 0) return false;//if we have already set values earlier
		id0 = bdd_varnum();
		varBDDCnt = 1;
		bdd_extvarnum(2); // because we use second var to encode next(var)
		valuesBDD["TRUE"] = bdd_ithvar(id0);
		valuesBDD["FALSE"] = bdd_nithvar(id0);
		nextValuesBDD["TRUE"] = bdd_ithvar(id0 + varBDDCnt);
		nextValuesBDD["FALSE"] = bdd_nithvar(id0 + varBDDCnt);
		return true;
	}
	
	bool SetValues(std::vector<std::string> var_values) {
		if (varBDDCnt > 0) return false;//if we have already set values earlier
		id0 = bdd_varnum();
		varBDDCnt = log2(var_values.size());
		bdd_extvarnum(varBDDCnt * 2);// because we use second vars set to encode next(var)

		for (unsigned i = 0; i < var_values.size(); i++) {
			valuesBDD[var_values[i]] = bdd_ithfun(i, id0, varBDDCnt);
			nextValuesBDD[var_values[i]] = bdd_ithfun(i, id0 + varBDDCnt, varBDDCnt);
		}
		return true;
	}

	bool SetValues(std::vector<int> var_values) {
		if (varBDDCnt > 0) return false;//if we have already set values earlier
		id0 = bdd_varnum();
		varBDDCnt = log2(var_values.size());
		bdd_extvarnum(varBDDCnt * 2);// because we use second vars set to encode next(var)

		for (unsigned i = 0; i < var_values.size(); i++) {
			valuesBDD[std::to_string(var_values[i])] = bdd_ithfun(i, id0, varBDDCnt);
			nextValuesBDD[std::to_string(var_values[i])] = bdd_ithfun(i, id0 + varBDDCnt, varBDDCnt);
		}
	}

	int* IDs() {//all BDD variables IDs used to encode this Variable
		int *res = new int[varBDDCnt];
		for (unsigned i = 0; i < varBDDCnt; i++)
			res[i] = id0 + i;

		return res;
	}

	int* NextIDs() {//all BDD variables IDs used to encode Next(Variable) (next <=> primed)
		int *res = new int[varBDDCnt];
		for (unsigned i = 0; i < varBDDCnt; i++)
			res[i] = id0 + varBDDCnt + i;

		return res;
	}

	unsigned GetVarBDDCnt() { return varBDDCnt; }

	bdd varValueBDD(std::string value) {
		return (valuesBDD.find(value) == valuesBDD.end()) ? bddfalsepp : valuesBDD[value];
	}

	bdd varValueBDD(int value) {
		return (valuesBDD.find(std::to_string(value)) == valuesBDD.end()) ? bddfalsepp : valuesBDD[std::to_string(value)];
	}

	bdd nextVarValueBDD(std::string value) {
		return (nextValuesBDD.find(value) == nextValuesBDD.end()) ? bddfalsepp : nextValuesBDD[value];
	}

	bdd nextVarValueBDD(int value) {
		return (nextValuesBDD.find(std::to_string(value)) == nextValuesBDD.end()) ? bddfalsepp : nextValuesBDD[std::to_string(value)];
	}

	std::string GetNameFromBDD_DOT(bdd fun) {
		if (isBoolean()) {
			if (((fun & valuesBDD["TRUE"]) != bddfalsepp) && ((fun & valuesBDD["FALSE"]) == bddfalsepp)) return name;
			if (((fun & valuesBDD["TRUE"]) == bddfalsepp) && ((fun & valuesBDD["FALSE"]) != bddfalsepp)) return "<O>" + name + "</O>";
		}
		//else
		for(auto& item : valuesBDD) {
			if (((fun & item.second) != bddfalsepp) && ((fun & bdd_not(item.second)) == bddfalsepp)) return name + "=" + item.first;
		}
		//else
		return "";
	}

	bdd GetEqualNextBDD() {// get BDD: var = next(var)
		bdd res = bddtruepp;
		for (unsigned i = 0; i < varBDDCnt; i++)
			res &= bdd_apply(bdd_ithvar(id0 + i), bdd_ithvar(id0 + varBDDCnt + i), bddop_biimp);

		return res;
	}

	bool isBoolean() {
		return ((varBDDCnt == 1) && (valuesBDD.count("TRUE") == 1) && (valuesBDD.count("FALSE") == 1));
	}
};

class SMVModule {
private:
	std::string moduleName;
	std::vector<Variable> vars;
	std::vector<Variable> externalVars;
	std::vector<int> vars_IDs;
	std::vector<int> vars_NextIDs;

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
	
	void swap(SMVModule &smv1, SMVModule &smv2) {//[TA] or friend function?
		std::swap(smv1.vars, smv2.vars);
		std::swap(smv1.externalVars, smv2.externalVars);
		std::swap(smv1.moduleName, smv2.moduleName);
		std::swap(smv1.initial, smv2.initial);
		std::swap(smv1.transition, smv2.transition);
		std::swap(smv1.justice, smv2.justice);
	}
	
	SMVModule& operator=(const SMVModule& other) {
        SMVModule tmp(other);
		swap(*this, tmp);
        return *this;
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
		initial = initial & GetVariable(varName).varValueBDD(val_ini);
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
		throw("Error. Variable '" + varName + "' was not found.");
	}

	std::vector<Variable> GetInternalVariables() { return vars; }

	std::vector<int> GetVariablesIds() {
		if (vars_IDs.size() == 0) {
			for (unsigned i = 0; i < vars.size(); i++)
				for (unsigned j = 0; j < vars[i].GetVarBDDCnt(); j++)
					vars_IDs.push_back(vars[i].IDs()[j]);
		}

		return vars_IDs;
	}

	std::vector<int> GetVariablesNextIds() {
		if (vars_NextIDs.size() == 0) {
			for (unsigned i = 0; i < vars.size(); i++)
				for (unsigned j = 0; j < vars[i].GetVarBDDCnt(); j++)
					vars_NextIDs.push_back(vars[i].NextIDs()[j]);
		}

		return vars_NextIDs;
	}

	bool AddEmptyVariable(std::string varName) {
		for (unsigned i = 0; i < vars.size(); i++)
			if (varName == vars[i].Name()) return false;
		for (unsigned i = 0; i < externalVars.size(); i++)
			if (varName == externalVars[i].Name()) return false;

		vars.push_back(Variable(varName));
		return true;
	}

	bool AddVariable(Variable var) {
		for (unsigned i = 0; i < vars.size(); i++)
			if (var.Name() == vars[i].Name()) {
				/* [TA] we suppose that there will be no empty variables
				if (vars[i].GetVarBDDCnt() == 0) {
					vars[i] = var;
					return true;
				}*/
				return false;
			}

		vars.push_back(Variable(var));
		return true;
	}

	bool AddVariable(std::string varName) {
		for (unsigned i = 0; i < vars.size(); i++)
			if (varName == vars[i].Name()) {
				if (vars[i].GetVarBDDCnt() == 0) {
					vars[i].SetBooleanValues();
					return true;
				}
				return false;
			}

		Variable newVar(varName);
		newVar.SetBooleanValues();
		vars.push_back(newVar);
		return true;
	}

	bool AddVariable(std::string varName, std::vector<std::string> varValues) {
		for (unsigned i = 0; i < vars.size(); i++)
			if (varName == vars[i].Name()) {
				if (vars[i].GetVarBDDCnt() == 0) {
					vars[i].SetValues(varValues);
					return true;
				}
				return false;
			}

		Variable newVar(varName, varValues);
		vars.push_back(newVar);
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
	
	bdd getBDD(unsigned &i, std::string stop_sym, SMVModule* module) {
		bdd res = bddtrue;
		int prev_operator = bddop_and;
		// !!!!!!! добавить приоритеты операторов!
		static std::map<std::string, int> operatorsMap;
		static std::map<std::string, int> statesMap;
		if (operatorsMap.size() == 0) {//used to call the code below only once
			operatorsMap[")"] = -1;
			operatorsMap[";"] = -1;
			operatorsMap["&"] = bddop_and;
			operatorsMap["|"] = bddop_or;
			operatorsMap["->"] = bddop_imp;
			operatorsMap["<->"] = bddop_biimp;

			statesMap["("] = 1;
			statesMap[")"] = 2;
			statesMap["!"] = 3;
			statesMap["next"] = 4;
			statesMap[";"] = 5;
		}

		while(tokenText[i] != stop_sym) {//or until other special word
			switch(statesMap[tokenText[i]]) {
				case 1: {
					bdd temp = getBDD(++i, ")", module);

					res = bdd_apply(res, temp, prev_operator);
					break;
				}
				case 2: {
					i++;
					break;//throw exception: we can not reach this case!!!
				}
				case 3: {
					if (tokenText[++i] == "(") {
						bdd temp = getBDD(++i, ")", module);
						res = bdd_apply(res, bdd_not(temp), prev_operator);
					} else {
						if ((module->GetVariable(tokenText[i]).GetVarBDDCnt() > 1) || (module->GetVariable(tokenText[i]).varValueBDD("TRUE") == bddfalsepp))
							throw("Error. Variable '" + tokenText[i] + "' is not defined as boolean");
						res = bdd_apply(res, bdd_not(module->GetVariable(tokenText[i]).varValueBDD("TRUE")), prev_operator);
					}
					break;
				}
				case 4: {
					if (tokenText[++i] != "(") throw("Error while reading file. Expected '(', but '" + tokenText[i] + "' found.");
					//[TA] we could try to use grammar: next(bool_expr) instead of next(var). But it is rather complicated so I will ignore it.
					std::string varName = tokenText[++i];

					
					if (module->check_ifVariableExist(varName)) {
						Variable currVar = module->GetVariable(varName);

						i++;
						if (tokenText[i] == ")") {
							if ((currVar.GetVarBDDCnt() == 1) && (currVar.varValueBDD("TRUE") != bddfalsepp)) {
								res = bdd_apply(res, currVar.nextVarValueBDD("TRUE"), prev_operator);
							} else {
								throw("Error while reading file. Variable '" + tokenText[i] + "' is not defined as boolean.");
							}
						} else if (tokenText[i] == "=") {
							res = bdd_apply(res, currVar.nextVarValueBDD(tokenText[++i]), prev_operator);
							if (tokenText[++i] != ")")
								throw("Error while reading file. Expected ')' but '" + tokenText[i] + "' found.");
						} else
							throw("Error while reading file. Expected ')' or '=', but '" + tokenText[i] + "' found.");
					} else
						throw("Error while reading file. No variable '" + tokenText[i] + "' found.");

					break;
				}
				case 5: throw("Error while reading file. Expected boolean operator, but '" + tokenText[i] + "' found.");
				default: {//variable name by default
					if (module->check_ifVariableExist(tokenText[i])) {
						Variable currVar = module->GetVariable(tokenText[i]);
						if (tokenText[i + 1] == "=") {
							i++;
							std::string varValue = tokenText[++i];
							if (currVar.varValueBDD(varValue) != bddfalsepp) {
								res = bdd_apply(res, currVar.varValueBDD(varValue), prev_operator);
							} else
								throw("Error in input file. Variable '" + currVar.Name() + "' has no value '" + varValue + "'.");
						} else if ((currVar.GetVarBDDCnt() == 1) && (currVar.varValueBDD("TRUE") != bddfalsepp)) {
							res = bdd_apply(res, currVar.varValueBDD("TRUE"), prev_operator);
						} else
							throw("Error while reading file. Variable '" + currVar.Name() + "' is not defined as boolean.");
					} else
						throw("Error while reading file. No variable '" + tokenText[i] + "' found.");
				}
			}
			i++;
			if (i >= tokenText.size()) if (tokenText[++i] != ":") throw("Error while reading file. '" + stop_sym + "' expected before EOF");

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

				if (i >= tokenText.size()) if (tokenText[++i] != ":") throw("Error while reading file. " + stop_sym + " expected before EOF");
			} else break;// !!! throw Exception!
		}
		return res;
	}// end getBDD

	std::vector<Variable> readModuleVariables(std::string moduleName) {
		std::vector<Variable> res;

		unsigned i = 0;
		while (i < tokenText.size()) {
			if ((tokenText[i] == "MODULE") && (tokenText[i + 1] == moduleName)) break;
			++i;
		}
		if (i == tokenText.size()) {
			throw("Somethig went wrong... Module '" + moduleName + "' was not defined.");
		}
		if (tokenText[++i] == "(") {
			while(tokenText[++i] != ")") {}//later check if all external variables were defined earlier !!!
		}
		while ((tokenText[i] != "VAR") && (tokenText[i] != "MODULE") && (i < tokenText.size() - 1)) { ++i; }

		// We read all modules variables here.
		if (tokenText[i] == "VAR") {
			std::string next = tokenText[i + 1];
			while ((next != "TRANS") && (next != "MODULE") && (next != "JUSTICE") && (next != "ASSIGN")) {
				// read MODULE variables
				std::string name = tokenText[++i];
				if (tokenText[++i] != ":") throw("Error in input file. ':' expected but '" + tokenText[i] + "' found");
				std::string type = tokenText[++i];
				if (type == "boolean") {
					res.push_back(Variable(name));
					res[res.size() - 1].SetBooleanValues();
				} else if (type == "{") {//enumerable type
					std::vector<std::string> varValues;
					while(true) {
						std::string varValue = tokenText[++i];
						varValues.push_back(varValue);

						i++;
						if (tokenText[i] == "}") {
							break;
						} else if (tokenText[i] == ",") {
							continue;
						} else
							throw("Error in input file. '}' or ',' expected but '" + tokenText[i] + "' found");
					}
					res.push_back(Variable(name, varValues));
				}

				if (tokenText[++i] != ";") { throw("Error in input file. ';' expected but '" + tokenText[i] + "' found"); }
				next = tokenText[i + 1];
			}
		}
		return res;
	}

	void readMainSMVModule() {
		bool mainModuleExist = false;
		unsigned i = 0;

		std::map<std::string, int> modulePositions;//added to map temporary variable name to its position in allModules vector
		// === find main module: ========================
		while ((i < tokenText.size()) && !mainModuleExist) {
			if (tokenText[i] == "MODULE") {
				if (tokenText[++i] != "main") { continue; }
				mainModuleExist = true;
				if (tokenText[++i] != "VAR") throw("Error in input file. MODULE main: 'VAR' expected but '" + tokenText[i] + "' found");
			}
			i++;
		}
		if (!mainModuleExist) throw("Error in input file. MODULE main was not found.");
		//==============================================
		//		read all modules' names
		//==============================================
		for (int j = i; tokenText[j] != "MODULE"; j++) {
			if (tokenText[j] == "VAR") j++;

			std::string module_temporary_name = tokenText[j];
			if (tokenText[++j] != ":") throw("Error in input file. MODULE main: ':' expected but '" + tokenText[i] + "' found");
			std::string module_primary_name = tokenText[++j];

			allModules.push_back(SMVModule(module_primary_name));
			modulePositions[module_temporary_name] = allModules.size() - 1;

			while(tokenText[++j] != ";") {}
		}

		//==========================================================================
		//read all variables for all modules
		//==========================================================================
		for (unsigned j = 0; j < allModules.size(); j++) {
			std::vector<Variable> allVars = readModuleVariables(allModules[j].GetName());
			for (unsigned k = 0; k < allVars.size(); k++)
				allModules[j].AddVariable(allVars[k]);
		}
		//==========================================================================
		//read modules' variables that defined as external
		//==========================================================================
		SMVModule* otherModule;
		for (unsigned j = i; (tokenText[j] != "MODULE") && (j < tokenText.size()); j++) {
			if (tokenText[j] == "VAR") j++;

			std::string module_temporary_name = tokenText[j];
			++j;//tokenText[++j] == ":"
			std::string module_primary_name = tokenText[++j];

			if (tokenText[++j] == "(") {
				while(tokenText[j] != ")") {
					std::string otherModuleName = tokenText[++j];
					otherModule = &allModules[modulePositions[otherModuleName]];
					if (tokenText[++j] != ".") throw("Error in input file. MODULE main: '.' expected but '" + tokenText[i] + "' found.");

					std::string varName = tokenText[++j];

					GetModule(module_primary_name)->AddExternalVariable(otherModule->GetVariable(varName));
					if (tokenText[++j] == ",") continue;
				}
			}
			if (tokenText[++j] != ";") throw("Error in input file. MODULE main: ';' expected but '" + tokenText[i] + "' found.");
		}
	}

public:
	FileText(std::string fileName) {
		std::ifstream file(fileName);

		if (!file.is_open())
			std::cout << "File can not be opened!\n";//!!! throw Exception
		else {
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
	
    FileText(const FileText& other) {//  онструктор копировани€
		allModules = other.allModules;
		delims = other.delims;
		text = other.text;
		tokenText = other.tokenText;
    }
	
	~FileText() {
		text.clear();
		tokenText.clear();
		delims.clear();
		allModules.clear();
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

	void readSMVModules() {
		removeExtraData();
		bdd_init(20000000,2000000);//[TA] these numbers were set to have no GC calls for Mutual Exclusion Arbiter for 2-10 lines.
		bdd_setcacheratio(10);
		bdd_enable_reorder();

		readMainSMVModule();//here we read all modules names, create empty SMVModule elements, read and create modules' variables.

		//======================
		// Main parser!
		//======================
		// Here we get initial values, transitions and Justice requirements
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
							// read MODULE agruments: we are not reading them for the first time.
							while(tokenText[++i] != ")") { }
						}

						if (statesMap.find(tokenText[i + 1]) == statesMap.end()) throw("Error in input file. Expected one of 'MODULE, VAR, ASSIGN, TRANS, JUSTICE', but '" + allModules[m].GetName() + "' found.");
						break;
					}
					case 2: { 
						// all MODULE external variables were read earlier, so we skip this case
						break;
					}
					case 3: { // read MODULE initial values
						if (tokenText[i] != "init") throw("Error in input file. Expected 'init' but '" + tokenText[i] + "' found.");
						if (tokenText[++i] != "(") throw("Error in input file. Expected '(' but '" + tokenText[i] + "' found.");
						std::string varName = tokenText[++i];
						if (tokenText[++i] != ")") throw("Error in input file. Expected ')' but '" + tokenText[i] + "' found.");
						if (tokenText[++i] != ":=") throw("Error in input file. Expected ':=' but '" + tokenText[i] + "' found.");
						std::string val_ini = tokenText[++i];

						allModules[m].AddInitial(varName, val_ini);

						if (tokenText[++i] != ";") throw("Error in input file. Expected ';' before '" + tokenText[i] + "'");
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
					default: { throw("Error while reading file. One of 'MODULE', 'VAR', 'ASSIGN', 'TRANS', 'JUSTICE' expected but '" + tokenText[i] + "' found"); }
				}// end switch
			}
		}
	}

	SMVModule* GetModule(std::string moduleName) {
		for (unsigned i = 0; i < allModules.size(); i++)
			if (allModules[i].GetName() == moduleName) return &allModules[i];
		//else
		return NULL;//throw Exception
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
	std::vector<std::vector<std::vector<bdd>>> x_strat;//strategies for the system: leads the computation to J1-states
	std::vector<std::vector<bdd>> y_strat;//strategy for the system: leads the computation to get closer to J2-states

	unsigned log2(int val) {
		if (val == 0) return UINT_MAX;
		unsigned log = 0;
		while (val > 1) {
			val = val / 2 + val % 2;
			log++;
		}
		return log;
	}// end log2

	bdd Next(bdd vars) {
		static bddPair *sysEnv_Pairs = bdd_newpair();

		static bool b = true;
		if (b) {//used to call the code below only once
			b = false;

			std::vector<Variable> sys_vars = sys.GetInternalVariables();
			std::vector<Variable> env_vars = env.GetInternalVariables();

			for (unsigned i = 0; i < sys_vars.size(); i++)
				bdd_setpairs(sysEnv_Pairs, sys_vars[i].IDs(), sys_vars[i].NextIDs(), sys_vars[i].GetVarBDDCnt());
			for (unsigned i = 0; i < env_vars.size(); i++)
				bdd_setpairs(sysEnv_Pairs, env_vars[i].IDs(), env_vars[i].NextIDs(), sys_vars[i].GetVarBDDCnt());
		}

		return bdd_replace(vars, sysEnv_Pairs);
	}// end Next

	bdd NextAll(bdd vars) {
		static bddPair *allVars_Pairs = bdd_newpair();

		static bool b = true;
		if (b) {//used to call the code below only once
			b = false;

			std::vector<int> sys_vars_ids = sys.GetVariablesIds();
			std::vector<int> env_vars_ids = env.GetVariablesIds();
			std::vector<int> sys_vars_next_ids = sys.GetVariablesNextIds();
			std::vector<int> env_vars_next_ids = env.GetVariablesNextIds();

			for (unsigned i = 0; i < sys_vars_ids.size(); i++)
				bdd_setpair(allVars_Pairs, sys_vars_ids[i], sys_vars_next_ids[i]);
			for (unsigned i = 0; i < env_vars_ids.size(); i++)
				bdd_setpair(allVars_Pairs, env_vars_ids[i], env_vars_next_ids[i]);
			bdd_setpairs(allVars_Pairs, jx.IDs(), jx.NextIDs(), jx.GetVarBDDCnt());
		}
		return bdd_replace(vars, allVars_Pairs);
	}// end NextAll

	bdd UnprimeAll(bdd vars) {//get previous variable
		static bddPair *allVars_InvertPairs = bdd_newpair();

		static bool b = true;
		if (b) {//used to call the code below only once
			b = false;

			std::vector<int> sys_vars_ids = sys.GetVariablesIds();
			std::vector<int> env_vars_ids = env.GetVariablesIds();
			std::vector<int> sys_vars_next_ids = sys.GetVariablesNextIds();
			std::vector<int> env_vars_next_ids = env.GetVariablesNextIds();

			for (unsigned i = 0; i < sys_vars_ids.size(); i++)
				bdd_setpair(allVars_InvertPairs, sys_vars_next_ids[i], sys_vars_ids[i]);
			for (unsigned i = 0; i < env_vars_ids.size(); i++)
				bdd_setpair(allVars_InvertPairs, env_vars_next_ids[i], env_vars_ids[i]);
			bdd_setpairs(allVars_InvertPairs, jx.NextIDs(), jx.IDs(), jx.GetVarBDDCnt());
		}
		return bdd_replace(vars, allVars_InvertPairs);
	}// end UnprimeAll
	
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

	bdd forsome_next_jx(bdd fun) {
		//exist some primed jx
		bdd nextJx_BDDset = bdd_makeset(jx.NextIDs(), jx.GetVarBDDCnt());
		return bdd_exist(fun, nextJx_BDDset);
	}// end forsome_next_jx

	//[TA] check one more time!!!
	bdd step(bdd phi) { // function is named cox in the article
		cox_cnt++;
		std::vector<int> sys_varsIDs = sys.GetVariablesNextIds();

		static bdd sys_next_bdd = bddtruepp;//[TA] check: may be bddfalsepp
		if (sys_next_bdd == bddtruepp) {//[TA] this condition is to initialise sys_next_bdd only once
			int* sys_next_arr = new int[sys_varsIDs.size()];

			for (unsigned i = 0; i < sys_varsIDs.size(); i++)
				sys_next_arr[i] = sys_varsIDs[i];

			sys_next_bdd = bdd_makeset(sys_next_arr, sys_varsIDs.size());
		}
		//p_e => \exist y' such that (p_s and phi(x',y'))

		bdd res = bdd_imp(env.GetTransition(), bdd_exist(sys.GetTransition() & Next(phi), sys_next_bdd));
		//\foreach x'
		std::vector<int> env_next_IDs = env.GetVariablesNextIds();
		for (unsigned i = 0; i < env_next_IDs.size(); i++)
			res = bdd_forall(res, bdd_ithvarpp(env_next_IDs[i]));//////!!!!!!!!!!!!!!!!!!!!!!!!!!
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

	void reduce(bdd &trans, int j, int k) {
		bdd init = env.GetInitial() & sys.GetInitial();

		std::vector<Variable> env_vars = env.GetInternalVariables();
		std::vector<Variable> sys_vars = sys.GetInternalVariables();

		bdd obseq = bddtrue; //describes transitions where all variables except jx doesn't change:
		for (unsigned i = 0; i < env_vars.size(); i++)
			obseq &= env_vars[i].GetEqualNextBDD();
		for (unsigned i = 0; i < sys_vars.size(); i++)
			obseq &= sys_vars[i].GetEqualNextBDD();

		bdd states = forsome_next_V(trans & obseq & jx.varValueBDD(j) & jx.nextVarValueBDD(k));
		bdd add_trans = forsome_next_jx(trans & NextAll(states)) & jx.nextVarValueBDD(k);
		bdd add_init = forsome_next_jx((init) & states) & jx.varValueBDD(k);
		trans = (trans & !(NextAll(states) | states)) | add_trans;
		init = (init & !(states & jx.varValueBDD(j))) | add_init;
	}// end reduce

	State GetState(bdd allVarsBDD, bool ifFrom) {
		bdd bddState = allVarsBDD;//delete later bddState!!!
		if (ifFrom) {//we receive transition BDD, if we should take from-state, we delete all primed variables
			bddState = forsome_next_V(bddState);
		} else {
			//we delete all unprimed variables (from-states) and unprime other (primed) variables - we convert to-states into from-states
			bddState = UnprimeAll(forsome_V(bddState));
		}
		
		State state;

		// set Name
		state.name = "s";

		for (unsigned i = 0; i < bdd_varnum(); i++) {
			if ((bddState & bdd_ithvarpp(i)) == bddfalsepp) state.name += "0";
			if ((bddState & bdd_nithvarpp(i)) == bddfalsepp) state.name += "1";
		}
		// set Title
		state.title = "";
		std::vector<Variable> env_vars = env.GetInternalVariables();
		std::vector<Variable> sys_vars = sys.GetInternalVariables();
		for (unsigned i = 0; i < env_vars.size(); i++)
			state.title += env_vars[i].GetNameFromBDD_DOT(bddState) + ",";
		for (unsigned i = 0; i < sys_vars.size(); i++)
			state.title += sys_vars[i].GetNameFromBDD_DOT(bddState) + ",";
		state.title += " ";
		state.title += jx.GetNameFromBDD_DOT(bddState);

		state.initial = ((env.GetInitial() & sys.GetInitial() & bddState) != bddfalsepp) ? true : false;

		return state;
    }
public:
	GRGame() {}

	GRGame(SMVModule environment, SMVModule system) {
		env = environment;
		sys = system;
		y_strat.resize(sys.GetJustice().size());
		x_strat.resize(sys.GetJustice().size());
	}
	
	GRGame& operator=(const GRGame& other) {
        GRGame tmp(other);
        std::swap(*this, tmp);
        return *this;
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
		return z;
	}// end WinningRegion

	bdd getConroller(bdd z) {
		std::vector<bdd> fromjx, tojx;
		bdd trans = bddfalse;

		unsigned sysJ_cnt = sys.GetJustice().size();
		unsigned jx1 = bdd_varnum();//jx1 position
		//!!!потом перенести добавление переменных jx в инициализацию и проверить, изменилось ли врем€.

		std::vector<int> from0toN;
		for (unsigned i = 0; i < sysJ_cnt; i++)
			from0toN.push_back(i);
		jx = Variable(" jx", from0toN);//I give such name (" jx") because it can not be assigned for the other variables (parser doesn't allow to create the names like this).

		for (unsigned i = 0; i < sysJ_cnt; i++) {
			fromjx.push_back(jx.varValueBDD(from0toN[i]));
			tojx.push_back(jx.nextVarValueBDD(from0toN[i]));
		}
		// проверить: должно быть fromjx[i] == jx.varValueBDD(""+i)

		unsigned envJ_cnt = env.GetJustice().size();

		for (unsigned j = 0; j < sysJ_cnt; j++) {
			trans |= jx.varValueBDD(j) & jx.nextVarValueBDD((j + 1) % sysJ_cnt) & z & sys.GetJustice()[j] & env.GetTransition() & sys.GetTransition() & Next(z);
		}
		for (unsigned j = 0; j < sysJ_cnt; j++) {
			bdd low = y_strat[j][0];
			for (unsigned r = 1; r < y_strat[j].size(); r++) {//maxr[j] == y_strat[j].size()
				trans |= jx.varValueBDD(j) & jx.nextVarValueBDD(j) & y_strat[j][r] & !low & env.GetTransition() & sys.GetTransition() & Next(low);
				low |= y_strat[j][r];
			}
		}
		for (unsigned j = 0; j < sysJ_cnt; j++) {
			bdd low = bddfalse;
			for (unsigned r = 0; r < y_strat[j].size(); r++) {//maxr[j] == y_strat[j].size()
				for (unsigned i = 0; i < envJ_cnt; i++) {
					trans |= jx.varValueBDD(j) & jx.nextVarValueBDD(j) & x_strat[j][r][i] & !low & !env.GetJustice()[i] & env.GetTransition() & sys.GetTransition() & Next(x_strat[j][r][i]);
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

	void removeStuttering(bdd &bddtrans) {
		bdd stutter = bddtruepp;//only stuttering transitions (from states to themselves)
		for (unsigned i = 0; i < jx.GetVarBDDCnt(); i++)
			stutter &= bdd_biimp(bdd_ithvarpp(jx.IDs()[i]), bdd_ithvarpp(jx.NextIDs()[i]));
		for (unsigned i = 0; i < env.GetVariablesIds().size(); i++)
			stutter &= bdd_biimp(bdd_ithvarpp(env.GetVariablesIds()[i]), bdd_ithvarpp(env.GetVariablesNextIds()[i]));
		for (unsigned i = 0; i < sys.GetVariablesIds().size(); i++)
			stutter &= bdd_biimp(bdd_ithvarpp(sys.GetVariablesIds()[i]), bdd_ithvarpp(sys.GetVariablesNextIds()[i]));

		bddtrans &= !stutter;
	}// end removeStuttering

	bdd GetAllReachableTrans(bdd & bddTrans) {
		bdd res = env.GetInitial() & sys.GetInitial() & bddTrans,
			res_old;
		do {
			res_old = res;
			res = res | (UnprimeAll(forsome_V(res)) & bddTrans);
		} while(res_old != res);
		return res;
	}// end allReachableTrans

	void printDot(std::string fileName, bdd bddtrans) {
		std::ofstream out(fileName);
		if (!out.is_open()) return;//throw Exception!!!

		bdd nonPrinted_trans = GetAllReachableTrans(bddtrans);
		bdd trans_curr_bdd;
	
		out<<"digraph G {"<<std::endl;
		std::set<std::string> printedNames;
		std::string color;
	
		out << "init [shape = point, color = red];" << std::endl;
		while(nonPrinted_trans != bddfalsepp) {
			trans_curr_bdd = bdd_fullsatone(nonPrinted_trans);
			State from = GetState(trans_curr_bdd, true);
			State to = GetState(trans_curr_bdd, false);

			if (printedNames.count(from.name) == 0) {
				color = from.initial ? "red" : "black";
				out << from.name << " [label=<" << from.title << ">, color = " << color << "];"<<std::endl;
				printedNames.insert(from.name);
				if (from.initial)
					out<<"init -> " + from.name + " [color = red];"<<std::endl;//to show initial states we use additional state "init" and edges to these states
			}
			if (printedNames.count(to.name) == 0) {
				color = to.initial ? "red" : "black";
				out << to.name << " [label=<"<< to.title + ">, color = " << color << "];"<<std::endl;
				printedNames.insert(to.name);
				if (to.initial)
					out<<"init -> " + to.name + " [color = red];"<<std::endl;//to show initial states we use additional state "init" and edges to these states
			}
			out << "\"" << from.name << "\" -> \"" << to.name << "\";" << std::endl;

			nonPrinted_trans &= !trans_curr_bdd;
		}
		out<<"}"<<std::endl;
	}// end printDot
	
	bdd forsome_next_V(bdd fun) {//[TA] put it to private!!!
		std::vector<int> sys_vars_next_ids = sys.GetVariablesNextIds();
		std::vector<int> env_vars_next_ids = env.GetVariablesNextIds();

		int *primed_env_sys_jx_arr = new int[sys_vars_next_ids.size() + env_vars_next_ids.size() + jx.GetVarBDDCnt()];

		for (unsigned i = 0; i < sys_vars_next_ids.size(); i++)
			 primed_env_sys_jx_arr[i] = sys_vars_next_ids[i];
		for (unsigned i = 0; i < env_vars_next_ids.size(); i++)
			primed_env_sys_jx_arr[sys_vars_next_ids.size() + i] = env_vars_next_ids[i];
		for (unsigned i = 0; i < jx.GetVarBDDCnt(); i++) {
			primed_env_sys_jx_arr[sys_vars_next_ids.size() + env_vars_next_ids.size() + i] = jx.NextIDs()[i];
		}

		//exist v' from V: env_pr, sys_pr or jx_pr
		bdd nextV_BDDset = bdd_makeset(primed_env_sys_jx_arr, sys_vars_next_ids.size() + env_vars_next_ids.size() + jx.GetVarBDDCnt());
		return bdd_exist(fun, nextV_BDDset);
	}// end forsome_next_V

};// end class GRGame

void printFullSAT(bdd tmp) {//!!!! delete this
	std::ofstream out("tmp.txt");
	while (tmp != bddfalsepp) {
		bdd tmp1 = bdd_fullsatone(tmp);
		out << tmp1 << "\n";
		tmp &= !tmp1;
	}
}
int main(void)
{
	try {
		cox_cnt = 0;
		FileText file("arbiter9.smv");

		file.readSMVModules();

		SMVModule sys(*file.GetModule("sys"));
		SMVModule env(*file.GetModule("env"));
		GRGame arbiter2(env, sys);
		long t1 = clock();
		bdd win_reg = arbiter2.WinningRegion();
		if ((env.GetInitial() & sys.GetInitial() & win_reg) == bddfalse) {
			std::cout << "GR requirements are not realizable!" << std::endl;
		}
		long t2 = clock();
		std::cout << "Win reg: " << t2 - t1 << std::endl;
		bdd jds = arbiter2.getConroller(win_reg);
		long t3 = clock();
		std::cout << "synthesis : " << t3 - t2 << std::endl;

		arbiter2.removeStuttering(jds);//[TA] вообще, система переходов должна быть детерминированной по построению => она без дребезжани€!!!
		jds = arbiter2.GetAllReachableTrans(jds); // если удалить недостижимые переходы, минимизаци€ пройдет быстрее. ј затем снова можно удалить недостижимые. ¬џ√ќƒЌќ!

		arbiter2.Minimize(jds);

		arbiter2.removeStuttering(jds);//[TA] вообще, система переходов должна быть детерминированной по построению => она без дребезжани€!!!
		jds = arbiter2.GetAllReachableTrans(jds);
		
		//arbiter2.printDot("JDS_result.dot", jds);
		std::cout << "minimize : " << clock() - t3 << std::endl;

		std::cout << "cox cnt " << cox_cnt << "\n\n";
		std::cout << "SAT count : " << bdd_satcount(jds) << std::endl;
		//std::cout << "Node count: " << bdd_nodecount(jds) << std::endl;
		//std::cout << "Controller nodes count: " << bdd_satcount(arbiter2.forsome_next_V(arbiter2.GetAllReachableTrans(jds)) & bdd_ithvar(0) & bdd_ithvar(2) & bdd_ithvar(4) & bdd_ithvar(6) & bdd_ithvar(8) & bdd_ithvar(10) & bdd_ithvar(12) & arbiter2.[0]) << std::endl;
	}
	catch(std::string err) {
		std::cout << err << std::endl;
	}

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
