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

#pragma comment(lib, "Debug/bdd.lib")	// BuDDy library
#include "bdd.h"
#include "variable.h"
#include "module.h"
#include "grGame.h"

#include <vector>
#include <string>
#include <set>
#include <map>
#include <fstream>
#include <time.h>


class FileText {
private:
	std::vector<std::string> text;
	std::vector<std::string> tokenText;
	std::vector<std::string> delims;
	std::vector<SMVModule> allModules;

	std::pair<int, unsigned> getFirstDelimiterPos(std::vector<std::string> delims, std::string val) {
		std::pair<int, unsigned> min_index(val.size() + 1, delims.size());

		for (unsigned i = 0; i < delims.size(); i++) {
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
		// [TA] the main thing that should be also implemented: 
		// There is no boolean operators priority. Should be added later...
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
				case 2:	throw(std::string("Error in input file. Extra ')' was found"));
				case 3: {
					if (tokenText[++i] == "(") {
						bdd temp = getBDD(++i, ")", module);
						res = bdd_apply(res, bdd_not(temp), prev_operator);
					} else {//[TA] I could also use grammar "!next(var)" or next(!var), but it is not necessary for now.
						if ((module->GetVariable(tokenText[i]).GetVarBDDCnt() > 1) || (module->GetVariable(tokenText[i]).varValueBDD("TRUE") == bddfalsepp))
							throw("Error. Variable '" + tokenText[i] + "' is not defined as boolean");
						res = bdd_apply(res, bdd_not(module->GetVariable(tokenText[i]).varValueBDD("TRUE")), prev_operator);
					}
					break;
				}
				case 4: {
					if (tokenText[++i] != "(") throw("Error while reading file. Expected '(', but '" + tokenText[i] + "' found.");
					//[TA] I could try to use grammar: next(bool_expr) instead of next(var). But it is rather complicated so I will ignore it.
					std::string varName = tokenText[++i];

					if (module->check_ifVariableExist(varName)) {
						Variable currVar = module->GetVariable(varName);

						i++;
						if (tokenText[i] == ")") {
							if ((currVar.GetVarBDDCnt() == 1) && (currVar.varValueBDD("TRUE") != bddfalsepp)) {
								res = bdd_apply(res, currVar.nextVarValueBDD("TRUE"), prev_operator);
							} else {
								throw("Error in input file. Variable '" + tokenText[i] + "' is not defined as boolean.");
							}
						} else if (tokenText[i] == "=") {
							res = bdd_apply(res, currVar.nextVarValueBDD(tokenText[++i]), prev_operator);
							if (tokenText[++i] != ")")
								throw("Error in input file. Expected ')' but '" + tokenText[i] + "' found.");
						} else
							throw("Error in input file. Expected ')' or '=', but '" + tokenText[i] + "' found.");
					} else
						throw("Error in input file. No variable '" + tokenText[i] + "' found.");

					break;
				}
				case 5: throw("Error in input file. Expected boolean operator, but '" + tokenText[i] + "' found.");
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
							throw("Error in input file. Variable '" + currVar.Name() + "' is not defined as boolean.");
					} else
						throw("Error in input file. No variable '" + tokenText[i] + "' found.");
				}
			}
			i++;
			if (i >= tokenText.size()) throw("Error in input file. '" + stop_sym + "' expected before EOF");

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

				if (i >= tokenText.size()) throw("Error in input file. " + stop_sym + " expected before EOF");
			} else throw("Error in input file. Expected one of: ')', ';', '&', '|', '->', '<->' but '" + tokenText[i] + "' found.");
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
		if (i == tokenText.size())
			throw("Somethig went wrong... Module '" + moduleName + "' was not defined.");

		if (tokenText[++i] == "(") {
			while(tokenText[++i] != ")") {}//later check if all external variables were defined earlier. Not implemented, but may be(?) it is excess.
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
			throw(std::string("Error. File can not be opened!"));
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
			// check if we read "MODULE" token while reading our module: this means our (current) module description is ended
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
						if (tokenText[i++] != allModules[m].GetName()) { state = 0; break; }

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

	void printFile(std::ofstream& stream) {
		for (unsigned i = 0; i < text.size(); i++) {
			stream << text[i];
		}
	}

	void printFileTokens(std::ofstream& stream) {
		for (unsigned i = 0; i < tokenText.size(); i++) {
			stream << tokenText[i] << " ";
		}
	}
};// end class FileText

int main(void)
{
	try {
		FileText file("testdata/arbiter2.smv");

		file.readSMVModules();
		SMVModule sys(*file.GetModule("sys"));
		SMVModule env(*file.GetModule("env"));
		GRGame grGame(env, sys);
		long t1 = clock();
		bdd win_reg = grGame.WinningRegion();
		if ((env.GetInitial() & sys.GetInitial() & win_reg) == bddfalse) {
			std::cout << "GR requirements are not realizable!" << std::endl;
		}
		long t2 = clock();
		std::cout << "Win reg: " << t2 - t1 << std::endl;
		bdd jds = grGame.getConroller(win_reg);
		long t3 = clock();
		std::cout << "synthesis : " << t3 - t2 << std::endl;

		grGame.removeStuttering(jds);
		jds = grGame.GetAllReachableTrans(jds); // if we delete unreachable transitions minimisation will be faster. And then remove them one more time. Profit!

		grGame.Minimize(jds);

		grGame.removeStuttering(jds);
		jds = grGame.GetAllReachableTrans(jds);

		std::cout << "minimize : " << clock() - t3 << std::endl;

		// for big GR-games should be commented: resulting controllers are HUGE!
		grGame.printDot("result_controller_DOT/JDS_result.dot", jds);

		std::cout << "SAT count : " << bdd_satcount(jds) << std::endl;
		//std::cout << "Controller nodes count: " << bdd_satcount(arbiter2.forsome_next_V(arbiter2.GetAllReachableTrans(jds)) & bdd_ithvar(0) & bdd_ithvar(2) & bdd_ithvar(4) & bdd_ithvar(6) & bdd_ithvar(8) & bdd_ithvar(10) & bdd_ithvar(12) & arbiter2.[0]) << std::endl;
	}
	catch(std::string err) {
		std::cout << err << std::endl;
	}

	system("pause");
	return 0;
}