#include "variable.h"
#include "module.h"

SMVModule::SMVModule() {
	moduleName = "";
	initial = bddtruepp;
	transition = bddtruepp;
}
	
SMVModule::SMVModule(std::string name) {
	moduleName = name;
	initial = bddtruepp;
	transition = bddtruepp;
}
	
SMVModule::SMVModule(const SMVModule& other) {
	moduleName = other.moduleName;
	vars = other.vars;
	externalVars = other.externalVars;
	vars_IDs = other.vars_IDs;
	vars_NextIDs = other.vars_NextIDs;
	initial = other.initial;
	transition = other.transition;
	justice = other.justice;
}

SMVModule& SMVModule::operator=(const SMVModule& other) {
	if (this != &other) {
		moduleName = other.moduleName;
		vars = other.vars;
		externalVars = other.externalVars;
		vars_IDs = other.vars_IDs;
		vars_NextIDs = other.vars_NextIDs;
		initial = other.initial;
		transition = other.transition;
		justice = other.justice;
    }
    return *this;
}
// end constructors
SMVModule::~SMVModule() {
	moduleName.clear();
	vars.clear();
	externalVars.clear();
	vars_IDs.clear();
	vars_NextIDs.clear();
	justice.clear();
}

std::string SMVModule::GetName() {
	return moduleName;
}

void SMVModule::SetName(std::string name) {
	moduleName = name;
}
	
bdd SMVModule::GetInitial() {
	return initial;
}

void SMVModule::SetInitial(bdd ini) {
	initial = ini;
}
	
void SMVModule::AddInitial(bdd ini) {
	initial = initial & ini;
}

void SMVModule::AddInitial(std::string varName, std::string val_ini) {
	initial = initial & GetVariable(varName).varValueBDD(val_ini);
}
	
bool SMVModule::check_ifVariableExist(std::string varName) {
	for (unsigned i = 0; i < vars.size(); i++)
		if (varName == vars[i].Name()) return true;
	for (unsigned i = 0; i < externalVars.size(); i++)
		if (varName == externalVars[i].Name()) return true;
	//else
	return false;
}

Variable SMVModule::GetVariable(std::string varName) {
	for (unsigned i = 0; i < vars.size(); i++)
		if (varName == vars[i].Name()) return vars[i];
	for (unsigned i = 0; i < externalVars.size(); i++)
		if (varName == externalVars[i].Name()) return externalVars[i];
	//else
	throw("Error. Variable '" + varName + "' was not found.");
}

std::vector<Variable> SMVModule::GetInternalVariables() { return vars; }

std::vector<int> SMVModule::GetVariablesIds() {
	if (vars_IDs.size() == 0) {
		for (unsigned i = 0; i < vars.size(); i++)
			for (unsigned j = 0; j < vars[i].GetVarBDDCnt(); j++)
				vars_IDs.push_back(vars[i].IDs()[j]);
	}

	return vars_IDs;
}

std::vector<int> SMVModule::GetVariablesNextIds() {
	if (vars_NextIDs.size() == 0) {
		for (unsigned i = 0; i < vars.size(); i++)
			for (unsigned j = 0; j < vars[i].GetVarBDDCnt(); j++)
				vars_NextIDs.push_back(vars[i].NextIDs()[j]);
	}
	return vars_NextIDs;
}

bool SMVModule::AddEmptyVariable(std::string varName) {
	for (unsigned i = 0; i < vars.size(); i++)
		if (varName == vars[i].Name()) return false;
	for (unsigned i = 0; i < externalVars.size(); i++)
		if (varName == externalVars[i].Name()) return false;

	vars.push_back(Variable(varName));
	return true;
}

bool SMVModule::AddVariable(Variable var) {
	for (unsigned i = 0; i < vars.size(); i++)
		if (var.Name() == vars[i].Name()) {
			//We suppose that there will be no empty variables. But this code is used to be on the safe side.
			if (vars[i].GetVarBDDCnt() == 0) {
				vars[i] = var;
				return true;
			}
			return false;
		}

	vars.push_back(Variable(var));
	return true;
}

bool SMVModule::AddVariable(std::string varName) {
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

bool SMVModule::AddVariable(std::string varName, std::vector<std::string> varValues) {
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

void SMVModule::AddExternalVariable(Variable ext_var) {
	externalVars.push_back(ext_var);
}

void SMVModule::SetTransition(bdd trans) {
	transition = trans;
}

bdd SMVModule::GetTransition() {
	return transition;
}

void SMVModule::AddJustice(bdd justice_new) {
	justice.push_back(justice_new);
}

std::vector<bdd> SMVModule::GetJustice() {
	return justice;
}
