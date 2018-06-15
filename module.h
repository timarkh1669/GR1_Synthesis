#ifndef MODULE_H
#define MODULE_H

#include <vector>
#include <string>

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
	SMVModule();
	
	SMVModule(std::string name);
	
	SMVModule(const SMVModule& other);

	SMVModule& operator=(const SMVModule& other);

	~SMVModule();

	std::string GetName();

	void SetName(std::string name);
	
	bdd GetInitial();

	void SetInitial(bdd ini);
	
	void AddInitial(bdd ini);

	void AddInitial(std::string varName, std::string val_ini);
	
	bool check_ifVariableExist(std::string varName);

	Variable GetVariable(std::string varName);

	std::vector<Variable> GetInternalVariables();

	std::vector<int> GetVariablesIds();

	std::vector<int> GetVariablesNextIds();

	bool AddEmptyVariable(std::string varName);

	bool AddVariable(Variable var);

	bool AddVariable(std::string varName);

	bool AddVariable(std::string varName, std::vector<std::string> varValues);

	void AddExternalVariable(Variable ext_var);

	void SetTransition(bdd trans);

	bdd GetTransition();

	void AddJustice(bdd justice_new);

	std::vector<bdd> GetJustice();
};//end class SMVModule


#endif