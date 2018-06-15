#ifndef VARIABLE_H
#define VARIABLE_H

#include "bdd.h"
#include <vector>
#include <string>
#include <map>

using namespace std;

class Variable {
private:
	std::string name;
	std::map<std::string, bdd> valuesBDD;
	std::map<std::string, bdd> nextValuesBDD;
	unsigned varBDDCnt;// count of BDD variables used to encode this Variable
	int id0;

	unsigned log2(int val);
	bdd bdd_ithfun(int f_num, int fromVar, unsigned varCnt);

public:
	Variable() {};

	Variable(std::string name_str);

	Variable(std::string name_str, std::vector<std::string> var_values);
	
	Variable(std::string name_str, std::vector<int> var_values);

	Variable(const Variable& other);

	Variable& operator=(const Variable& other);
	~Variable();

	std::string Name();

	bool SetBooleanValues();
	
	bool SetValues(std::vector<std::string> var_values);

	bool SetValues(std::vector<int> var_values);

	int* IDs();//all BDD variables IDs used to encode this Variable

	int* NextIDs();//all BDD variables IDs used to encode Next(Variable) (next <=> primed)

	unsigned GetVarBDDCnt();//get count of BDD variables used to encode this Variable (not Next)

	bdd varValueBDD(std::string value);//get BDD that satisfies expression: "var = value"

	bdd varValueBDD(int value);//get BDD that satisfies expression: "var = value"

	bdd nextVarValueBDD(std::string value);//get BDD that satisfies expression: "next(var = value)"

	bdd nextVarValueBDD(int value);//get BDD that satisfies expression: "next(var = value)"

	std::string GetNameFromBDD_DOT(bdd fun);

	bdd GetEqualNextBDD();// get BDD: var = next(var)

	bool isBoolean();// flag if this Variable is boolean or enumerable
};

#endif