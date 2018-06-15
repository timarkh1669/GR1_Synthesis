#include "bdd.h"
#include "variable.h"

Variable::Variable(std::string name_str) {
	name = name_str;
	id0 = -1;
	varBDDCnt = 0;
}

Variable::Variable(std::string name_str, std::vector<std::string> var_values) {
	name = name_str;
	id0 = bdd_varnum();
	varBDDCnt = log2(var_values.size());
	bdd_extvarnum(varBDDCnt * 2);// because we use second vars set to encode next(var)

	for (unsigned i = 0; i < var_values.size(); i++) {
		valuesBDD[var_values[i]] = bdd_ithfun(i, id0, varBDDCnt);
		nextValuesBDD[var_values[i]] = bdd_ithfun(i, id0 + varBDDCnt, varBDDCnt);
	}	
}
	
Variable::Variable(std::string name_str, std::vector<int> var_values) {
	name = name_str;
	id0 = bdd_varnum();
	varBDDCnt = log2(var_values.size());
	bdd_extvarnum(varBDDCnt * 2);// because we use second vars set to encode next(var)

	for (unsigned i = 0; i < var_values.size(); i++) {
		valuesBDD[std::to_string(var_values[i])] = bdd_ithfun(i, id0, varBDDCnt);
		nextValuesBDD[std::to_string(var_values[i])] = bdd_ithfun(i, id0 + varBDDCnt, varBDDCnt);
	}
}

Variable::Variable(const Variable& other) {
	name = other.name;
	id0 = other.id0;
	valuesBDD = other.valuesBDD;
	nextValuesBDD = other.nextValuesBDD;
	varBDDCnt = other.varBDDCnt;
}

Variable& Variable::operator=(const Variable& other) {
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
Variable::~Variable() {
	name.clear();
	valuesBDD.clear();
}

std::string Variable::Name() {
	return name;
}

bool Variable::SetBooleanValues() {
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
	
bool Variable::SetValues(std::vector<std::string> var_values) {
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

bool Variable::SetValues(std::vector<int> var_values) {
	if (varBDDCnt > 0) return false;//if we have already set values earlier
	id0 = bdd_varnum();
	varBDDCnt = log2(var_values.size());
	bdd_extvarnum(varBDDCnt * 2);// because we use second vars set to encode next(var)

	for (unsigned i = 0; i < var_values.size(); i++) {
		valuesBDD[std::to_string(var_values[i])] = bdd_ithfun(i, id0, varBDDCnt);
		nextValuesBDD[std::to_string(var_values[i])] = bdd_ithfun(i, id0 + varBDDCnt, varBDDCnt);
	}
	return true;
}

int* Variable::IDs() {//all BDD variables IDs used to encode this Variable
	int *res = new int[varBDDCnt];
	for (unsigned i = 0; i < varBDDCnt; i++)
		res[i] = id0 + i;

	return res;
}

int* Variable::NextIDs() {//all BDD variables IDs used to encode Next(Variable) (next <=> primed)
	int *res = new int[varBDDCnt];
	for (unsigned i = 0; i < varBDDCnt; i++)
		res[i] = id0 + varBDDCnt + i;

	return res;
}

unsigned Variable::GetVarBDDCnt() {
	return varBDDCnt;
}

bdd Variable::varValueBDD(std::string value) {
	return (valuesBDD.find(value) == valuesBDD.end()) ? bddfalsepp : valuesBDD[value];
}

bdd Variable::varValueBDD(int value) {
	return (valuesBDD.find(std::to_string(value)) == valuesBDD.end()) ? bddfalsepp : valuesBDD[std::to_string(value)];
}

bdd Variable::nextVarValueBDD(std::string value) {
	return (nextValuesBDD.find(value) == nextValuesBDD.end()) ? bddfalsepp : nextValuesBDD[value];
}

bdd Variable::nextVarValueBDD(int value) {
	return (nextValuesBDD.find(std::to_string(value)) == nextValuesBDD.end()) ? bddfalsepp : nextValuesBDD[std::to_string(value)];
}

std::string Variable::GetNameFromBDD_DOT(bdd fun) {
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

bdd Variable::GetEqualNextBDD() {// get BDD: var = next(var)
	bdd res = bddtruepp;
	for (unsigned i = 0; i < varBDDCnt; i++)
		res &= bdd_apply(bdd_ithvar(id0 + i), bdd_ithvar(id0 + varBDDCnt + i), bddop_biimp);

	return res;
}

bool Variable::isBoolean() {
	return ((varBDDCnt == 1) && (valuesBDD.count("TRUE") == 1) && (valuesBDD.count("FALSE") == 1));
}

unsigned Variable::log2(int val) {
	if (val == 0) return UINT_MAX;
	unsigned log = 0;
	while (val > 1) {
		val = val / 2 + val % 2;
		log++;
	}
	return log;
}// end log2

bdd Variable::bdd_ithfun(int f_num, int fromVar, unsigned varCnt) {
	bdd fun = bddtruepp;
	for (unsigned i = 0; i < varCnt; i++)
		fun &= ((f_num >> (varCnt - i) - 1) & 1) ? bdd_ithvarpp(i + fromVar) : bdd_nithvarpp(i + fromVar);
	return fun;
}// end bdd_ithfun