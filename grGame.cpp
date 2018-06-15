#include "variable.h"
#include "module.h"
#include "grGame.h"

#include <set>
#include <fstream>

	/*SMVModule sys;
	SMVModule env;
	Variable jx;
	std::vector<std::vector<std::vector<bdd>>> x_strat;//strategies for the system: leads the computation to J1-states
	std::vector<std::vector<bdd>> y_strat;//strategy for the system: leads the computation to get closer to J2-states
	*/


bdd GRGame::Next(bdd vars) {
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

bdd GRGame::NextAll(bdd vars) {
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

bdd GRGame::UnprimeAll(bdd vars) {//get previous variable
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
	
bdd GRGame::forsome_V(bdd fun) {
	std::vector<int> sys_vars_ids = sys.GetVariablesIds();
	std::vector<int> env_vars_ids = env.GetVariablesIds();

	static bdd v_BDDset = bddtruepp;
	if (v_BDDset == bddtruepp) {//this condition is to initialise v_BDDset only once
		int *env_sys_jx_arr = new int[sys_vars_ids.size() + env_vars_ids.size() + jx.GetVarBDDCnt()];

		for (unsigned i = 0; i < sys_vars_ids.size(); i++)
				env_sys_jx_arr[i] = sys_vars_ids[i];
		for (unsigned i = 0; i < env_vars_ids.size(); i++)
			env_sys_jx_arr[sys_vars_ids.size() + i] = env_vars_ids[i];
		for (unsigned i = 0; i < jx.GetVarBDDCnt(); i++)
			env_sys_jx_arr[sys_vars_ids.size() + env_vars_ids.size() + i] = jx.IDs()[i];

		v_BDDset = bdd_makeset(env_sys_jx_arr, sys_vars_ids.size() + env_vars_ids.size() + jx.GetVarBDDCnt());
	}

	//exist v from V: env, sys or jx
	return bdd_exist(fun, v_BDDset);
}// end forsome_V

bdd GRGame::forsome_next_jx(bdd fun) {
	//exist some primed jx
	static bdd nextJx_BDDset = bdd_makeset(jx.NextIDs(), jx.GetVarBDDCnt());
	return bdd_exist(fun, nextJx_BDDset);
}// end forsome_next_jx

bdd GRGame::forsome_next_V(bdd fun) {
	std::vector<int> sys_vars_next_ids = sys.GetVariablesNextIds();
	std::vector<int> env_vars_next_ids = env.GetVariablesNextIds();

	static bdd nextV_BDDset = bddtruepp;
	if (nextV_BDDset == bddtruepp) {//this condition is to initialise nextV_BDDset only once
		int *primed_env_sys_jx_arr = new int[sys_vars_next_ids.size() + env_vars_next_ids.size() + jx.GetVarBDDCnt()];

		for (unsigned i = 0; i < sys_vars_next_ids.size(); i++)
				primed_env_sys_jx_arr[i] = sys_vars_next_ids[i];
		for (unsigned i = 0; i < env_vars_next_ids.size(); i++)
			primed_env_sys_jx_arr[sys_vars_next_ids.size() + i] = env_vars_next_ids[i];
		for (unsigned i = 0; i < jx.GetVarBDDCnt(); i++) {
			primed_env_sys_jx_arr[sys_vars_next_ids.size() + env_vars_next_ids.size() + i] = jx.NextIDs()[i];
		}
		nextV_BDDset = bdd_makeset(primed_env_sys_jx_arr, sys_vars_next_ids.size() + env_vars_next_ids.size() + jx.GetVarBDDCnt());
	}

	//exist v' from V: env_pr, sys_pr or jx_pr
	return bdd_exist(fun, nextV_BDDset);
}// end forsome_next_V

bdd GRGame::step(bdd phi) { // function is named cox in the 'Piterman2006' article
	static bdd sys_next_bdd = bddtruepp;
	if (sys_next_bdd == bddtruepp) {// this condition is used to initialise sys_next_bdd only once
		std::vector<int> sys_varsIDs = sys.GetVariablesNextIds();
		int* sys_next_arr = new int[sys_varsIDs.size()];

		for (unsigned i = 0; i < sys_varsIDs.size(); i++)
			sys_next_arr[i] = sys_varsIDs[i];

		sys_next_bdd = bdd_makeset(sys_next_arr, sys_varsIDs.size());
	}
	//p_e => \exist y' such that (p_s and phi(x',y'))
	bdd res = bdd_imp(env.GetTransition(), bdd_exist(sys.GetTransition() & Next(phi), sys_next_bdd));
		
	//\foreach x'
	static bdd env_next_bdd = bddtruepp;
	if (env_next_bdd == bddtruepp) {// this condition is used to initialise env_next_bdd only once
		std::vector<int> env_next_IDs = env.GetVariablesNextIds();
		int* env_next_arr = new int[env_next_IDs.size()];

		for (unsigned i = 0; i < env_next_IDs.size(); i++)
			env_next_arr[i] = env_next_IDs[i];

		env_next_bdd = bdd_makeset(env_next_arr, env_next_IDs.size());
	}

	return bdd_forall(res, env_next_bdd);
}// end step(cox)

bdd GRGame::greatestFixPoint(bdd & z, bdd & start, int i) {
	bdd x = z,
		x_old;
	do {
		x_old = x;
		x = !env.GetJustice()[i] & step(x) | start;
	} while(x_old != x);
	return x;
}// end greatestFixPoint

bdd GRGame::leastFixPoint(bdd & z, int j) {
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

void GRGame::reduce(bdd &trans, int j, int k) {
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

State GRGame::GetState(bdd allVarsBDD, bool ifFrom) {
	bdd bddState = ifFrom
		? forsome_next_V(allVarsBDD)//if we should take from-state, we delete all primed variables
		: bddState = UnprimeAll(forsome_V(allVarsBDD));//we delete all unprimed variables (from-states) and unprime other (primed) variables: we convert to-states into from-states
		
	State state;

	// set Name:
	state.name = "s";
	for (int i = 0; i < bdd_varnum(); i++) {
		if ((bddState & bdd_ithvarpp(i)) == bddfalsepp) state.name += "0";
		if ((bddState & bdd_nithvarpp(i)) == bddfalsepp) state.name += "1";
	}

	// set Title:
	state.title = "";
	std::vector<Variable> env_vars = env.GetInternalVariables();
	std::vector<Variable> sys_vars = sys.GetInternalVariables();
	for (unsigned i = 0; i < env_vars.size(); i++)
		state.title += env_vars[i].GetNameFromBDD_DOT(bddState) + ",";
	for (unsigned i = 0; i < sys_vars.size(); i++)
		state.title += sys_vars[i].GetNameFromBDD_DOT(bddState) + ",";
	state.title += " ";
	state.title += jx.GetNameFromBDD_DOT(bddState);

	// set Initial:
	state.initial = ((env.GetInitial() & sys.GetInitial() & bddState) != bddfalsepp) ? true : false;

	return state;
}

GRGame::GRGame(SMVModule environment, SMVModule system) {
	env = environment;
	sys = system;
	y_strat.resize(sys.GetJustice().size());
	x_strat.resize(sys.GetJustice().size());

	// set JX variables:
	std::vector<int> from0toN;
	for (unsigned i = 0; i < sys.GetJustice().size(); i++)
		from0toN.push_back(i);
	jx = Variable(" jx", from0toN);//I give such name (" jx") because it can not be assigned for the other variables (parser doesn't allow to create the names like this).
}
	
bdd GRGame::WinningRegion() {
	bdd z = bddtruepp,
		z_old;

	do {//GratestFixPoint(z)
		z_old = z;
		for (unsigned j = 0; j < sys.GetJustice().size(); j++)
			z = leastFixPoint(z, j);
	} while(z != z_old);
	return z;
}// end WinningRegion

bdd GRGame::getConroller(bdd z) {
	unsigned envJ_cnt = env.GetJustice().size();
	unsigned sysJ_cnt = sys.GetJustice().size();

	bdd trans = bddfalse;

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

void GRGame::Minimize(bdd &trans) {
	//n == jxCnt
	std::ofstream out;
	for (unsigned j = 0; j < sys.GetJustice().size(); j++)
		reduce(trans, j, (j + 1) % sys.GetJustice().size());
	for (unsigned j = 0; j < sys.GetJustice().size() - 1; j++)
		reduce(trans, sys.GetJustice().size() - 1, j);
}

void GRGame::removeStuttering(bdd &bddtrans) {
	bdd stutter = bddtruepp;//only stuttering transitions (from states to themselves)
	for (unsigned i = 0; i < jx.GetVarBDDCnt(); i++)
		stutter &= bdd_biimp(bdd_ithvarpp(jx.IDs()[i]), bdd_ithvarpp(jx.NextIDs()[i]));
	for (unsigned i = 0; i < env.GetVariablesIds().size(); i++)
		stutter &= bdd_biimp(bdd_ithvarpp(env.GetVariablesIds()[i]), bdd_ithvarpp(env.GetVariablesNextIds()[i]));
	for (unsigned i = 0; i < sys.GetVariablesIds().size(); i++)
		stutter &= bdd_biimp(bdd_ithvarpp(sys.GetVariablesIds()[i]), bdd_ithvarpp(sys.GetVariablesNextIds()[i]));

	bddtrans &= !stutter;
}// end removeStuttering

bdd GRGame::GetAllReachableTrans(bdd & bddTrans) {
	bdd res = env.GetInitial() & sys.GetInitial() & bddTrans,
		res_old;
	do {
		res_old = res;
		res = res | (UnprimeAll(forsome_V(res)) & bddTrans);
	} while(res_old != res);
	return res;
}// end allReachableTrans

void GRGame::printDot(std::string fileName, bdd bddtrans) {
	std::ofstream out(fileName);
	if (!out.is_open()) throw("Error while printing controller. File '" + fileName + "' can not be opened.");

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
