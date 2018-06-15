#include <vector>
#include <string>

struct State {
	std::string name;
	std::string title;
	bool initial;
};

class GRGame {
private:
	SMVModule sys;
	SMVModule env;
	Variable jx;
	std::vector<std::vector<std::vector<bdd>>> x_strat;//strategies for the system: leads the computation to J1-states
	std::vector<std::vector<bdd>> y_strat;//strategy for the system: leads the computation to get closer to J2-states

	bdd Next(bdd vars);

	bdd NextAll(bdd vars);

	bdd UnprimeAll(bdd vars);
	
	bdd forsome_V(bdd fun);

	bdd forsome_next_jx(bdd fun);

	bdd forsome_next_V(bdd fun);

	bdd step(bdd phi);// function is named cox in the 'Piterman2006' article

	bdd greatestFixPoint(bdd & z, bdd & start, int i);

	bdd leastFixPoint(bdd & z, int j);

	void reduce(bdd &trans, int j, int k);

	State GetState(bdd allVarsBDD, bool ifFrom);

public:
	GRGame(SMVModule environment, SMVModule system);
	
	bdd WinningRegion();

	bdd getConroller(bdd z);

	void Minimize(bdd &trans);

	void removeStuttering(bdd &bddtrans);

	bdd GetAllReachableTrans(bdd & bddTrans);

	void printDot(std::string fileName, bdd bddtrans);
};// end class GRGame
