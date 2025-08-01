#ifndef _KCounter_h_
#define _KCounter_h_

#include "../Component_Types/Incremental_Component.h"
#include "../Component_Types/Incremental_Component_BigInt.h"
#include "../Extensive_Inprocessor.h"

/*
thl add 
*/

// #include "../../lib/cudd-3.0.0/cplusplus/cuddObj.hh"
// #include "../../lib/cudd-3.0.0/cudd/cuddInt.h"

namespace KCBox {

class KCounter: public Extensive_Inprocessor
{
public:
	BigInt sum_count = 0;
	double Entropy = 0,time_counting = 0;
	double gather_time = 0,IBCP_time = 0,picktime = 0,centtime = 0;
	double minfill_time = 0,Full_IBCP_time = 0,Init_time = 0;
	double X_pick_time = 0,dynamic_time = 0,XCache_hit_time = 0,YCache_hit_time = 0;
	StopWatch START;
	long long counting_time = 0,count_modelzero = 0,cache_hit = 0,cacheX_hit = 0;
	long long cache_node_hit = 0;
	long long Clear_times = 0; 
	vector<unsigned>rd_zero;

protected:
	BigInt * Counting_stack; // thl 记录组件的模型数
	double * Entropy_stack; // thl 记录组件的entropy cache


	BigInt * _rsl_stack;  // rsl denotes result
	unsigned * _aux_rsl_stack;  // record the auxiliary information for results
	unsigned _num_rsl_stack;  // recording the number of temporary results
	unsigned old_entropy_num_levels; // thl use for cache clear 
	Incremental_Component_Cache_BigInt _component_cache;
	Component _incremental_comp;
	vector<Literal> _equivalent_lit_pairs;
public:
	KCounter();
	~KCounter();
	void Reset();
	size_t Memory();
	void Set_Max_Var( Variable max_var ) { Allocate_and_Init_Auxiliary_Memory( max_var ); }
protected:
	void Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Free_Auxiliary_Memory(); 

protected:
	BigInt Backtrack_Init();
	void Choose_Running_Options( Heuristic heur );
	void Compute_Var_Order_Automatical();
	void Choose_Running_Options_Static( Heuristic heur );
	void Compute_Var_Order_Automatical_Static();
	void Choose_Implicate_Computing_Strategy();
	void Choose_Implicate_Computing_Strategy_Static();
	void Create_Init_Level();
	void Set_old_num_levels(unsigned num_levles) { // thl 记录counting前的决策等级
		old_entropy_num_levels = num_levles;
	}
	unsigned Get_old_num_levels() { // thl 获取counting前的决策等级
		return old_entropy_num_levels;
	}
	void Component_Cache_Add_Original_Clauses();
protected:
	void Count_With_Implicite_BCP(); // thl update add backjump_to y
	void Backjump_Decision( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decision
	void Backtrack_Known( BigInt cached_result ); 
	void Component_Cache_Erase( Component & comp );  // thl add old_num_levels
	void Backtrack_True();
	void Generate_Incremental_Component( Component & comp );
	void Generate_Incremental_Component_Old( Component & comp );
	bool Cache_Clear_Applicable();
	BigInt Component_Cache_Map( Component & comp ); // thl updates old_num_levels 清cache要用
	void Component_Cache_Clear(); // thl add old_num_levels
	void Backtrack();  // backtrack one level without discarding results
	void Extend_New_Level();
	void Backtrack_Decision();
	void Backjump_Decomposition( unsigned num_kept_levels );  // backtrack when detect some unsatisfiable component, and tail is decomposition
	// thl add old_num_levels
	void Iterate_Known( BigInt cached_result );
	void Backtrack_Decomposition2Decision();
	void Iterate_Decision();
	void Backtrack_Decomposition();
protected:
	void Verify_Result_Component( Component & comp, BigInt count );
	void Display_Statistics( unsigned option );
	void Display_Result_Stack( ostream & out );
	void Display_Memory_Status( ostream & out );
protected:
	void Count_With_SAT_Imp_Computing();  // employ SAT engine to compute implied literals
	bool Try_Shift_To_Implicite_BCP();
	bool Estimate_Hardness( Component & comp );
	lbool Try_Final_Kernelization();  // return whether solved by this function
	bool Estimate_Final_Kernelization_Effect();
	void Leave_Tmp_Kernelization();
	void Leave_Final_Kernelization();
	void Compute_Second_Var_Order_Automatical( Component & comp );
	lbool Try_Kernelization();  // return whether solved by this function
	bool Estimate_Kernelization_Effect();
	void Sort_Clauses_For_Caching();
	void Sort_Long_Clauses_By_IDs();
	void Encode_Long_Clauses();
	void Leave_Kernelization();
	void Calculate_Decision();
	void Backtrack_Decision_Imp();
	void Iterate_Decision_Next();
public:
	BigInt Count_Models( CNF_Formula & cnf, vector<Model *> & models);
	BigInt Count_Models( CNF_Formula & cnf, vector<Model *> & models, double timeout );
	BigInt Count_Models( CNF_Formula & cnf, Heuristic heur = AutomaticalHeur);

protected:
	void Count_With_Implicite_BCP( double timeout );
	void Terminate_Counting();
	void Count_With_SAT_Imp_Computing( double timeout );  // employ SAT engine to compute implied literals
	bool Try_Shift_To_Implicite_BCP( double timeout );
	BigInt Backtrack_Failure();
	bool Is_Memory_Exhausted();
public:
	static void Debug() { Debug_File(); }
	static void Debug_Rand()
	{
		Random_Generator rand_gen;
		KCounter counter;
		counter.debug_options.verify_count = true;
		counter.debug_options.verify_component_count = false;
		for ( unsigned i = 0; i < 100; i++ ) {
			rand_gen.Reset( i );
			cout << "========== " << i << " ==========" << endl;
			unsigned nv = 20, nc = 40;
			CNF_Formula cnf( rand_gen, nv, nc, 3, 3 );
			cnf.Sort_Clauses();
			cout << cnf;
			counter.Count_Models( cnf, AutomaticalHeur );
//			ofstream fout( "result.cdd" );
//			manager.Display( fout );
//			fout.close();
//			system( "./pause" );
		}
	}
	static void Debug_File()
	{
		KCounter counter;
		counter.debug_options.verify_count = true;
		counter.running_options.max_kdepth = 2;
		ifstream fin( "../benchmarks/kc-domain-benchmarks-BE/misc_07A-3.cnf.gz.no_w.cnf" );
//		ifstream fin( "../benchmarks/Benchmarks-Shubham-BE/log2.sk_72_391.cnf.gz.no_w.cnf.cnf" );
		CNF_Formula cnf( fin );
		fin.close();
		counter.Count_Models( cnf, AutomaticalHeur );
	}
	static void Test( const char * infile, Counter_Parameters parameters, bool quiet )
	{
		KCounter counter;
		counter.debug_options.verify_count = false;
		counter.debug_options.verify_component_count = false;
		counter.running_options.detect_AND_gates = false;
		counter.running_options.static_heur = parameters.static_heur;
		counter.running_options.phase_selecting = false;
		counter.running_options.max_kdepth = parameters.kdepth;
		counter.running_options.mixed_imp_computing = true;
		counter.running_options.trivial_variable_bound = 128;
		counter.running_options.display_kernelizing_process = false;
		counter.running_options.max_memory = parameters.memo;
		Heuristic heur = Parse_Heuristic( parameters.heur );
		if ( quiet ) {
			counter.running_options.profile_solving = Profiling_Close;
			counter.running_options.profile_preprocessing = Profiling_Close;
			counter.running_options.profile_counting = Profiling_Close;
		}
		if ( parameters.competition ) counter.running_options.display_prefix = "c o ";
		ifstream fin( infile );
		CNF_Formula cnf( fin );
		fin.close();
		BigInt count = 1;
		double Entropy_Count;
		if ( cnf.Max_Var() == Variable::undef ) {
			count = cnf.Known_Count();
			if ( count != 0 ) cout << "s SATISFIABLE" << endl;
			else cout << "s UNSATISFIABLE" << endl;
		}
		else {
			count = counter.Count_Models( cnf, heur );
			//Entropy_Count = counter.Count_Entropy( cnf , heur );
		}
		//cout << counter.running_options.display_prefix << "Number of models: " << count << endl;
		
		if ( parameters.competition ) {  // for model counting competition
			cout << "c s type mc" << endl;
			cout << "c o The solver log10-estimates a solution of " << count << endl;
			long exp;
			double num = count.TransformDouble_2exp( exp );
			cout << "c s log10-estimate " << log10( num ) + exp * log10(2) << endl;
			cout << "c o Arbitrary precision result is " << count << endl;
			cout << "c s exact arb int " << count << endl;
		}
		//cout<<"Final Entropy is "<< Entropy_Count<< endl;
		//printf("%.2f\n",Entropy_Count);
	}
};


}


#endif  // _Compiler_h_
