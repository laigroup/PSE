#include "../Component_Types/Incremental_Component.h"
#include "../Component_Types/Incremental_Component_BigInt.h"
#include "../Extensive_Inprocessor.h"
#include "KCounter.h"
#include <map>

#include "../Compilers/Integrated_Compiler.h"
#include "../KC_Languages/OBDD[AND].h"

namespace KCBox {



class ECounter: public KCounter 
{
protected:
	// BigInt * Counting_stack; // thl 记录组件的模型数
	// double * Entropy_stack; // thl 记录组件的entropy cache
    unsigned _num_entropy_stack; // thl 记录中间组件答案的数量
	int * vis; // thl 记录遍历的过程中的点是否出现
    unsigned old_num_levels; // thl use for cache clear 
    Component_Cache<double> Entropy_Cache; // thl Y部分的决策的子公式缓存Entropy
	Component_Cache<BigInt> Counting_Cache; // thl Y部分的决策的子公式缓存Counting
	unsigned * _active_all_comps;
	unsigned * _aux_counting_stack;

public:
	ECounter();
	~ECounter();
protected:
	void Entropy_Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Entropy_Free_Auxiliary_Memory(); 
public: // thl
	BigInt Entropy_Count_Models( unsigned old_num_dec = 1); // thl
	BigInt Baseline_Search( Diagram & bddc,  OBDDC_Manager &manager, CNF_Formula & cnf, const vector<unsigned>& Ylist, int pos ,BigInt total_count, Heuristic heur = AutomaticalHeur ); // thl
	Variable Pick_Var_From_topo( Component & comp, int op);
	BigInt Count_Entropy_With_ADD( Diagram & bddc ,  OBDDC_Manager & BDDC_manager , CNF_Formula & cnf, const vector<unsigned>& Ylist,BigInt total_count, Heuristic heur = AutomaticalHeur ); // thl 纯ADD
	BigInt Count_Entropy_SAT_Imp_Computing( CNF_Formula & cnf, const vector<unsigned>& Ylist,BigInt total_count, Heuristic heur = AutomaticalHeur ); // thl
	BigInt Count_Entropy_With_Implicite_BCP( CNF_Formula & cnf, const vector<unsigned>& Ylist,BigInt total_count, Heuristic heur = AutomaticalHeur ); // thl
	void Count_Entropy_With_ADDC( Diagram & bddc ,  OBDDC_Manager & BDDC_manager , CNF_Formula & cnf, const vector<unsigned>& Ylist,BigInt total_count, Heuristic heur = AutomaticalHeur ); // thl
	double Count_Entropy( const char * infile, CNF_Formula & cnf,  Heuristic heur = AutomaticalHeur ); // thl
	void Compile_ADDL_With_Rotate( CNF_Formula & cnf,  Heuristic heur = AutomaticalHeur );
	void Search_Test( CNF_Formula & cnf ); // thl
	void Dfs_Test(int u); // thl 
	void test_addIte(); // thl
	bool Check_Circuit_Formula( CNF_Formula & cnf );
	void Iterate_Known(double entropy_cached,BigInt cached_result);
	void Backtrack_Decomposition2Decision();
	void Entropy_Component_Cache_Erase( Component & comp );

	Component & Current_Allvar_Component() { // thl
		assert(_num_levels - 1 >= 0);
		return Allvar_Compstack[_active_all_comps[_num_levels - 1]]; 
	}
	Component & Parent_of_Current_Allvar_Component() {  // thl
		return Allvar_Compstack[_active_all_comps[_num_levels - 2]]; 
	}
	
	unsigned Num_Components_On_Current_Level() const { return _num_all_stack - comp_id[_num_levels - 1]; }
	unsigned Num_Components_On_Level( unsigned level ) const { comp_id[_num_levels] = _num_all_stack;  return comp_id[level + 1] - comp_id[level]; }
	bool Is_Current_Level_Empty() const { return _num_all_stack == comp_id[_num_levels - 1]; }
	bool Is_Current_Level_Decision() const { return _num_all_stack == comp_id[_num_levels - 1] + 1; }
	bool Is_Current_Level_Decomposition() const { return _num_all_stack > comp_id[_num_levels - 1] + 1; }
	bool Is_Current_Level_Active() const { return _active_all_comps[_num_levels - 1] < _num_all_stack; }
	bool Is_Level_Decision( unsigned level ) const { comp_id[_num_levels] = _num_all_stack;  return comp_id[level + 1] == comp_id[level] + 1; }
	void Iterate_Decision();
	void Entropy_Backtrack_Decomposition();
	void Backtrack_True();

protected: // thl

	BigInt Entropy_Backtrack_Init(unsigned old_num_dec,unsigned Init); 
	void Create_Init_Component(); // thl
	unsigned Create_Component_Init_Level(Component & all_comp); // thl
	unsigned Create_Component_Init_Level_Pre(); // thl
	void ComponentCache_Add_Original_Clauses(); // thl
	//void Count_With_Implicite_BCP( int &backjump_toY ); // thl update add backjump_to y
	void Entropy_Backjump_Decision( unsigned num_kept_levels); // thl
	void Backtrack_Known_Entropy( double entropy_cached , BigInt Counting_result); // thl
	double Component_Cache_Entropy_Map( Component & comp ); // thl Entropy部分
	BigInt Component_Cache_Counting_Map( Component & comp ); // thl counting部分
	bool Counting_Cache_Clear_Applicable(); // thl  Counting_Cache
	bool Entropy_Cache_Clear_Applicable(); // thl Entropy_Cache
	void Counting_Component_Cache_Clear(); // thl to clear Counting_Cache
	void Entropy_Component_Cache_Clear(); // thl to clear Entropy_Cache
	void print_result(BigInt total_count,double tim); // 打印输出结果
	void Entropy_Backtrack(); // thl 
	void Entropy_Extend_New_Level(); // THL 
	void Entropy_Backtrack_Decision();
	void Entropy_Backjump_Decomposition( unsigned num_kept_levels ); 
	void Entropy_Counting( Diagram & bddc , OBDDC_Manager & manager, CNF_Formula & cnf, BigInt total_count , Heuristic heur = AutomaticalHeur); // thl
/*       Above is ECounter*/
// ----------------------------------- Follow is Compiler


protected:
	NodeID * ADDL_stack; // denotes result 记录ADDL的节点栈
	Component_Cache<NodeID> ADDL_cache; // 
	unsigned _num_addl_stack; 
	Rough_ADD_Node ADDL_rnode;  
	unsigned _remove_redundancy_trigger;  

protected:
	void Compiler_Allocate_and_Init_Auxiliary_Memory( Variable max_var );
	void Compiler_Free_Auxiliary_Memory();

public: 
	void print_heur();
	void ADDL_Cache_Clear();
	void Init_ADDL_Cache( Variable max_var , unsigned Old_num_long_clauses , Component & comp) {
		assert( ADDL_cache.Size() == 0 );
		ADDL_cache.Init( max_var, Old_num_long_clauses, NodeID::undef );
		ADDL_cache.Hit_Component( comp  );
	}
	NodeID Component_Cache_Node_Map( Component & comp );



/* Above is ADDL-Compiler*/

	public:
		void Compile_OBDDC( OBDDC_Manager & manager, CNF_Formula & cnf, Heuristic heur, Chain & vorder );
		void Baseline_OBDDC(CNF_Formula & cnf, Heuristic heur,BigInt total_count);
		BigInt Count_With_OBDDC( const Diagram & bddc, OBDDC_Manager & manager, CNF_Formula & cnf, BigInt total_count, Heuristic heur = AutomaticalHeur ); // thl OBDDC
		void BDDC_Counting( const Diagram & bddc, CNF_Formula & cnf, OBDDC_Manager & manager , BigInt total_count , Heuristic heur = AutomaticalHeur); // thl
/* Above is Baseline */

public:
	static void Parse_Method(ECounter &counter, PSE parameters) {
		if (strcmp(parameters.XCache,"false") == 0) counter.running_options.XCache = 0;
		if (strcmp(parameters.YCache,"false") == 0) counter.running_options.YCache = 0;
		if (strcmp(parameters.Pre,"false") == 0) counter.running_options.Pre = 0;
		if (strcmp(parameters.ConjunctiveDecomposition,"false") == 0) counter.running_options.ConjunctiveDecomposition = 0;
		counter.running_options.Counting = parameters.Counting;
	}
    static void Test( const char * infile, PSE parameters, bool quiet )
	{
		ECounter counter;
		counter.running_options.Time_limit = 3000;
		counter.debug_options.verify_count = false;
		counter.debug_options.verify_component_count = false;
		counter.running_options.detect_AND_gates = false;
		//counter.running_options.static_heur = parameters.static_heur;
		counter.running_options.phase_selecting = false;
		//counter.running_options.max_kdepth = parameters.kdepth;
		counter.running_options.mixed_imp_computing = true;
		counter.running_options.trivial_variable_bound = 128;
		counter.running_options.display_kernelizing_process = false;
		//counter.running_options.max_memory = parameters.memo;
		Heuristic heur = Parse_Heuristic( parameters.heur );
		Parse_Method(counter,parameters);
		if ( quiet ) {
			counter.running_options.profile_solving = Profiling_Close;
			counter.running_options.profile_preprocessing = Profiling_Close;
			counter.running_options.profile_counting = Profiling_Close;
		}
		//if ( parameters.competition ) counter.running_options.display_prefix = "c o ";
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
			Entropy_Count = counter.Count_Entropy( infile, cnf , heur );
		}
		//OBDDC_Compiler( infile, parameters, quiet );
		//cout<<"Final Entropy is "<< Entropy_Count<< endl;
		//printf("%.2f\n",Entropy_Count);
	}
};
}