#include "KCounter.h"
#include "ECounter.h"
#include <sstream>
#include <sys/sysinfo.h>
#include "../KC_Languages/DecDNNF.h"

#include "../Compilers/Integrated_Compiler.h"
#include "../KC_Languages/OBDD[AND].h"

namespace KCBox {
using namespace std;

ECounter::ECounter():
_num_entropy_stack( 0 )
{
}

ECounter::~ECounter()
{
	Entropy_Free_Auxiliary_Memory();
}

/* Follow is Compiler */


/* Above is Compiler */
void ECounter::Entropy_Allocate_and_Init_Auxiliary_Memory( Variable max_var )  // ToDo: whether can we optimize when max_var < _max_var
{
	//if ( _max_var != Variable::undef ) Entropy_Free_Auxiliary_Memory();
    
	//Counting_stack = new BigInt [2 * max_var + 2]; // thl
	//Entropy_stack = new double [2 * max_var + 2]; // thl

	_active_all_comps = new unsigned [2 * max_var + 2];
	_aux_counting_stack = new unsigned [2 * max_var + 2];
}
void ECounter::Entropy_Free_Auxiliary_Memory()
{
	// if ( _max_var == Variable::undef ) return;
	// delete [] Counting_stack; // thl
	// delete [] Entropy_stack; // thl
	//KCounter::Free_Auxiliary_Memory();
	delete[] _active_all_comps;
	delete[] _aux_counting_stack;
}
void ECounter::print_heur() {
	Heuristic heur = running_options.var_ordering_heur;
	switch ( running_options.var_ordering_heur ) {
	case AutomaticalHeur:
		cout<<"AutomaticalHeur,";
		break;
	case minfill:
		cout<<"minfill,";
		break;
	case LinearLRW:
		cout<<"LinearLRW,";
		break;
	case LexicographicOrder:
		cout<<"LexicographicOrder,";
		break;
	case VSADS:
		cout<<"VSADS,";
		break;
	case DLCS:
		cout<<"DLCS,";
		break;
	case DLCP:
		cout<<"DLCP,";
		break;
	case dynamic_minfill:
		cout<<"dynamic_minfill,";
		break;
	}
}
bool ECounter::Check_Circuit_Formula( CNF_Formula & cnf ) {
	vector<unsigned>Ylist = cnf.Get_Ylist();
	for (auto it = cnf.Clause_Begin() ; it != cnf.Clause_End() ; it ++) {
		Clause cls = *it;
	}
	vector< vector<int> > clause_tmp;
	vector< int > tmp , tmp2 ;
	clause_tmp.clear();
	unsigned mxvar = cnf.Max_Var();
	int * appered = new int [mxvar + 5];
	memset(appered,0,sizeof(appered));
	for (auto it = cnf.Clause_Begin() ; it != cnf.Clause_End() ; it ++) {
		Clause cls = *it;
		tmp.clear();
		tmp2.clear();
		for (int i = 0 ; i < cls.Size() ; i ++) {
			Literal lit = cls[i];
			appered[lit.Var()] ++;
			int sign = 1;
			if (!lit.Sign()) sign = -1;
			int litvar = lit.Var() * sign;
			tmp.push_back(litvar);
			int var = lit.Var() + mxvar;
			tmp2.push_back(var * sign);
		}
		clause_tmp.push_back(tmp);
		clause_tmp.push_back(tmp2);
	}
	vector< vector<int> > Cluase_test = clause_tmp;
	vector<int> cls_tmp;
	for (int i = 1 ; i <= mxvar ; i ++) { // 在X中 x_i = y_i
		if (belong_XORY[i]) continue;
		if (!appered[i]) continue; // 没出现的变量不进行建模
		int var_a = i;
		int var_b = i + mxvar;
		cls_tmp.clear();
		cls_tmp.push_back(var_a * -1);
		cls_tmp.push_back(var_b);
		Cluase_test.push_back(cls_tmp);

		cls_tmp.clear();
		cls_tmp.push_back(var_a);
		cls_tmp.push_back(var_b * -1);
		Cluase_test.push_back(cls_tmp);
	}
	unsigned tmp_num = 2 * mxvar;
	for (int i = 1 ; i <= mxvar ; i ++) { // !(x_i = y_i) 
		if (!appered[i]) continue; // 没出现的变量不进行建模
		int var_a = i;
		int var_b = i + mxvar;
		int var_tmp = i + tmp_num;
		cls_tmp.clear();
		cls_tmp.push_back(var_a * -1);
		cls_tmp.push_back(var_b * -1);
		cls_tmp.push_back(var_tmp);
		Cluase_test.push_back(cls_tmp);

		cls_tmp.clear();
		cls_tmp.push_back(var_a);
		cls_tmp.push_back(var_b);
		cls_tmp.push_back(var_tmp);
		Cluase_test.push_back(cls_tmp);
	}
	cls_tmp.clear();
	for (int i = 1 ; i <= mxvar ; i ++) {
		if (!appered[i]) continue; // 没出现的变量不进行
		int var_tmp = (i + tmp_num) * -1;
		cls_tmp.push_back(var_tmp);
	}
	Cluase_test.push_back(cls_tmp);
	vector<Model *> premodel;
	bool Test_sat = Solve_SAT( premodel , Cluase_test);
	return Test_sat;
}
BigInt TT = 0;
int res = 0;
int unit_ = 0;
double baseline_entropy = 0;
BigInt ECounter::Baseline_Search( Diagram & bddc, OBDDC_Manager &manager, CNF_Formula & cnf, const vector<unsigned>& Ylist, int pos ,BigInt total_count, Heuristic heur) { // thl
	if (!pos) {
		//total_count = Count_Models(cnf,heur);
		//bddc = BDDC_compiler.Compile( manager, cnf, heur );
	}	
	

	unsigned old_num_dec = _num_dec_stack;

	unsigned backjump_level;
	Reason backjump_reason;
	// if (pos % 10 == 0) backjump_reason = Get_Approx_Imp(backjump_level);
	// else 
	for (int i = 1 ; i <= 30 ; i ++) {
		backjump_reason = BCP(1);
		Un_BCP(old_num_dec);
	}

	if (pos >= Ylist.size()) {
		res ++;
		Reason conf = BCP( 1 ); // _num_dec_stack - 1
		if (conf != Reason::undef) {
			Un_BCP(old_num_dec);
			return 0;
		}
		vector<Literal> assign;
		for (int i = 0 ; i < _num_dec_stack ; i ++) {
			assign.push_back(_dec_stack[i]);
		}
		// condition to do
		//num_models = -res;
		BigInt num_models = manager.Count_Models(bddc,assign);
		//BigInt num_models = Entropy_Count_Models(_num_dec_stack);
		double m1 = num_models.TransformDouble();
		double m2 = total_count.TransformDouble();
		if (m1 != 0 && m2 != 0) baseline_entropy -= (m1 / m2) * log2(m1 / m2);
		Un_BCP(old_num_dec);
		TT += num_models;
		return 0;
	}
	Variable var = Variable(Ylist[pos]);
	BigInt res1,res2;
	if (Var_Decided(var)) {
		unit_ ++;
		res1 = Baseline_Search(bddc,manager,cnf,Ylist,pos + 1,total_count,heur);
	}
	else {
		if (Var_Undecided(var)) Assign(Literal(var,true));
		
		//Reason conf = BCP( 1 ); // _num_dec_stack - 1
		
		res1 = Baseline_Search(bddc,manager,cnf,Ylist,pos + 1,total_count,heur);
		
		Un_BCP(old_num_dec);

		if (Var_Undecided(var)) Assign(Literal(var,false));
		//conf = BCP( 1 ); // _num_dec_stack - 1
		res2 = Baseline_Search(bddc,manager,cnf,Ylist,pos + 1,total_count,heur);
		Un_BCP(old_num_dec);
	}
	if (!pos) {
		double tim = START.Get_Elapsed_Seconds();
		cout<<baseline_entropy<<","<<tim<<endl;
		//assert(TT == total_count);
	}
	return res1;
}

BigInt ECounter::Count_Entropy_With_ADD( Diagram & bddc ,  OBDDC_Manager & BDDC_manager , CNF_Formula & cnf, const vector<unsigned>& Ylist , BigInt total_count,Heuristic heur ) {
	Create_Init_Component();
	unsigned old_num_levels = _num_levels;
	unsigned old_num_rsl_stack = _num_rsl_stack;
	Variable var;
	double cached_result;
	BigInt Counting_result = 0;
	NodeID Cached_Node;
	Reason backjump_reason = Reason::undef;  // just used for omitting warning
	unsigned backjump_level;
	bool flag;
	int loop_count = 0;
	int tt = 0;
	int op = 0;
	int delta = 0,prenum;
	int pre_num_dec_stack;
	int first_num_dec_stack = _num_dec_stack;
	Heuristic pre_heur = running_options.var_ordering_heur;
	BigInt num_models;
	//int _num_stack = Dynamic_Decompose_Component( Parent_of_Current_Allvar_Component(), _comp_stack + comp_id[_num_levels - 1] );
	while ( _num_levels >= old_num_levels ) {
		StopWatch tmp;
		loop_count ++;
		double tim;
		switch ( _state_stack[_num_levels - 1] ) {	 // decision or preparation 	逐一尝试 false true
		case 0: // 蕴含文字
			tim = START.Get_Elapsed_Seconds();
			if (tim > running_options.Time_limit) {
				cout<<"Time limit excceed ,";
				print_result(total_count,tim);
				exit(0);
			}
			//backjump_reason = Get_Approx_Imp( backjump_level );
			pre_num_dec_stack = _num_dec_stack;
			backjump_reason = BCP(first_num_dec_stack); //Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component() ,backjump_level);
			//Un_BCP(pre_num_dec_stack);
			if ( backjump_reason != Reason::undef ) {
				//Entropy_Backjump_Decision( backjump_level , 0);
				_num_levels--;
				_num_all_stack = comp_id[_num_levels];
				//Un_BCP( _dec_offsets[_num_levels] );	
				
				Counting_stack[_num_entropy_stack] = 0;
				Entropy_stack[_num_entropy_stack ++] = 0;
				break;
			}
			//Un_BCP(pre_num_dec_stack);
			flag = true;
			for (int i = 0 ; i < Ylist.size() ; i ++) {
				Variable var = Variable(Ylist[i]);
				if (Var_Undecided(var)) flag = false;
			}
			//if (!flag) Un_BCP(pre_num_dec_stack);
			GetYlist_NextComponent( Parent_of_Ylist_Component() , Ylist_Compstack[_num_all_stack] );
			flag = false;
			if (Current_Ylist_Component().Vars_Size() == 0) flag = true;
			// if (flag) {
			// 	//pre_num_dec_stack = _num_dec_stack;
			// 	backjump_reason = BCP(first_num_dec_stack);
			// 	//backjump_reason = Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component() ,backjump_level);
			// 	if ( backjump_reason != Reason::undef ) {
			// 		//backjump_times ++;
			// 		//Entropy_Backjump_Decision( backjump_level , 0);
			// 		_num_levels--;
			// 		_num_all_stack = comp_id[_num_levels];
			// 		Un_BCP( _dec_offsets[_num_levels] );	
			// 		Counting_stack[_num_entropy_stack] = 0;
			// 		Entropy_stack[_num_entropy_stack ++] = 0;
			// 		break;
			// 	}
			// 	//GetAllvar_NextComponent( Parent_of_Current_Allvar_Component() , Allvar_Compstack[_num_all_stack ++] );
			// }
			GetAllvar_NextComponent( Parent_of_Current_Allvar_Component() , Allvar_Compstack[_num_all_stack ++] );
			assert(Allvar_Compstack[_num_all_stack - 1] == Current_Allvar_Component());
			Counting_result = -1;
			cached_result = 99999;
			Cached_Node = NodeID::undef;
			if (Current_Allvar_Component().Vars_Size() >= 2) {
				tmp.Start();
				//cached_result = Component_Cache_Entropy_Map( Current_Allvar_Component());
				//Counting_result = Component_Cache_Counting_Map( Current_Allvar_Component() )
				//YCache_hit_time += tmp.Get_Elapsed_Seconds();
			}
			if (Cached_Node != NodeID::undef ) {  /// NOTE: backjump makes that there exists cacheable component with undef result
				//Add_Node_With_Imp( Cached_Node , -1);
				//cache_node_hit ++;
			}
			if (cached_result < 999) {
				//num_models = Entropy_Count_Models(_num_dec_stack);
				Backtrack_Known_Entropy( cached_result , Counting_result);	
				//assert(num_models == Counting_result);
			}
			else if (flag) {
				//BCP(first_num_dec_stack);
				Entropy_Counting(bddc,BDDC_manager,cnf,total_count,heur);
				//Un_BCP( pre_num_dec_stack );
			}
			else _state_stack[_num_levels - 1]++;
			break;
		case 1:
			_state_stack[_num_levels - 1]++; 
			tmp.Start();
			var = Pick_Good_Var_Component(Current_Ylist_Component()); // precode
			Entropy_Extend_New_Level();
			Assign( Literal( var, false ) );
			break;
		case 2:
			if (Counting_stack[_num_entropy_stack - 1] != 0) {
				_state_stack[_num_levels - 1]++;
				Entropy_Extend_New_Level();
				Assign( ~_dec_stack[_num_dec_stack] );
			}
			else {
				_num_entropy_stack --;
				_num_all_stack = comp_id[_num_levels - 1];
				_state_stack[_num_levels - 1] = 0;
				Assign( ~_dec_stack[_num_dec_stack], backjump_reason );
			}
			break;
		case 3:
			Entropy_Backtrack_Decision();
			break;
		}
	}
	Entropy = Entropy_stack[_num_entropy_stack - 1];
	sum_count = Counting_stack[_num_entropy_stack - 1];
	assert( _num_levels == 1 );
	return 1;

	
/*
	Create_Init_Component();
	Compiler BDDC_compiler;
	OBDDC_Manager BDDC_manager( cnf.Max_Var() );
	Diagram bddc;
	unsigned old_num_levels = _num_levels;
	unsigned old_num_rsl_stack = _num_rsl_stack;
	Variable var;
	BigInt cached_result;
	double entropy_cached = 0;
	Reason backjump_reason = Reason::undef;  // just used for omitting warning
	unsigned backjump_level;
	Component Current_compoent = Current_Allvar_Component(); // thl toremove
	StopWatch tmp;
	double tim;
	unsigned pre_num_dec_stack;
	unsigned first_num_dec_stack = _num_dec_stack;
	while ( _num_levels >= old_num_levels ) {
		if ( DEBUG_OFF ) {
			if ( Num_Components_On_Current_Level() <= 1 && _state_stack[_num_levels - 1] == 0 )
				Display_Component( Parent_of_Current_Allvar_Component(), cerr );  // ToRemove
			else Display_Component( Current_Allvar_Component(), cerr );  // ToRemove
			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	//		system( "pause" );
//			Display_Comp_And_Decision_Stacks( cerr );  // ToRemove
		}
		bool flag = true;
		vector<Literal>vec;
		pre_num_dec_stack = _num_dec_stack;
		if ( Num_Components_On_Current_Level() <= 1 ) { // decision or preparation 	逐一尝试 false true
			unsigned  dynamic_num; // thl toremove
			switch ( _state_stack[_num_levels - 1] ) {
			case 0: // 蕴含文字
				backjump_reason = BCP(first_num_dec_stack); // Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component(), backjump_level );
				if ( backjump_reason != Reason::undef ) {
					//Entropy_Backjump_Decision( backjump_level );
					_num_levels--;
					_num_all_stack = comp_id[_num_levels];
					Un_BCP( _dec_offsets[_num_levels] );	
					Counting_stack[_num_entropy_stack] = 0;
					Entropy_stack[_num_entropy_stack ++] = 0;
					break;
				}
				//Un_BCP( pre_num_dec_stack );
				assert(_active_all_comps[_num_levels - 2] <= _active_all_comps[_num_levels - 1]); 
				_num_all_stack += Dynamic_Decompose_Component( Parent_of_Current_Allvar_Component(), Allvar_Compstack + comp_id[_num_levels - 1] );
				if ( Is_Current_Level_Empty() ) {
					//backjump_reason = BCP(first_num_dec_stack); //Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component(), backjump_level );
					
					// for (int i = 0 ; i < vec.size() ; i ++) {
					// 	_dec_stack[_num_dec_stack ++] = vec[i];
					// }
					//Entropy_Counting(bddc,BDDC_manager,cnf,total_count,heur);
					// backjump_reason = BCP(first_num_dec_stack); //Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component(), backjump_level );
					// if ( backjump_reason != Reason::undef ) {
					// 	Entropy_Backjump_Decision( _num_levels - 1 );
					// 	// _num_levels--;
					// 	// _num_all_stack = comp_id[_num_levels];
					// 	// Un_BCP( _dec_offsets[_num_levels] );	
					// 	// Counting_stack[_num_entropy_stack] = 0;
					// 	// Entropy_stack[_num_entropy_stack ++] = 0;
					// 	break;
					// }
					Backtrack_True();
					//Un_BCP( pre_num_dec_stack );
				}
				else if ( Is_Current_Level_Decision() ) {
					entropy_cached = Component_Cache_Entropy_Map( Current_Allvar_Component() );
					cached_result = Component_Cache_Counting_Map( Current_Allvar_Component() );
					if ( cached_result != -1 ) {  /// NOTE: backjump makes that there exists cacheable component with undef result
						Backtrack_Known_Entropy( entropy_cached, cached_result );
					}
					else {
						for (auto i = Current_Allvar_Component().VarIDs_Begin() ; i != Current_Allvar_Component().VarIDs_End(); i ++) {
							unsigned var = *i;
							if (belong_XORY[var]) {
								flag = false;
								break;
							}
						}
						// if (flag) {
						// 	//BCP(first_num_dec_stack);
						// 	Entropy_Counting(cnf,total_count,heur);
						// }
						// else 
						_state_stack[_num_levels - 1]++;
					}
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				_state_stack[_num_levels - 1]++; 
				var = Pick_Good_Var_Component( Current_Allvar_Component() );
				Entropy_Extend_New_Level();
				Assign( Literal( var, false ) );
				break;
			case 2:
				if ( Counting_stack[_num_entropy_stack - 1] != 0 ) {
					_state_stack[_num_levels - 1]++;
					Entropy_Extend_New_Level();
					Assign( ~_dec_stack[_num_dec_stack] );
				}
				else {
					_num_entropy_stack--;  // pop 0
					_num_all_stack = comp_id[_num_levels - 1];  // re-decompose
					_state_stack[_num_levels - 1] = 0;
					Assign( ~_dec_stack[_num_dec_stack], backjump_reason );  // reason is assigned in the last iteration
				}
				break;
			case 3:
				Entropy_Backtrack_Decision();
				break;
			}
		}
		else { // decomposition 多个组件
			assert( _active_all_comps[_num_levels - 1] == comp_id[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					entropy_cached = Component_Cache_Entropy_Map( Current_Allvar_Component() );
					cached_result = Component_Cache_Counting_Map( Current_Allvar_Component() );
					if ( cached_result != -1 ) {  /// NOTE: backjump makes that there are unknown cacheable component
						Iterate_Known( entropy_cached, cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						var = Pick_Good_Var_Component( Current_Allvar_Component() );
						Entropy_Extend_New_Level();
						Assign( Literal( var, false ) );
					}
					break;
				case 1:
					if ( Counting_stack[_num_entropy_stack - 1] != 0 ) {
						Entropy_Extend_New_Level();
						Assign( ~_dec_stack[_num_dec_stack] );
					}
					else {
						_num_entropy_stack--;  // pop 0
						Assign( ~_dec_stack[_num_dec_stack], backjump_reason );
				
						// backjump_reason = Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component(), backjump_level );
						// if ( backjump_reason != Reason::undef ) {
						
						// 	Entropy_Backjump_Decision( backjump_level );
						// 	// _num_levels--;
						// 	// _num_all_stack = comp_id[_num_levels];
						// 	// Un_BCP( _dec_offsets[_num_levels] );	
						// 	// Counting_stack[_num_entropy_stack] = 0;
						// 	// Entropy_stack[_num_entropy_stack ++] = 0;
						// 	break;
						// }
						// Un_BCP(pre_num_dec_stack);
						
						backjump_reason = BCP(first_num_dec_stack); // Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component(), backjump_level );
						
						if ( backjump_reason != Reason::undef ) {
	
							//Entropy_Backjump_Decision( backjump_level );
	
							_num_levels--;
							_num_all_stack = comp_id[_num_levels];
							Un_BCP( _dec_offsets[_num_levels] );	
							Counting_stack[_num_entropy_stack] = 0;
							Entropy_stack[_num_entropy_stack ++] = 0;
							break;
						}

						unsigned num_comp = Dynamic_Decompose_Component( Current_Allvar_Component(), Allvar_Compstack + _num_all_stack );
						_num_all_stack += num_comp - 1;  // Replace one component with its sub-components
						Current_Allvar_Component() = Allvar_Compstack[_num_all_stack];
						if ( Is_Current_Level_Decision() && !Is_Current_Level_Active() ) {	// all components except one collapsed into literals
							Backtrack_Decomposition2Decision();  // overwrite the result of the only one component
						}
						else if ( Is_Current_Level_Decision() ) {	// all components except one collapsed into literals, and this component is not handled yet
							assert( _active_all_comps[_num_levels - 1] == _num_all_stack - 1 );
							cached_result = Component_Cache_Counting_Map( Current_Allvar_Component());  /// NOTE: the current component was after the collapsed one
							entropy_cached = Component_Cache_Entropy_Map( Current_Allvar_Component() );
							if ( cached_result != -1 ) {  /// NOTE: backjump makes that there are unknown cacheable component
								Backtrack_Known_Entropy( entropy_cached, cached_result );
							}
							else _state_stack[_num_levels - 1] = 1;
						}
						else _state_stack[_num_levels - 1] -= 2;
					}
					break;
				case 2:
					Iterate_Decision();
					break;
				}
			}
			else {  // all components are already processed
				Entropy_Backtrack_Decomposition();
			}
		}
	}
	
	Entropy = Entropy_stack[_num_entropy_stack - 1];
	sum_count = Counting_stack[_num_entropy_stack - 1];
	return 0;
*/
}
int countTimes = 0;
void ECounter::Iterate_Decision()
{
	assert( _num_entropy_stack > 1 );
	assert( Counting_stack[_num_entropy_stack - 2] != 0 );  // backjump guarantees this
	bool incomplete = ( Counting_stack[_num_entropy_stack - 1] == 0 ); /// NOTE: conflict can come from the upper levels
	_num_entropy_stack--;
	unsigned omit = Current_Allvar_Component().Vars_Size() - _aux_counting_stack[_num_entropy_stack - 1] - 1;
	Counting_stack[_num_entropy_stack - 1].Mul_2exp( omit );
	double low_p = Counting_stack[_num_entropy_stack - 1].TransformDouble();
	omit = Current_Allvar_Component().Vars_Size() - _aux_counting_stack[_num_entropy_stack] - 1;
	Counting_stack[_num_entropy_stack].Mul_2exp( omit );
	double high_p = Counting_stack[_num_entropy_stack].TransformDouble();
	double entropy = 0;
	if (belong_XORY[_dec_stack[_dec_offsets[_num_levels]].Var()]) {
		double p = low_p + high_p;
		low_p = low_p / p;
		high_p = high_p / p;
		if (low_p != 0) entropy += low_p * Entropy_stack[_num_entropy_stack - 1] - low_p * log2(low_p);
		if (high_p != 0) entropy += high_p * Entropy_stack[_num_entropy_stack] - high_p * log2(high_p);
		//cout<<" entropy = "<<entropy<<endl;
	}
	Entropy_stack[_num_entropy_stack - 1] = entropy;

	Counting_stack[_num_entropy_stack - 1] += Counting_stack[_num_entropy_stack];
	_aux_counting_stack[_num_entropy_stack - 1] = Current_Allvar_Component().Vars_Size();
	if (debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Allvar_Component(), Counting_stack[_num_entropy_stack - 1] );
	}
	if (!incomplete) {
		if (running_options.YCache) {
			Entropy_Cache.Write_Result( Current_Allvar_Component().caching_loc, Entropy_stack[_num_entropy_stack - 1] );
			Counting_Cache.Write_Result( Current_Allvar_Component().caching_loc, Counting_stack[_num_entropy_stack - 1] );
		}
	}
	_active_all_comps[_num_levels - 1]++;
}
void ECounter::Entropy_Backtrack_Decomposition()
{
	_num_entropy_stack -= Num_Components_On_Current_Level();
	assert( _num_levels > 2 );  // not decompose the initial formula
	//cout<<Counting_stack[_num_entropy_stack]<<" "<<Counting_stack[_num_entropy_stack + 1]<<" ";
	Counting_stack[_num_entropy_stack] *= Counting_stack[_num_entropy_stack + 1];
	_aux_counting_stack[_num_entropy_stack] += _aux_counting_stack[_num_entropy_stack + 1];
	Entropy_stack[_num_entropy_stack] += Entropy_stack[_num_entropy_stack + 1];
	for ( unsigned i = 2; i < Num_Components_On_Current_Level(); i++ ) {
		Counting_stack[_num_entropy_stack] *= Counting_stack[_num_entropy_stack + i];
		_aux_counting_stack[_num_entropy_stack] += _aux_counting_stack[_num_entropy_stack + i];
		Entropy_stack[_num_entropy_stack] += Entropy_stack[_num_entropy_stack + i];
		//cout<<Counting_stack[_num_entropy_stack + i]<<" ";
	}
	//cout<<endl;
	_aux_counting_stack[_num_entropy_stack] += Num_Current_Imps();
	//cout<<"Num_Current_Imps() = "<<Num_Current_Imps()<<" _aux_counting_stack["<<_num_entropy_stack<<"]="<<_aux_counting_stack[_num_entropy_stack]<<endl;
	//cout<<" backtrack decomposition result = "<<Counting_stack[_num_entropy_stack]<<endl;
	_num_entropy_stack++;
	Entropy_Backtrack();
}
void ECounter::Backtrack_True()
{
	Entropy_stack[_num_entropy_stack] = 0;
	Counting_stack[_num_entropy_stack ++] = 1;
	//Counting_stack[_num_entropy_stack - 1].Mul_2exp(Parent_of_Current_Allvar_Component().Vars_Size() - Num_Current_Imps());
	_aux_counting_stack[_num_entropy_stack - 1] = Num_Current_Imps();
	Entropy_Backtrack();
}
void ECounter::Iterate_Known( double entropy_cached, BigInt cached_result )
{
	if ( debug_options.verify_component_count ) { // debug_options.verify_component_count
		Verify_Result_Component( Current_Allvar_Component(), cached_result );
	}
	Counting_stack[_num_entropy_stack ++] = cached_result;
	Entropy_stack[_num_entropy_stack - 1] = entropy_cached;
	_aux_counting_stack[_num_entropy_stack - 1] = Current_Allvar_Component().Vars_Size();
	_active_all_comps[_num_levels - 1]++;
}
void ECounter::Backtrack_Decomposition2Decision()
{
	_aux_counting_stack[_num_entropy_stack - 1] += Num_Current_Imps();  // overwrite the result of the only one component
	Entropy_Backtrack();
}
void ECounter::Count_Entropy_With_ADDC(Diagram & bddc ,  OBDDC_Manager & BDDC_manager, CNF_Formula & cnf, const vector<unsigned>& Ylist,BigInt total_count, Heuristic heur)
{
	//Gather_Infor_For_Counting();
	Create_Init_Component();
	unsigned old_num_levels = _num_levels;
	unsigned old_num_rsl_stack = _num_rsl_stack;
	Variable var;
	BigInt cached_result;
	double entropy_cached = 0;
	Reason backjump_reason = Reason::undef;  // just used for omitting warning
	unsigned backjump_level;
	Component Current_compoent = Current_Allvar_Component(); // thl toremove
	StopWatch tmp;
	double tim;
	while ( _num_levels >= old_num_levels ) {
		if ( DEBUG_OFF ) {
			if ( Num_Components_On_Current_Level() <= 1 && _state_stack[_num_levels - 1] == 0 )
				Display_Component( Parent_of_Current_Allvar_Component(), cerr );  // ToRemove
			else Display_Component( Current_Allvar_Component(), cerr );  // ToRemove
			Debug_Print_Visit_Number( cerr, __LINE__ );  // ToRemove
	//		system( "pause" );
//			Display_Comp_And_Decision_Stacks( cerr );  // ToRemove
		}
		bool flag = true;
		if ( Num_Components_On_Current_Level() <= 1 ) { // decision or preparation 	逐一尝试 false true
			switch ( _state_stack[_num_levels - 1] ) {
			case 0: // 蕴含文字
				backjump_reason = Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component(), backjump_level );
				if ( backjump_reason != Reason::undef ) {
					Entropy_Backjump_Decision( backjump_level);
					break;
				}
				assert(_active_all_comps[_num_levels - 2] <= _active_all_comps[_num_levels - 1]); 
				_num_all_stack += Dynamic_Decompose_Component( Parent_of_Current_Allvar_Component(), Allvar_Compstack + comp_id[_num_levels - 1] );
				if ( Is_Current_Level_Empty() ) {
					//Entropy_Counting(bddc,BDDC_manager,cnf,total_count,heur);
					Backtrack_True();
				}
				else if ( Is_Current_Level_Decision() ) {
					//if (Current_Allvar_Component().Vars_Size() >= 2) 
					entropy_cached = Component_Cache_Entropy_Map( Current_Allvar_Component() );
					cached_result = Component_Cache_Counting_Map( Current_Allvar_Component() );
					if ( cached_result != -1 ) {  /// NOTE: backjump makes that there exists cacheable component with undef result
						assert(entropy_cached != 999999);
						Backtrack_Known_Entropy( entropy_cached, cached_result );
					}
					else {
						for (auto i = Current_Allvar_Component().VarIDs_Begin() ; i != Current_Allvar_Component().VarIDs_End(); i ++) {
							unsigned var = *i;
							if (belong_XORY[var]) {
								flag = false;
								break;
							}
						}
						// if (flag) {
						// 	Entropy_Counting(bddc,BDDC_manager,cnf,total_count,heur);
						// }
						// else 
						_state_stack[_num_levels - 1]++;
					}
				}
				else _state_stack[_num_levels - 1] = 0;
				break;
			case 1:
				_state_stack[_num_levels - 1]++; 
				var = Pick_Good_Var_Component( Current_Allvar_Component() );
				Entropy_Extend_New_Level();
				Assign( Literal( var, false ) );
				break;
			case 2:
				if ( Counting_stack[_num_entropy_stack - 1] != 0 ) {
					_state_stack[_num_levels - 1]++;
					Entropy_Extend_New_Level();
					Assign( ~_dec_stack[_num_dec_stack] );
				}
				else {
					_num_entropy_stack--;  // pop 0
					_num_all_stack = comp_id[_num_levels - 1];  // re-decompose
					_state_stack[_num_levels - 1] = 0;
					Assign( ~_dec_stack[_num_dec_stack], backjump_reason );  // reason is assigned in the last iteration
				}
				break;
			case 3:
				Entropy_Backtrack_Decision();
				break;
			}
		}
		else { // decomposition 多个组件
			assert( _active_all_comps[_num_levels - 1] == comp_id[_num_levels - 1] + _state_stack[_num_levels - 1] / 3 );
			if ( Is_Current_Level_Active() ) {  // not all components have been processed
				switch ( _state_stack[_num_levels - 1]++ % 3 ) {
				case 0:
					if (tim > running_options.Time_limit) {
						return;
					}
					entropy_cached = Component_Cache_Entropy_Map( Current_Allvar_Component() );
					cached_result = Component_Cache_Counting_Map( Current_Allvar_Component() );
					if ( cached_result != -1 ) {  /// NOTE: backjump makes that there are unknown cacheable component
						assert(entropy_cached != 999999);
						Iterate_Known( entropy_cached, cached_result );
						_state_stack[_num_levels - 1] += 2;
					}
					else {
						var = Pick_Good_Var_Component( Current_Allvar_Component() );
						Entropy_Extend_New_Level();
						Assign( Literal( var, false ) );
					}
					break;
				case 1:
					if ( Counting_stack[_num_entropy_stack - 1] != 0 ) {
						Entropy_Extend_New_Level();
						Assign( ~_dec_stack[_num_dec_stack] );
					}
					else {
						_num_entropy_stack--;  // pop 0
						Assign( ~_dec_stack[_num_dec_stack], backjump_reason );
						backjump_reason = Get_Approx_Imp_Component( Current_Allvar_Component(), backjump_level );  /// current component rather than parent component
						if ( backjump_reason != Reason::undef ) {
							Entropy_Backjump_Decomposition( backjump_level );
							break;
						}
						unsigned num_comp = Dynamic_Decompose_Component( Current_Allvar_Component(), Allvar_Compstack + _num_all_stack );
						_num_all_stack += num_comp - 1;  // Replace one component with its sub-components
						Current_Allvar_Component() = Allvar_Compstack[_num_all_stack];
						if ( Is_Current_Level_Decision() && !Is_Current_Level_Active() ) {	// all components except one collapsed into literals
							Backtrack_Decomposition2Decision();  // overwrite the result of the only one component
						}
						else if ( Is_Current_Level_Decision() ) {	// all components except one collapsed into literals, and this component is not handled yet
							assert( _active_all_comps[_num_levels - 1] == _num_all_stack - 1 );
							cached_result = Component_Cache_Counting_Map( Current_Allvar_Component());  /// NOTE: the current component was after the collapsed one
							entropy_cached = Component_Cache_Entropy_Map( Current_Allvar_Component() );
							if ( cached_result != -1 ) {  /// NOTE: backjump makes that there are unknown cacheable component
								assert(entropy_cached != 999999);
								Backtrack_Known_Entropy( entropy_cached, cached_result );
							}
							else _state_stack[_num_levels - 1] = 1;
						}
						else _state_stack[_num_levels - 1] -= 2;
					}
					break;
				case 2:
					Iterate_Decision();
					break;
				}
			}
			else {  // all components are already processed
				Entropy_Backtrack_Decomposition();
			}
		}
	}
	
	Entropy = Entropy_stack[_num_entropy_stack - 1];
	sum_count = Counting_stack[_num_entropy_stack - 1];
	//cout<<" _entropy_stack = "<<_num_entropy_stack<<" counting = "<<Counting_stack[_num_entropy_stack - 1]<<" entropy = "<<Entropy_stack[_num_entropy_stack - 1]<<endl;
	//assert( _num_levels == old_num_levels - 1 && _num_rsl_stack == old_num_rsl_stack + 1 );
}

bool TAG = false;
double firstcount_time = 0;
BigInt tt_count = 0;
void ECounter::print_result(BigInt total_count,double tim) {
	if (total_count == 0) total_count = tt_count;
	//cout<<sum_count<<","<<total_count<<",";
	cout << "c o The number of models is " << sum_count << endl;
	cout << "c o The entropy is ";
	printf("%.2f\n",Entropy);
	cout << "c o The time is ";
	printf("%.2f\n",tim);
}

double ECounter::Count_Entropy(const char * infile, CNF_Formula & cnf, Heuristic heur ) {
	Entropy_Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	START.Start(); // thl 全局时间
	StopWatch begin_watch, tmp_watch;
	if ( !running_options.display_counting_process ) {
		running_options.display_preprocessing_process = false;
		running_options.display_kernelizing_process = false;
	}
	if ( running_options.display_counting_process  ) cout << running_options.display_prefix << "Counting models..." << endl;
	Allocate_and_Init_Auxiliary_Memory( cnf.Max_Var() );
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	const vector<unsigned> Xlist = cnf.Get_Xlist();
	const vector<unsigned> Ylist = cnf.Get_Ylist();
	belong_XORY.resize(cnf.Max_Var() * 2 + 2);
	for (int i = 0 ; i < Xlist.size() ; i ++) {
		unsigned var = Xlist[i];
		belong_XORY[var] = 0;
	}
	for (int i = 0 ; i < Ylist.size() ; i ++) {
		unsigned var = Ylist[i];
		belong_XORY[var] = 1;
	}
	// cout<<Xlist.size()<<","<<Ylist.size()<<","<<_max_var<<endl;
	// return 0;
	// bool sat_ornot = Check_Circuit_Formula(cnf);
	// if (sat_ornot) cout<<"NO!!!!"<<endl;
	// else cout<<"YES"<<endl;
	// assert(sat_ornot == false);
	// return 0;
	double tim;
	

	BigInt total_count = 0;//Count_Models(cnf,heur);
	
	
	//print_heur();
	//tt_count = total_count;
	firstcount_time += START.Get_Elapsed_Seconds();
	
	// cout<<" Total_count = ";
	// printf(total_count);

	// cout<<"\n";
	// printf("%.5f,",firstcount_time);
	
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Begin preprocess..." << endl;
	running_options.detect_lit_equivalence = ( running_options.max_kdepth > 0 );
	
	running_options.recover_exterior = true;
	
	//cout<<"before preprocess"<<endl;
	//bool cnf_sat = Preprocess_Sharp( cnf, _models_stack[0] );
	
	bool cnf_sat = Preprocess( cnf, _models_stack[0] );
	
	//cout<<"preprocess done"<<endl;
	//Display_Processed_Clauses(cout,true);
	//Gather_Infor_For_Counting();
	
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "Preprocess done." << endl;
	if ( !cnf_sat ) {
		cout<<"UNSAT"<<endl;
		_num_levels--;
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
//				Display_Statistics( 0 );
			}
		}
		Reset();
		return 0;
	}
	if ( Non_Unary_Clauses_Empty() ) {
		Recycle_Models( _models_stack[0] );
		BigInt count = Backtrack_Init();
		if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_count = begin_watch.Get_Elapsed_Seconds();
		if ( running_options.display_counting_process ) {
			cout << running_options.display_prefix << "Done." << endl;
			if ( running_options.profile_counting >= Profiling_Abstract ) {
				Display_Statistics( 0 );
			}
		}
		Reset();
		tim += START.Get_Elapsed_Seconds();
		print_result(count,tim);
		return Entropy;
	}
	Store_Lit_Equivalences( _call_stack[0] );
	_fixed_num_vars -= _and_gates.size();
	Gather_Infor_For_Counting();
	if ( !running_options.static_heur ) Choose_Running_Options( heur );
	else Choose_Running_Options_Static( heur );

	running_options.imp_strategy = Partial_Implicit_BCP; // thl toremove
	Compiler BDDC_compiler;
	Diagram bddc;
	OBDDC_Manager BDDC_manager( cnf.Max_Var() );
	
	//bddc = BDDC_compiler.Compile( BDDC_manager, cnf, heur );
	
	//BigInt res = BDDC_manager.Count_Models( bddc );
	// Baseline_Search(bddc,BDDC_manager,cnf,Ylist,0,total_count,heur);
	// return 0;
	//_var_order.Display(cout);
	
	if ( running_options.display_counting_process && running_options.profile_counting != Profiling_Close ) running_options.Display( cout );  // ToRemove
	
	BigInt count;
	bool Baseline = false;
	if (Baseline) {
		Baseline_OBDDC(cnf,heur,total_count);
		tim += START.Get_Elapsed_Seconds();
		print_result(total_count,tim);
		cout<<endl;
		//return Entropy;
	}
	// bddc = BDDC_compiler.Compile( BDDC_manager, cnf, heur );

	if (running_options.Counting == "ConditionedCounting") {
		bddc = BDDC_compiler.Compile( BDDC_manager, cnf, heur );
	}

	if (running_options.ConjunctiveDecomposition) {
		//count = Count_Entropy_With_Implicite_BCP(cnf,Ylist,total_count,heur);
		Count_Entropy_With_ADDC(bddc, BDDC_manager , cnf,Ylist,total_count,heur);
	}
	else count = Count_Entropy_With_ADD(bddc, BDDC_manager,cnf,Ylist,total_count,heur);
	//Set_Current_Level_Kernelized( false );
	_fixed_num_vars += _and_gates.size();
	Load_Lit_Equivalences( _call_stack[0] );
	_call_stack[0].Clear_Lit_Equivalences();
	tim += START.Get_Elapsed_Seconds();
	print_result(total_count,tim);
	return Entropy;
}


BigInt ECounter::Entropy_Count_Models( unsigned old_num_dec)
{
	//Store_Lit_Equivalences( _call_stack[0] );
	//Choose_Running_Options( heur );
	StopWatch tmp;
	//_fixed_num_vars -= _and_gates.size();
	tmp.Start();
	//Gather_Infor_For_Counting();
	gather_time += tmp.Get_Elapsed_Seconds();
	unsigned pp = _num_levels;
	_num_levels ++ ;
	Set_Current_Level_Kernelized( true );
	tmp.Start();
	if (running_options.XCache == false) _component_cache.Clear();
	Component cp;
	unsigned Init = Create_Component_Init_Level(cp); // Parent_of_Current_Allvar_Component()
	Init_time += tmp.Get_Elapsed_Seconds();
	unsigned flag_init = 1;
	if (Init == 2 || Init == 1) flag_init = 0;
	unsigned backjump_level;
	unsigned pre_levels = _num_levels;
	tmp.Start();
	if (flag_init) {
		if ( running_options.imp_strategy != SAT_Imp_Computing ) {  // ToModify
		//here
			Recycle_Models( _models_stack[0] );
			if ( Large_Scale_Problem() ) _model_pool->Free_Unallocated_Models();
			//running_options.var_ordering_heur = Centrality; // thl toremove
			//Compute_Var_Centrality_Score(); // thl toremove
			//Compute_Second_Var_Order_Automatical(_comp_stack[0]);
			centtime += tmp.Get_Elapsed_Seconds();
			tmp.Start();
			Count_With_Implicite_BCP();
			//running_options.var_ordering_heur = minfill; // thl toremove
			IBCP_time += tmp.Get_Elapsed_Seconds();
		}
		else {
			if ( running_options.max_kdepth > 1 ) {
				if ( Is_Linear_Ordering( running_options.var_ordering_heur ) ) _lit_equivalency.Reorder( _var_order );
				Encode_Long_Clauses();
			}
			Count_With_SAT_Imp_Computing();
		}
	}
	Set_Current_Level_Kernelized( false );
	// _fixed_num_vars += _and_gates.size();
	// Load_Lit_Equivalences( _call_stack[0] );
	// _call_stack[0].Clear_Lit_Equivalences();
	BigInt count = Entropy_Backtrack_Init(old_num_dec,Init);
	//if ( debug_options.verify_learnts ) Verify_Learnts( cnf );
	//Reset();
	return count;
}

BigInt ECounter::Entropy_Backtrack_Init(unsigned old_num_dec,unsigned Init)
{
	if ( _num_rsl_stack == 0 ) {
		_rsl_stack[0] = Init;
		if (!running_options.ConjunctiveDecomposition) _rsl_stack[0].Mul_2exp( Num_Omitted_Vars() );  /// _unsimplifiable_num_vars is 0
		 //Un_BCP( _dec_offsets[--_num_levels] ); // pre code
		 _num_levels --; 
		 Un_BCP(old_num_dec); 
	}
	else {
		_num_rsl_stack--;
		if (!running_options.ConjunctiveDecomposition) _rsl_stack[0].Mul_2exp( Num_Omitted_Vars() );
		//Backtrack(); 
		_num_levels--;
		Un_BCP(old_num_dec); 
		_num_comp_stack = _comp_offsets[_num_levels];
	}
	return _rsl_stack[0];
}

unsigned ECounter::Create_Component_Init_Level_Pre()
{
	StopWatch tmp_watch;
	_dec_offsets[0] = 0;  // NOTE: the first bit facilitates loop break
	_comp_offsets[0] = 0;
	_active_all_comps[0] = 0;
	_num_rsl_stack = 0;
	assert( _num_levels == 1 );  // NOTE: level 0 is used to unary clauses
	Generate_Init_Component( *_comp_stack );  // NOTE: we will not decompose the initialized formula
	if (_comp_stack[0].Vars_Size() == 1) return 2; // 2^1
	if (_comp_stack[0].Vars_Size() == 0) return 1; // 2^0 ?
	_dec_offsets[1] = _num_dec_stack;
	_state_stack[1] = 1;
	_num_comp_stack = 1;
	_comp_offsets[1] = 0;
	_active_all_comps[1] = 0;
	_num_levels = 2;
	if ( running_options.profile_counting >= Profiling_Abstract ) tmp_watch.Start();
	if (_component_cache.Size() == 0) _component_cache.Init( _max_var, _old_num_long_clauses, -1 ); // now code
	Component_Cache_Add_Original_Clauses();
	_component_cache.Hit_Component( _comp_stack[0] );
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache = tmp_watch.Get_Elapsed_Seconds();
	return 0; // size >= 2
}

unsigned ECounter::Create_Component_Init_Level(Component & all_comp)
{
	StopWatch tmp_watch;
	_dec_offsets[_num_levels-1] = 0;  // NOTE: the first bit facilitates loop break
	_comp_offsets[_num_levels-1] = 0;
	_active_comps[_num_levels-1] = 0;
	_num_rsl_stack = 0;
	
	/*Variable i ; // pre code is Variable i;
	_comp_stack[0].Clear();
	for ( auto i = all_comp.VarIDs_Begin() ; i != all_comp.VarIDs_End() ; i ++) {  /// NOTE: must be sorted with respect to the lexicographic order for binary search
		if ( Var_Undecided( Variable(*i) ) && ( Var_Appeared( Variable(*i) ) ) ) _comp_stack[0].Add_Var( Variable(*i) );
	} // pre code is i ++; 
	_comp_stack[0].Add_Var( _max_var.Next() );
	_comp_stack[0].Dec_Var();  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
	for ( i = 0; i < _old_num_long_clauses; i++ ) {
		if (Clause_SAT(_long_clauses[i])) continue; // thl now code
		_comp_stack[0].Add_ClauseID( i );
	}*/

	//Generate_Init_Component( _comp_stack[0] );  // NOTE: we will not decompose the initialized formula
	
	_comp_stack[0] = Parent_of_Current_Allvar_Component();

	// if (true) {
	// 	_comp_stack[0].Clear();
	// 	for ( Variable i = Variable::start ; i != _max_var ; i ++) {  /// NOTE: must be sorted with respect to the lexicographic order for binary search
	// 		if ( Var_Undecided( i ) && ( Var_Appeared( i ) ) ) _comp_stack[0].Add_Var( i );
	// 	} // pre code is i ++; 
	// 	_comp_stack[0].Add_Var( _max_var.Next() );
	// 	_comp_stack[0].Dec_Var();  /// NOTE: prevent comp.Vars() from reallocating memory when push_back mar_var + 1 later
	// 	for ( unsigned i = 0; i < _old_num_long_clauses; i++ ) {
	// 		if (Clause_SAT(_long_clauses[i])) continue; // thl now code
	// 		_comp_stack[0].Add_ClauseID( i );
	// 	}
	// }
	
	//if (_comp_stack[0].Vars_Size() == 1 && _comp_stack[0].ClauseIDs_Size()) return 1;
	
	//if (_comp_stack[0].Vars_Size() == 1) return 2; // 2^1
	if (_comp_stack[0].Vars_Size() == 0) return 1; // 2^0 ?
	
	_dec_offsets[_num_levels] = _num_dec_stack;
	_state_stack[_num_levels] = 1;
	_num_comp_stack = 1;
	_comp_offsets[_num_levels] = 0;
	_active_comps[_num_levels] = 0;
	_num_levels ++;
	if ( running_options.profile_counting >= Profiling_Abstract ) tmp_watch.Start();
	if (running_options.XCache == false) _component_cache.Reset();
	if (_component_cache.Size() == 0) _component_cache.Init( _max_var, _old_num_long_clauses, -1 ); // now code
	//_component_cache.Init( _max_var, _old_num_long_clauses, -1 ); // pre code
	Component_Cache_Add_Original_Clauses(); // 可以删？
	_component_cache.Hit_Component( _comp_stack[0] );
	
	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache = tmp_watch.Get_Elapsed_Seconds();
	return 0; // size >= 2
}
void ECounter::Create_Init_Component()
{
	_num_levels = 1;
	_active_all_comps[0] = 0;
	_dec_offsets[0] = 0;  // NOTE: the first bit facilitates loop break
	assert( _num_levels == 1 );  // NOTE: level 0 is used to unary clauses
	_dec_offsets[1] = _num_dec_stack;
	_state_stack[1] = 1;
	_num_levels = 2;
	comp_id[1] = 0;
	_active_all_comps[1] = 0;
	_num_all_stack = 1;
	_num_entropy_stack = 0;
	StopWatch tmp_watch;
	Generate_Init_XYComponent( *Allvar_Compstack );
	Generate_Init_YComponent( *Ylist_Compstack );

	if ( running_options.profile_counting >= Profiling_Abstract ) tmp_watch.Start();
	if (Entropy_Cache.Size() == 0) Entropy_Cache.Init( _max_var, _old_num_long_clauses, 999999 );
	Entropy_Cache.Hit_Component( Allvar_Compstack[0] );

	if (Counting_Cache.Size() == 0) Counting_Cache.Init( _max_var, _old_num_long_clauses, -1 );
	Counting_Cache.Hit_Component( Allvar_Compstack[0] );

	if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache = tmp_watch.Get_Elapsed_Seconds();
}
void ECounter::Entropy_Component_Cache_Erase( Component & comp )
{
	unsigned back_loc = Counting_Cache.Size() - 1;
	unsigned back_entropy_loc = Entropy_Cache.Size() - 1;
	assert(back_loc == back_entropy_loc);
	Counting_Cache.Erase( comp.caching_loc );
	Entropy_Cache.Erase( comp.caching_loc );
	for ( unsigned i = 1 ; i < _num_levels; i++ ) { // pre code : unsigned i = 1; i < _num_levels; i++ 
		if ( Allvar_Compstack[comp_id[i]].caching_loc == back_loc ) {
			Allvar_Compstack[comp_id[i]].caching_loc = comp.caching_loc;
		} 
		for ( unsigned j = comp_id[i] + 1; j <= _active_all_comps[i]; j++ ) {
			if ( Allvar_Compstack[j].caching_loc == back_loc ) {
				Allvar_Compstack[j].caching_loc = comp.caching_loc;
			}
		}
		/*if ( _call_stack[i].Existed() ) {
			if ( _call_stack[i].Get_Caching_Loc() == back_loc ) {
				_call_stack[i].Set_Caching_Loc( comp.caching_loc );
			}
		}*/
	}
}

void ECounter::Entropy_Backjump_Decomposition( unsigned num_kept_levels )
{
	assert( num_kept_levels < _num_levels );
	_num_entropy_stack -= _active_all_comps[_num_levels - 1] - comp_id[_num_levels - 1];
	//if ( running_options.erase_useless_cacheable_component ) Entropy_Component_Cache_Erase( Current_Allvar_Component() ); // fo fix
	for ( _num_levels--; _num_levels > num_kept_levels; _num_levels-- ) {
		if ( comp_id[_num_levels] - comp_id[_num_levels - 1] <= 1 ) _num_entropy_stack -= _state_stack[_num_levels - 1] - 2;  // ToCheck
		else _num_entropy_stack -= _active_all_comps[_num_levels - 1] - comp_id[_num_levels - 1];
		//if ( running_options.erase_useless_cacheable_component ) Entropy_Component_Cache_Erase( Current_Allvar_Component() ); // to fix
	}
	Un_BCP( _dec_offsets[_num_levels] );
	_num_all_stack = comp_id[_num_levels];
	Entropy_stack[_num_entropy_stack] = 0;
	Counting_stack[_num_entropy_stack++] = 0;  /// NOTE: cannot omit when in the second decision, and need to be AFTER backjump
}

void ECounter::Entropy_Backjump_Decision( unsigned num_kept_levels) // thl
{
	assert( num_kept_levels < _num_levels );
	assert( _state_stack[_num_levels - 1] == 0 );
	for ( _num_levels--; _num_levels > num_kept_levels; _num_levels-- ) {
		if ( comp_id[_num_levels] - comp_id[_num_levels - 1] <= 1 ) _num_entropy_stack -= _state_stack[_num_levels - 1] - 2;  // ToCheck
		else _num_entropy_stack -= _active_all_comps[_num_levels - 1] - comp_id[_num_levels - 1];
		//if ( running_options.erase_useless_cacheable_component ) Component_Cache_Erase( Current_Component() );
	}
	_num_all_stack = comp_id[_num_levels];
	Un_BCP( _dec_offsets[_num_levels] );	
	Counting_stack[_num_entropy_stack] = 0;
	Entropy_stack[_num_entropy_stack ++] = 0;

	/*assert( num_kept_levels < _num_levels );
	assert( _state_stack[_num_levels - 1] == 0 );
	for ( _num_levels--; _num_levels > num_kept_levels; _num_levels-- ) {
		// if ( comp_id[_num_levels] - comp_id[_num_levels - 1] <= 1 ) {
		// 	_num_entropy_stack -= _state_stack[_num_levels - 1] - 2;  // ToCheck
		// }
		// else assert(0);
	}
	_num_all_stack = comp_id[_num_levels];
	_num_all_stack = comp_id[_num_levels];
	Un_BCP( _dec_offsets[_num_levels] );	
	Counting_stack[_num_entropy_stack] = 0;
	Entropy_stack[_num_entropy_stack ++] = 0;*/
}

void ECounter::Entropy_Extend_New_Level()
{
	_dec_offsets[_num_levels] = _num_dec_stack;
	comp_id[_num_levels] = _num_all_stack; // now thl BODDC code
	//comp_id[_num_levels] = _num_all_stack; // pre code 
	_active_all_comps[_num_levels] = comp_id[_num_levels];
	_state_stack[_num_levels++] = 0;
}
void ECounter::Backtrack_Known_Entropy( double entropy_cached , BigInt Counting_result)
{
	if ( debug_options.verify_component_count ) { // 
		Verify_Result_Component( Current_Allvar_Component(), Counting_result );
	}
	Counting_stack[_num_entropy_stack] = Counting_result;
	_aux_counting_stack[_num_entropy_stack ] = Current_Allvar_Component().Vars_Size() + Num_Current_Imps();
	Entropy_stack[_num_entropy_stack ++] = entropy_cached;
	Entropy_Backtrack();
}

bool ECounter::Entropy_Cache_Clear_Applicable()
{
	const size_t GB = 1024 * 1024 * 1024;
	double max_mem = running_options.max_memory * GB;
	if ( false ) {
		return Entropy_Cache.Memory() > max_mem * 0.5;
	}
	if ( Entropy_Cache.Memory() <= max_mem * 0.3 ) return false;
	if ( Entropy_Cache.Memory() > max_mem * 0.7 ) return true;
	if ( Entropy_Cache.Size() < Entropy_Cache.Capacity() || Entropy_Cache.Hit_Successful() ) return false;
	size_t mem = Total_Used_Memory();
	if ( running_options.display_counting_process && running_options.profile_counting != Profiling_Close ) {
		cout << (double) Entropy_Cache.Memory() / GB << " (cache) / ";
		cout << (double) mem / GB << " (total) in GB" << endl;
	}
	if ( mem < max_mem * 0.8 ) return false;
	else return true;
}
bool ECounter::Counting_Cache_Clear_Applicable()
{
	const size_t GB = 1024 * 1024 * 1024;
	double max_mem = running_options.max_memory * GB;
	if ( false ) {
		return Counting_Cache.Memory() > max_mem * 0.5;
		// if ( _component_cache.Memory() > max_mem * 0.5 ) return true;
		// double upper_bound = max_mem * 0.8;
		// if ( mem >= upper_bound ) return true;
		// unsigned size = _component_cache.Size();
		// unsigned capacity = size + size * ( upper_bound / mem - 1 ) / 2;
		// _component_cache.Reserve( capacity );  // in case of overflow
		// return false;
	}
	if ( Counting_Cache.Memory() <= max_mem * 0.3 ) return false;
	if ( Counting_Cache.Memory() > max_mem * 0.7 ) return true;
	if ( Counting_Cache.Size() < Counting_Cache.Capacity() || Counting_Cache.Hit_Successful() ) return false;
	size_t mem = Total_Used_Memory();
	if ( running_options.display_counting_process && running_options.profile_counting != Profiling_Close ) {
		cout << running_options.display_prefix << (double) Counting_Cache.Memory() / GB << " (cache) / ";
		cout << (double) mem / GB << " (total) in GB" << endl;
	}
	if ( mem < max_mem * 0.8 ) return false;
	else return true;
}
BigInt ECounter::Component_Cache_Counting_Map( Component & comp )
{
	StopWatch begin_watch;
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	if ( _current_kdepth <= 1 ) comp.caching_loc = Counting_Cache.Hit_Component( comp );
	else {
		assert(0);
	}
	// if ( Counting_Cache_Clear_Applicable() ) {
	// 	Counting_Component_Cache_Clear();
	// }
	//if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache += begin_watch.Get_Elapsed_Seconds();
	return Counting_Cache.Read_Result( comp.caching_loc );
}

double ECounter::Component_Cache_Entropy_Map( Component & comp ) // thl
{
	StopWatch begin_watch;
	const size_t GB = 1024 * 1024 * 1024;
	if ( running_options.profile_counting >= Profiling_Abstract ) begin_watch.Start();
	if ( _current_kdepth <= 1 ) comp.caching_loc = Entropy_Cache.Hit_Component( comp );
	else {
		assert(0);
	}
	//if ( Entropy_Cache_Clear_Applicable() || Counting_Cache_Clear_Applicable() || ADDL_cache.Memory() > running_options.max_memory / 4 * GB) { // OR Counting_Cache_Clear_Applicable()
	if ( Entropy_Cache_Clear_Applicable() || Counting_Cache_Clear_Applicable()) {	
		unsigned loc = Counting_Cache.Hit_Component( comp );
		assert(loc == comp.caching_loc);
		// loc = ADDL_cache.Hit_Component( comp );
		// assert(loc == comp.caching_loc);

		cout<<" Cache Clear "<<endl;
		
		Entropy_Component_Cache_Clear();
		
		Clear_times ++;
	}
	//  || Counting_Cache_Clear_Applicable()
	//if ( running_options.profile_counting >= Profiling_Abstract ) statistics.time_gen_cnf_cache += begin_watch.Get_Elapsed_Seconds();
	return Entropy_Cache.Read_Result( comp.caching_loc );
}

void ECounter::Entropy_Component_Cache_Clear() // thl
{
	/*vector<size_t> kept_locs;
	for ( unsigned i = 1 ; i < _num_levels; i++ ) { // update pre is i = 1 ,now is i = old_num_levels - 1
		kept_locs.push_back( Allvar_Compstack[comp_id[i]].caching_loc );
		for ( unsigned j = comp_id[i] + 1; j <= _active_all_comps[i]; j++ ) {
			kept_locs.push_back( Allvar_Compstack[j].caching_loc );
		}
	}
	for ( unsigned i = 1 ; i < _num_levels; i++ ) { // update pre is i = 1 ,now is i = old_num_levels - 1
		if ( _call_stack[i].Existed() ) {
			kept_locs.push_back( _call_stack[i].Get_Caching_Loc() );
		}
	}
	if ( true ) {
		Counting_Cache.Clear( kept_locs );  // ToModify
		Entropy_Cache.Clear( kept_locs );
	}
	//else Counting_Cache.Clear( kept_locs );
	unsigned index = 0;
	for ( unsigned i = 1 ; i < _num_levels; i++ ) {  // update pre is i = 1 ,now is i = old_num_levels - 1
		Allvar_Compstack[comp_id[i]].caching_loc = kept_locs[index++];
		for ( unsigned j = comp_id[i] + 1; j <= _active_all_comps[i]; j++ ) {
			Allvar_Compstack[j].caching_loc = kept_locs[index++];
		}
	}
	
	for ( unsigned i = 1 ; i < _num_levels; i++ ) { // update pre is i = 1 ,now is i = old_num_levels - 1
		if ( _call_stack[i].Existed() ) _call_stack[i].Set_Caching_Loc( kept_locs[index++] );
	}
*/

	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "clear cache" << endl;
	vector<size_t> kept_locs;
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		kept_locs.push_back( Allvar_Compstack[comp_id[i]].caching_loc );
	}
	Counting_Cache.Clear( kept_locs ); 
	//Counting_Cache.Clear_Half( kept_locs );  // ToModify

	kept_locs.clear();
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		kept_locs.push_back( Allvar_Compstack[comp_id[i]].caching_loc );
	}
	Entropy_Cache.Clear( kept_locs );
	//Entropy_Cache.Clear_Half( kept_locs );
	unsigned index = 0;
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		Allvar_Compstack[comp_id[i]].caching_loc = kept_locs[index++];
	}

}
void ECounter::Counting_Component_Cache_Clear() // thl
{
	if ( running_options.display_counting_process ) cout << running_options.display_prefix << "clear cache" << endl;
	vector<size_t> kept_locs;
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		kept_locs.push_back( Allvar_Compstack[comp_id[i]].caching_loc );
	}
	if ( true ) {
		Counting_Cache.Clear( kept_locs );  // ToModify
		Entropy_Cache.Clear( kept_locs );
	}
	unsigned index = 0;
	for ( unsigned i = 1; i < _num_levels; i++ ) {
		Allvar_Compstack[comp_id[i]].caching_loc = kept_locs[index++];
		// for ( unsigned j = comp_id[i] + 1; j <= _active_all_comps[i]; j++ ) {
		// 	_comp_stack[j].caching_loc = kept_locs[index++];
		// }
	}
	// for ( unsigned i = 1; i < _num_levels; i++ ) {
	// 	if ( _call_stack[i].Existed() ) _call_stack[i].Set_Caching_Loc( kept_locs[index++] );
	// }
}
void ECounter::Entropy_Backtrack()
{
	_num_levels--;
	Un_BCP( _dec_offsets[_num_levels] ); // precode
	_num_all_stack = comp_id[_num_levels];
}

int tmp_count = 0;
void ECounter::Entropy_Counting( Diagram & bddc , OBDDC_Manager & manager, CNF_Formula & cnf, BigInt total_count ,  Heuristic heur )
{
	countTimes ++;
	unsigned rest_var_num = Current_Allvar_Component().Vars_Size();
	BigInt num_models ;
	double res = -99;
	if (running_options.Counting == "SharedCounting") {
		num_models = Entropy_Count_Models(_num_dec_stack);
	}
	else {
		vector<Literal> assign;
		for (int i = 0 ; i < _num_dec_stack ; i ++) {
			assign.push_back(_dec_stack[i]);
		}
		// condition to do
		//num_models = -res;
		num_models = manager.Count_Models(bddc,assign);
	}
	//cout<<" num_models=  "<<num_models<<endl;

	debug_options.verify_component_count = false;
	if ( debug_options.verify_component_count ) { // 
		Verify_Result_Component( Current_Allvar_Component(), num_models );
	}
	//num_models = res2;
	//assert(res2 == num_models);
	double tim = START.Get_Elapsed_Seconds();
	if (tim > running_options.Time_limit) {
		cout<<"Time limit excceed ,";
		print_result(total_count,tim);
		exit(0);
	}
	if (res < 0) {
		res = num_models.TransformDouble();
		double t_c = total_count.TransformDouble();
		res = res / t_c;
		if (num_models != 0) res = res * log2(res);
		else res = 0;
		if (num_models != 0) Entropy -= res;
	}
	counting_time ++;

	//rest_var_num += Num_Omitted_Vars();

	Counting_stack[ _num_entropy_stack ] = num_models;
	_aux_counting_stack[ _num_entropy_stack ] = rest_var_num + Num_Current_Imps(); // rest_var_num; //Num_Current_Imps();
	Entropy_stack[ _num_entropy_stack ++ ] = 0; 
	
	if (Entropy_stack[_num_entropy_stack - 1] < 0) {
		cout<<" Wrong entropy = "<<Entropy_stack[_num_entropy_stack - 1]<<endl;
		assert(0);
	}
	if (running_options.YCache) {
		Entropy_Cache.Write_Result( Current_Allvar_Component().caching_loc, Entropy_stack[_num_entropy_stack - 1] );
		Counting_Cache.Write_Result( Current_Allvar_Component().caching_loc, Counting_stack[_num_entropy_stack - 1] );
	}
	Entropy_Backtrack();
}

void ECounter::Entropy_Backtrack_Decision()
{
	assert( _num_entropy_stack > 1 );
	assert( Counting_stack[_num_entropy_stack - 2] != 0 );  // backjump guarantees this
	bool incomplete = ( Counting_stack[_num_entropy_stack - 1] == 0 ); /// NOTE: conflict can come from the upper levels
	//cerr << Counting_stack[_num_entropy_stack - 2] << " vs " << Counting_stack[_num_entropy_stack - 1] << endl;  // ToRemove

	_num_entropy_stack--;
	unsigned omit = Current_Allvar_Component().Vars_Size() - _aux_counting_stack[_num_entropy_stack - 1] - 1;
	//cout<<"omit = "<<omit<<" Current_Allvar_Component().Vars_Size() = "<<Current_Allvar_Component().Vars_Size()<<"  _aux_counting_stack[_num_entropy_stack - 1] = "<<_aux_counting_stack[_num_entropy_stack - 1]<<endl;
	
	if (running_options.ConjunctiveDecomposition) Counting_stack[_num_entropy_stack - 1].Mul_2exp( omit );
	double low_p = Counting_stack[_num_entropy_stack - 1].TransformDouble();

	//cout<<"omit = "<<omit<<" num_stack -1 = "<<_num_entropy_stack-1<<"  res["<<_num_entropy_stack-1<<"]= "<<Counting_stack[_num_entropy_stack-1]<<endl;
	omit = Current_Allvar_Component().Vars_Size() - _aux_counting_stack[_num_entropy_stack] - 1;
	//cout<<"pre    omit="<<omit<<"  num_stack = "<<_num_entropy_stack<<"  res["<<_num_entropy_stack<<"]="<<Counting_stack[_num_entropy_stack]<<endl;
	if (running_options.ConjunctiveDecomposition) Counting_stack[_num_entropy_stack].Mul_2exp( omit );
	double high_p = Counting_stack[_num_entropy_stack].TransformDouble();
	
	//cout<<"Counting_stack["<<_num_entropy_stack - 1<<"]="<<Counting_stack[_num_entropy_stack - 1]<<"   Counting_stack["<<_num_entropy_stack<<"] = "<< Counting_stack[_num_entropy_stack]<<endl;
	
	Counting_stack[_num_entropy_stack - 1] += Counting_stack[_num_entropy_stack];
	if ( _num_levels != 2 ) _aux_counting_stack[_num_entropy_stack - 1] = Current_Allvar_Component().Vars_Size() + Num_Current_Imps();
	else _aux_counting_stack[_num_entropy_stack - 1] = Current_Allvar_Component().Vars_Size();// NOTE: _dec_offsets[1] is equal to the number of initial implied literals
	
	double entropy = 0;
	//cout<<" backtrack_Decision var = "<<_dec_stack[_dec_offsets[_num_levels]].Var()<<endl;
	if (belong_XORY[_dec_stack[_dec_offsets[_num_levels]].Var()]) {
		double p = low_p + high_p;
		//cout<<"low_models = "<<low_p<<" high_models= "<<high_p<<" ";
		low_p = low_p / p;
		high_p = high_p / p;
		if (low_p != 0) entropy += low_p * Entropy_stack[_num_entropy_stack - 1] - low_p * log2(low_p);
		if (high_p != 0) entropy += high_p * Entropy_stack[_num_entropy_stack] - high_p * log2(high_p);
	}
	
	Entropy_stack[_num_entropy_stack - 1] = entropy;

	debug_options.verify_component_count = false;
	if ( debug_options.verify_component_count ) {
		Verify_Result_Component( Current_Allvar_Component(), Counting_stack[_num_entropy_stack - 1] );
	}

	if (!incomplete) {
		if (running_options.YCache) { 
			Counting_Cache.Write_Result( Current_Allvar_Component().caching_loc, Counting_stack[_num_entropy_stack - 1] );
			Entropy_Cache.Write_Result( Current_Allvar_Component().caching_loc, Entropy_stack[_num_entropy_stack - 1] );
		}
	}
	Entropy_Backtrack();
}

/* Above is ECounter */

/* Follow is Baseline */

	BigInt ECounter::Count_With_OBDDC( const Diagram & bddc, OBDDC_Manager & manager, CNF_Formula & cnf, BigInt total_count, Heuristic heur ) {
		Gather_Infor_For_Counting();
		Create_Init_Component();
		unsigned old_num_levels = _num_levels;
		unsigned old_num_rsl_stack = _num_rsl_stack;
		Variable var;
		double cached_result;
		BigInt Counting_result = 0;
		NodeID Cached_Node;
		Reason backjump_reason = Reason::undef;  // just used for omitting warning
		unsigned backjump_level;
		unsigned pre_num_dec_stack;
		unsigned first_num_dec_stack = _num_dec_stack;
		bool flag;
		int loop_count = 0;
		int tt = 0;
		int op = 0;
		int delta = 0,prenum;
		Heuristic pre_heur = running_options.var_ordering_heur;
		vector<int> Ylist;
		for (int i = 0 ; i < cnf.Max_Var() ; i ++) {
			if (belong_XORY[i]) Ylist.push_back(i);
		}
		while ( _num_levels >= old_num_levels ) {
			StopWatch tmp;
			loop_count ++;
			double tim;
			switch ( _state_stack[_num_levels - 1] ) {	 // decision or preparation 	逐一尝试 false true
			case 0: // 蕴含文字
				tim = START.Get_Elapsed_Seconds();
				if (tim > running_options.Time_limit) {
					cout<<"Time limit excceed ,";
					print_result(total_count,tim);
					exit(0);
				}
				pre_num_dec_stack = _num_dec_stack;
				backjump_reason = BCP(first_num_dec_stack); //Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component() ,backjump_level);
				if ( backjump_reason != Reason::undef ) {
					_num_levels--;
					_num_all_stack = comp_id[_num_levels];
					Un_BCP( _dec_offsets[_num_levels] );	
					Counting_stack[_num_entropy_stack] = 0;
					Entropy_stack[_num_entropy_stack ++] = 0;
					break;
				}
				Un_BCP(pre_num_dec_stack);
				flag = true;
				for (int i = 0 ; i < Ylist.size() ; i ++) {
					Variable var = Variable(Ylist[i]);
					if (Var_Undecided(var)) flag = false;
				}
				GetYlist_NextComponent( Parent_of_Ylist_Component() , Ylist_Compstack[_num_all_stack] );
				flag = false;
				if (Current_Ylist_Component().Vars_Size() == 0) flag = true;
				GetAllvar_NextComponent( Parent_of_Current_Allvar_Component() , Allvar_Compstack[_num_all_stack ++] );
				assert(Allvar_Compstack[_num_all_stack - 1] == Current_Allvar_Component());
				Counting_result = -1;
				cached_result = 99999;
				Cached_Node = NodeID::undef;
				if (Current_Allvar_Component().Vars_Size() >= 2) {
					tmp.Start();
					//cached_result = Component_Cache_Entropy_Map( Current_Allvar_Component());
					//Counting_result = Component_Cache_Counting_Map( Current_Allvar_Component() );
					//YCache_hit_time += tmp.Get_Elapsed_Seconds();
				}
				if (flag) {
					/*BCP(first_num_dec_stack);
					backjump_reason = BCP(first_num_dec_stack); //Get_Approx_Imp_Component( Parent_of_Current_Allvar_Component() ,backjump_level);
					if ( backjump_reason != Reason::undef ) {
						_num_levels--;
						_num_all_stack = comp_id[_num_levels];
						Un_BCP( _dec_offsets[_num_levels] );	
						Counting_stack[_num_entropy_stack] = 0;
						Entropy_stack[_num_entropy_stack ++] = 0;
						break;
					}*/
					BDDC_Counting(bddc, cnf,manager,total_count,heur);
					//Un_BCP( pre_num_dec_stack );
				}
				else _state_stack[_num_levels - 1]++;
			break;
			case 1:
				_state_stack[_num_levels - 1]++; 
				tmp.Start();
				//var = Pick_Good_Var_Component(Current_Allvar_Component());
				var = Pick_Good_Var_Component(Current_Ylist_Component());
				picktime += tmp.Get_Elapsed_Seconds();
				Entropy_Extend_New_Level();
				Assign( Literal( var, false ) );
				break;
			case 2:
				//if (Entropy_stack[_num_entropy_stack - 1] != 0) 
				if (Counting_stack[_num_entropy_stack - 1] != 0) {
					_state_stack[_num_levels - 1]++;
					Entropy_Extend_New_Level();
					Assign( ~_dec_stack[_num_dec_stack] );
					//cout<<" var = "<<_dec_stack[_num_dec_stack-1].Var()<<" "<<_dec_stack[_num_dec_stack-1].Sign()<<endl;
				}
				else {
					_num_entropy_stack --;
					_num_addl_stack --;
					_num_all_stack = comp_id[_num_levels - 1];
					_state_stack[_num_levels - 1] = 0;
					Assign( ~_dec_stack[_num_dec_stack], backjump_reason );
					//cout<<" var = "<<_dec_stack[_num_dec_stack-1].Var()<<" "<<_dec_stack[_num_dec_stack-1].Sign()<<endl;
				}
				break;
			case 3:
				Entropy_Backtrack_Decision();
				break;
			}
		}
		assert( _num_levels == 1 );
		return 1;
	}
	void ECounter::BDDC_Counting( const Diagram & bddc, CNF_Formula & cnf,  OBDDC_Manager & manager , BigInt total_count ,  Heuristic heur)
	{
		StopWatch tmp;
		tmp.Start();
		unsigned rest_var_num = Current_Allvar_Component().Vars_Size();
		BigInt num_models ;
		double res = -99;
		bool Used_BDDC = true;
		vector<Literal> assign;
		for (int i = 0 ; i < _num_dec_stack ; i ++) {
			assign.push_back(_dec_stack[i]);
		}
		num_models = manager.Count_Models(bddc,assign);
		double tim = START.Get_Elapsed_Seconds();
		if (tim > running_options.Time_limit) {
			cout<<"Time limit excceed ,";
			print_result(total_count,tim);
			exit(0);
		}
		//if (++ tmp_count > 10000) exit(0); // toremove
		time_counting += tmp.Get_Elapsed_Seconds();
		if (num_models == 0) count_modelzero ++; 
		sum_count += num_models;
		if (res < 0) {
			res = num_models.TransformDouble();
			double t_c = total_count.TransformDouble();
			res = res / t_c;
			if (num_models != 0) res = res * log2(res);
			else res = 0;
			if (num_models != 0) Entropy -= res;
		}
		counting_time ++;
		rest_var_num += Num_Omitted_Vars();
		Counting_stack[ _num_entropy_stack ] = num_models;
		Entropy_stack[ _num_entropy_stack ++ ] = - res;
		if (Entropy_stack[_num_entropy_stack - 1] < 0) {
			cout<<" Wrong entropy = "<<Entropy_stack[_num_entropy_stack - 1]<<endl;
			assert(0);
		}
		/*if (running_options.YCache) {
			Entropy_Cache.Write_Result( Current_Allvar_Component().caching_loc, Entropy_stack[_num_entropy_stack - 1] );
			Counting_Cache.Write_Result( Current_Allvar_Component().caching_loc, Counting_stack[_num_entropy_stack - 1] );
		}*/
		Entropy_Backtrack();
	}
	
	void ECounter::Baseline_OBDDC(CNF_Formula & cnf, Heuristic heur,BigInt total_count) {
		Compiler BDDC_compiler;
		OBDDC_Manager BDDC_manager( cnf.Max_Var() );
		Diagram bddc;
		
		bddc = BDDC_compiler.Compile( BDDC_manager, cnf, heur );
		//cout << "c o Number of models: " << BDDC_manager.Count_Models( bddc ) << endl;
		if (BDDC_manager.Count_Models( bddc ) != total_count) cout<<"NO,";
		//BDDC_manager.Display(cout);
		Entropy = BDDC_manager.Count_Entropy(bddc,belong_XORY);
		//BigInt res = Count_With_OBDDC(bddc, BDDC_manager,cnf,total_count,heur);
	}
}