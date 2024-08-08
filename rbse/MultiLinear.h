#pragma once
#include "QRAT.h"
#include "File.h"
#include "Circuits.h"
//using namespace ccircuits;
namespace multilinear {
	struct IndexLit {//tracks the numerical names of membership literals
		bool is_membership_defined;
		Var membership; //l in C^i
		Cnf* def_membership;
		//Circuit* circ_membership;
		Lit lit; //original literal

		IndexLit() {
			is_membership_defined = 0;
			membership = 0;
			lit = Lit();
			def_membership = new Cnf;
			//circ_membership = new Circuit;
		}
	};
	struct IndexLine {//tracks the numerical names of extension variables on a line by line basis
		//bool is_tautological_defined;
		bool is_selon_defined;
		bool is_selval_defined;
		bool is_ancestor_defined;
		bool is_xselval0_defined;
		bool is_xselval1_defined;

		LinkL<IndexLit>* memberships;

		Var membership_start; //convenient start and end points for list of IndexLits
		Var membership_end;


		//Var tautological;
		//Cnf* def_tautological;

		//Cnf members are used to store definition clauses, which are later loaded in order to the main Cnf

		Var selon; // variable for whether C^i is derived as selection rule instead of resolution
		Cnf* def_selon;
		//Circuit* circ_selon;
		Var selval;//variable for the direction of the selection rule
		Cnf* def_selval;
		//Circuit* circ_selval;

		Var ancestor;//variable to signal if connected to the empty clause (or other specified base), used for the strategy
		Cnf* def_ancestor;
		//Circuit* circ_ancestor;
		Var xselval0;//variable used aid a big disjunction for the definition of earlier ancestors
		Cnf* def_xselval0;
		//Circuit* circ_xselval0;
		Var xselval1;//variable used aid a big disjunction for the definition of earlier ancestors
		Cnf* def_xselval1;
		//Circuit* circ_xselval1;

		IndexLine() {
			//is_tautological_defined = 0;
			is_selon_defined = 0;
			is_selval_defined = 0;
			is_ancestor_defined =0;
			is_xselval0_defined =0;
			is_xselval1_defined =0;
			membership_start = 0;
			membership_end = 0;
			//tautological = 0;
			selon = 0;
			selval = 0;
			memberships = new LinkL < IndexLit>;
			//def_tautological = new Cnf;
			def_selon = new Cnf;
			//circ_selon = new Circuit;
			def_selval = new Cnf;
			//circ_selon = new Circuit;

			ancestor = 0;
			def_ancestor = new Cnf;
			//circ_ancestor = new Circuit;
			xselval0 = 0;
			def_xselval0 = new Cnf;
			//circ_xselval0 = new Circuit;
			xselval1 = 0;
			def_xselval1 = new Cnf;
			//circ_xselval1 = new Circuit;
		}
	};

	struct IndexStrat {//Keeps track of the numerical name of the strategy extension variable for each universal variable 
		Var u;
		bool is_strategy_defined;
		Var strategy;// strategy extension variable defined by axiom ancestors
		Cnf* def_strategy;
		//Circuit* circ_strategy;
		LinkL<int>* axioms;
		LinkL<int>* ucommitments;

		IndexStrat() {
			is_strategy_defined = 0;
			strategy = 0;
			def_strategy = new Cnf;
			//circ_strategy = new Circuit;

			axioms = new LinkL <int>;
		}
	};

	struct Strategy_Extractor {//does the main technical work of the solution
		QCNF* input_QBF;
		ClausalProof* input_proof;
		Cnf* extension_clauses;//intermediate to output, this is a satisfiable CNF
		Cnf* negated_assumptions;//adding this to the extension clauses gives unsatisfiability
		Cnf* output_cnf;// used to store the full output
		QRAT_Proof* output_QRAT;// in some versions of this program extension was done using QRATs rules
		LinkL<LinkL<IndexLine>>* main_index;//stores the index for numerical names of extension variables
		LinkL<IndexStrat>* strategy_index;//the extra numerical names for strategies are stored seperately
		int base_max_var;//the maximum variable in the input_QBF
		int idx_max_var;//the maximum variable appearing in the indexes
		Prefix* long_prefix;//full prefix with all extension variables, original prefix in input_QBF

		Strategy_Extractor() {
			input_QBF = new QCNF;
			input_proof = new ClausalProof;
			extension_clauses = new Cnf;
			negated_assumptions = new Cnf;
			output_cnf = new Cnf;
			output_cnf = new Cnf;
			output_QRAT = new QRAT_Proof();
			main_index = new LinkL<LinkL<IndexLine>>;
			strategy_index = new LinkL<IndexStrat>;
			base_max_var = 0;
			idx_max_var = 0;
			long_prefix = new Prefix;
		}
		Strategy_Extractor(QCNF* phi, ClausalProof* pi) {
			input_QBF = new QCNF();
			input_QBF->matrix = ccopy(phi->matrix);//length should be same
			input_QBF->prefix = copy(phi->prefix);//length should be same
			input_proof = pi;
			output_cnf = new Cnf;
			extension_clauses = new Cnf;
			negated_assumptions = new Cnf;
			output_QRAT = new QRAT_Proof();
			output_QRAT->Phi = *input_QBF;
			base_max_var = phi->matrix.mvar;
			idx_max_var = base_max_var;
			long_prefix = new Prefix;// starts empty rather than a copy
		}

		void load_output_cnf_negated() {//adds everything to output_cnf
			output_cnf->makeempty();
			copyinto(output_cnf, &(input_QBF->matrix));
			copyinto(output_cnf, extension_clauses);//should still be satisfiable
			copyinto(output_cnf, negated_assumptions);//becomes unsatisfiable
		}
	};

	void increment(Var* max_var, Prefix* P, Var* idx) {//adds a new extension variable
		int new_val = *max_var + 1;
		*max_var = new_val;
		P->addvar(new_val);//adds to end 
		*idx = new_val;
	}

	int add_literal1(Var max_var, IndexLine* idx_line, Prefix* P, Clause C, int position) {//adds a new membership literal
		IndexLit* temp = new IndexLit();
		increment(&max_var, P, &(temp->membership));
		temp->lit = C[position]; //record the actual literal in the index for easy reference
		idx_line->memberships->addnode(*temp);
		return max_var;
	}

	int add_IndexLine(Var max_var, LinkL<IndexLine>* idx_layer, Prefix* P, ClausalProof* pi, int line_no) {// add an entry on memberships, taut and sel
		IndexLine* temp = new IndexLine();
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		Link1<Lit>* current = C.head;
		int position = 0; //position for the literals 
		if (L.rule == RESOLUTION) {//only resolution steps can become selection
			increment(&max_var, P, &(temp->selon));
			increment(&max_var, P, &(temp->selval));
		}
		//increment(&max_var, P, &(temp->tautological));
		if (C.length > 0) {
			temp->membership_start = max_var + 1;
			//each literal is done individually
			while (current != NULL) {
				max_var = add_literal1(max_var, temp, P, C, position);
				current = current->next;
				position++;
			}
			temp->membership_end = max_var;
		}
		idx_layer->addnode(*temp);
		return max_var;
	}

	int addbackwards_IndexLine(Var max_var, LinkL<IndexLine>* idx_column, Prefix* P, ClausalProof* pi) {
		//start at bot, move backwards
		int botpos = pi->tail->position;
			for (int i = botpos; i >= 0; i--) {//i is the first (row) index
				Link1<IndexLine>* idx_cell = idx_column->findnode(i);
				increment(&max_var, P, &(idx_cell->data.ancestor));
				if (pi->operator[](i).rule == RESOLUTION) {
					//increment(&max_var, P, &(idx_cell->data.xselon));
					increment(&max_var, P, &(idx_cell->data.xselval0));
					increment(&max_var, P, &(idx_cell->data.xselval1));
				}
			}
		return max_var;
	}

	int add_layer(Var max_var, LinkL<LinkL<IndexLine> >* idx_proof, Prefix* P, ClausalProof* pi) {//adds the numerical names of extension variables for the next restricted proof 
		
		//we do not need the restriction level, this will be obvious as the position in the link list
		LinkL<IndexLine>* temp = new LinkL<IndexLine>();
		Link1<Line<Clause>>* current = pi->head;
		int line_no = 0;
		while (current != NULL) {
			max_var = add_IndexLine(max_var, temp, P, pi, line_no);// each line is added 
			//note for here we add all lines not just connected ones this makes it a little easier to calculate the numerical names, but perhaps wastes them when thye do not appear
			current = current->next;
			line_no++;
		}
		//ancestors are defined backwards
		max_var = addbackwards_IndexLine(max_var, temp, P, pi);
		idx_proof->addnode(*temp);
		return max_var;
	};

	int add_disjunct(Var max_var, IndexStrat* idx_u, Prefix* P, int line_no) {
		int* temp = new int;
		*temp = line_no;
		idx_u->axioms->addnode(*temp);
		return max_var;
	}

	int add_universal(Var max_var, LinkL<IndexStrat>* idx_strat, Prefix* P, ClausalProof* pi, Var u) {

		IndexStrat* temp = new IndexStrat();
		temp->u = u;
		Link1<Line<Clause>>* current = pi->head;
		//temp->xmembership_start = max_var + 1;
		bool found_axiom = 0;
		while (current != NULL) {
			if (current->data.rule == AXIOM) {
				//check all literals
				Link1<Lit>* current_lit = current->data.clause.head;
				int upos = -1;
				while (current_lit != NULL) {
					if (current_lit->data == Lit(u)) {

						upos = current_lit->position;
					}
					current_lit = current_lit->next;
				}
				if (upos != -1) {
					found_axiom = 1;
					max_var = add_disjunct(max_var, temp, P, current->position);
				}
			}
			current = current->next;
		}
		increment(&max_var, P, &(temp->strategy));
		idx_strat->addnode(*temp);
		return max_var;
	}

	void def_line(Strategy_Extractor* SE, IndexLine read, int level, int line_no) {// add an entry on memberships, taut and sel
		//Index1* temp = new Index1();
		Prefix P = SE->input_QBF->prefix;
		ClausalProof* pi = SE->input_proof;
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		QRAT_Proof* qrat = SE->output_QRAT;// we also create a QRAT proof
		int position = 0;
		if (L.rule == AXIOM) {
			//Clause taut_long;
			//Lit taut = Lit(read.tautological);//tautological implies clause less than level
			//taut_long.addnode(-taut);
			if (C.length > 0) {

				Link1<Lit>* current = C.head;
				while (current != NULL) {
					//def_literal1(max_var, temp, P, C, position);
					Lit l = current->data;
					Lit ml = Lit(read.memberships->operator[](position).membership);
					if (P.lvl(l.var) <= level) {
						//Clause taut_short;// any satisfied literal implies tautological
						//taut_short.addnode(-l);
						//taut_short.addnode(taut);
						//read.def_tautological->addnode(taut_short);//RATA on taut: trivial
						//qrat->QRATA(taut_short, taut);
						Clause mem_equiv1; //literal implies membership
						mem_equiv1.addnode(-l);
						mem_equiv1.addnode(ml);
						Clause mem_equiv2; //literal implies membership
						mem_equiv2.addnode(l);
						mem_equiv2.addnode(-ml);
						read.memberships->operator[](position).def_membership->addnode(mem_equiv1);//RATA on ml: trivial
						qrat->QRATA(mem_equiv1, ml);
						read.memberships->operator[](position).def_membership->addnode(mem_equiv2);//RATA on -ml: l, -l blocked on mem_equiv1
						qrat->QRATA(mem_equiv2, -ml);
						//taut_long.addnode(l);

					}
					else {
						Clause mem_assertion;
						mem_assertion.addnode(ml);
						read.memberships->operator[](position).def_membership->addnode(mem_assertion);//RATA on ml: trivial
						qrat->QRATA(mem_assertion, ml);
					}


					current = current->next;
					position++;
				}
			}
			//read.def_tautological->addnode(taut_long);//RATA on -taut: l, -l blocked on each taut_short
			//qrat->QRATA(taut_long, -taut);
		}
		if (L.rule == RESOLUTION) {


			int parent0 = L.parent0;
			int litpos0 = L.litpos0;
			int parent1 = L.parent1;
			int litpos1 = L.litpos1;
			Lit p0 = Lit(SE->main_index->operator[](level).operator[](parent0).memberships->operator[](litpos0).membership, 1);
			Lit p1 = Lit(SE->main_index->operator[](level).operator[](parent1).memberships->operator[](litpos1).membership, 1);
			Lit selonl = Lit(read.selon);
			Lit selvall = Lit(read.selval);
			Clause selon_long;//defines when selon is false i.e. none of the triggers
			selon_long.addnode(-selonl);

			Clause selon_p0;//asserts selon true when missing pivot at parent0
			selon_long.addnode(-p0);
			selon_p0.addnode(p0);
			selon_p0.addnode(selonl);
			read.def_selon->addnode(selon_p0);//RATA on selonl: trivial
			qrat->QRATA(selon_p0, selonl);
			Clause selon_p1;//asserts selon true when missing pivot at parent1
			selon_long.addnode(-p1);
			selon_p1.addnode(p1);
			selon_p1.addnode(selonl);
			read.def_selon->addnode(selon_p1);//RATA on selonl: trivial
			qrat->QRATA(selon_p1, selonl);
			Clause selval_0andnot1; //asserts selval when only pivot1 is missing;
			selval_0andnot1.addnode(selvall);
			selval_0andnot1.addnode(-p0);
			selval_0andnot1.addnode(p1);
			read.def_selval->addnode(selval_0andnot1);//RATA on selvall: trivial
			qrat->QRATA(selval_0andnot1, selvall);
			if (level > 0) {
				Lit prevon = Lit(SE->main_index->operator[](level - 1).operator[](line_no).selon, 1);
				Lit prevval = Lit(SE->main_index->operator[](level - 1).operator[](line_no).selval, 1);
				Clause selon_prev; //triggers if previous selon is true
				selon_long.addnode(prevon);
				selon_prev.addnode(-prevon);
				selon_prev.addnode(selonl);
				read.def_selon->addnode(selon_prev);//RATA on selonl: trivial
				qrat->QRATA(selon_prev, selonl);

				Clause selval_prevs;//triggers if previous selon is true and selval already true
				selval_prevs.addnode(-prevon);
				selval_prevs.addnode(-prevval);
				selval_prevs.addnode(selvall);
				read.def_selval->addnode(selval_prevs);//RATA on selvall: trivial
				qrat->QRATA(selval_prevs, selvall);

				Clause selval_0on;// sets selval FALSE if previous sel is off and current parent0 missing pivot
				Clause selval_0val;// sets selval FALSE if previous val is false and current parent0 missing pivot
				Clause selval_1on;// sets selval FALSE if previous sel is off and current parent1 contains pivot
				Clause selval_1val;// sets selval FALSE if previous val is false and current parent1 contains pivot

				selval_0on.addnode(-selvall);
				selval_0on.addnode(prevon);
				selval_0on.addnode(p0);
				read.def_selval->addnode(selval_0on);//RATA on -selvall, blocked by -prevon on selval_prevs, blocked by -p0 on selval_0andnot1
				qrat->QRATA(selval_0on, -selvall);


				selval_0val.addnode(-selvall);
				selval_0val.addnode(prevval);
				selval_0val.addnode(p0);
				read.def_selval->addnode(selval_0val);//RATA on -selvall, blocked by -prevval on selval_prevs, blocked by -p0 on selval_0andnot1
				qrat->QRATA(selval_0val, -selvall);

				selval_1on.addnode(-selvall);
				selval_1on.addnode(prevon);
				selval_1on.addnode(-p1);
				read.def_selval->addnode(selval_1on);//RATA on -selvall, blocked by -prevon on selval_prevs, blocked by p1 on selval_0andnot1
				qrat->QRATA(selval_1on, -selvall);

				selval_1val.addnode(-selvall);
				selval_1val.addnode(prevval);
				selval_1val.addnode(-p1);
				read.def_selval->addnode(selval_1val);//RATA on -selvall, blocked by -prevval on selval_prevs, blocked by p1 on selval_0andnot1
				qrat->QRATA(selval_1val, -selvall);
			}
			else {
				Clause selval_0;// sets selval FALSE if current parent0 missing pivot
				selval_0.addnode(-selvall);
				selval_0.addnode(p0);
				read.def_selval->addnode(selval_0);//RATA on -selvall, blocked by p0;
				qrat->QRATA(selval_0, -selvall);
				Clause selval_1;// sets selval FALSE if current parent1 contains pivot
				selval_1.addnode(-selvall);
				selval_1.addnode(-p1);
				read.def_selval->addnode(selval_1);//RATA on -selvall, blocked by p1;
				qrat->QRATA(selval_1, -selvall);
			}

			read.def_selon->addnode(selon_long);//RATA on -selonl: blocked on each short clause
			qrat->QRATA(selon_long, -selonl);

			//taut
			//Lit tautl = Lit(read.tautological);
			//Lit taut_parent0 = Lit(I->Idx_Proof->operator[](level).operator[](parent0).tautological);
			//Lit taut_parent1 = Lit(I->Idx_Proof->operator[](level).operator[](parent1).tautological);

			//Clause taut_forwardoff0;
			//taut_forwardoff0.addnode(selonl);
			//taut_forwardoff0.addnode(-taut_parent0);
			//taut_forwardoff0.addnode(tautl);
			//read.def_tautological->addnode(taut_forwardoff0);//RATA on tautl: trivial
			//qrat->QRATA(taut_forwardoff0, tautl);

			//Clause taut_forwardoff1;
			//taut_forwardoff1.addnode(selonl);
			//taut_forwardoff1.addnode(-taut_parent1);
			//taut_forwardoff1.addnode(tautl);
			//read.def_tautological->addnode(taut_forwardoff1);//RATA on tautl: trivial
			//qrat->QRATA(taut_forwardoff1, tautl);

			//Clause taut_forwardon0;
			//taut_forwardon0.addnode(-selonl);
			//taut_forwardon0.addnode(selvall);
			//taut_forwardon0.addnode(-taut_parent0);
			//taut_forwardon0.addnode(tautl);
			///read.def_tautological->addnode(taut_forwardon0);//RATA on tautl: trivial
			//qrat->QRATA(taut_forwardon0, tautl);

			//Clause taut_forwardon1;
			//taut_forwardon1.addnode(-selonl);
			//taut_forwardon1.addnode(-selvall);
			//taut_forwardon1.addnode(-taut_parent1);
			//taut_forwardon1.addnode(tautl);
			//read.def_tautological->addnode(taut_forwardon1);//RATA on tautl: trivial
			//qrat->QRATA(taut_forwardon1, tautl);

			//Clause taut_backwardoff;
			//taut_backwardoff.addnode(selonl);
			//taut_backwardoff.addnode(taut_parent0);
			//taut_backwardoff.addnode(taut_parent1);
			//taut_backwardoff.addnode(-tautl);
			//read.def_tautological->addnode(taut_backwardoff);//RATA on -tautl: 0 blocked on -taut_parent0, 1 blocked on -taut_parent1
			//qrat->QRATA(taut_backwardoff, -tautl);

			//Clause taut_backwardon0;
			//taut_backwardon0.addnode(-selonl);
			//taut_backwardon0.addnode(selvall);
			//taut_backwardon0.addnode(taut_parent0);
			//taut_backwardon0.addnode(-tautl);
			//read.def_tautological->addnode(taut_backwardon0); //RATE on -taul: 0 blocked on -taut_parent0, off1 blocked by selonl, on1 blocked by selvall
			//qrat->QRATA(taut_backwardon0, -tautl);

			//Clause taut_backwardon1;
			//taut_backwardon1.addnode(-selonl);
			//taut_backwardon1.addnode(-selvall);
			//taut_backwardon1.addnode(taut_parent1);
			//taut_backwardon1.addnode(-tautl);
			//read.def_tautological->addnode(taut_backwardon1); //RATA on -tautl: 1 blocked on -taut_parent1, off0 blocked by selonl, on0 blocked by selvall
			//qrat->QRATA(taut_backwardon1, -tautl);
			//members
			Clause P0 = pi->operator[](parent0).clause;
			Clause P1 = pi->operator[](parent1).clause;
			Link1<Lit>* current = L.clause.head;
			int lit_counter = 0;
			while (current != NULL) {
				Lit l = current->data;
				int pos0 = find_a_position(l, P0);
				int pos1 = find_a_position(l, P1);
				Lit meml = Lit(read.memberships->operator[](lit_counter).membership);
				if ((pos0 == -1) && (pos1 != -1)) {
					Lit l1 = Lit(SE->main_index->operator[](level).operator[](parent1).memberships->operator[](pos1).membership);
					Clause mem_val;//sets meml true if selval=1 and l1
					mem_val.addnode(-selvall);
					mem_val.addnode(-l1);
					mem_val.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_val);//RATA on meml, trivial;
					qrat->QRATA(mem_val, meml);
					Clause mem_on;// sets meml true if seloff and l1
					mem_on.addnode(selonl);
					mem_on.addnode(-l1);
					mem_on.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_on);//RATA on meml, trivial;
					qrat->QRATA(mem_on, meml);
					Clause mem_parent;// sets meml false if -l1
					mem_parent.addnode(l1);
					mem_parent.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_parent);//RATA on -meml, blocked by -l1 in both clauses
					qrat->QRATA(mem_parent, -meml);
					Clause mem_sel;// sets meml false if selon and -selval
					mem_sel.addnode(-selonl);
					mem_sel.addnode(selvall);
					mem_sel.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_sel);//RATA on -meml, blocked by selonl on mem_on and -selvall in mem_val
					qrat->QRATA(mem_sel, -meml);
					//add equivalence for parent1
				}
				if ((pos0 != -1) && (pos1 == -1)) {
					Lit l0 = Lit(SE->main_index->operator[](level).operator[](parent0).memberships->operator[](pos0).membership);
					//add equivalence for parent0
					Clause mem_val;//sets meml true when -selval and l0
					mem_val.addnode(selvall);
					mem_val.addnode(-l0);
					mem_val.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_val);//RATA on meml, trivial;
					qrat->QRATA(mem_val, meml);
					Clause mem_on;//sets meml true when -selon and l0
					mem_on.addnode(selonl);
					mem_on.addnode(-l0);
					mem_on.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_on);//RATA on meml, trivial;
					qrat->QRATA(mem_on, meml);
					Clause mem_parent;//sets meml false when -l0
					mem_parent.addnode(l0);
					mem_parent.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_parent);//RATA on -meml, blocked by -l0 in both clauses
					qrat->QRATA(mem_parent, -meml);
					Clause mem_sel;//sets meml false when selon and selval
					mem_sel.addnode(-selonl);
					mem_sel.addnode(-selvall);
					mem_sel.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_sel);//RATA on -meml, blocked by selonl on mem_on and -selvall in mem_val
					qrat->QRATA(mem_sel, -meml);
					//add equivalence for parent1

				}
				if ((pos0 != -1) && (pos1 != -1)) {
					Lit l0 = Lit(SE->main_index->operator[](level).operator[](parent0).memberships->operator[](pos0).membership);
					Lit l1 = Lit(SE->main_index->operator[](level).operator[](parent1).memberships->operator[](pos1).membership);
					//disjunctive reasoning except for selon
					Clause mem_val0;//sets meml true when selval=0 and l0
					mem_val0.addnode(selvall);
					mem_val0.addnode(-l0);
					mem_val0.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_val0);//RATA on meml, trivial;
					qrat->QRATA(mem_val0, meml);
					Clause mem_val1;//sets meml true when selval=0  and l1
					mem_val1.addnode(-selvall);
					mem_val1.addnode(-l1);
					mem_val1.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_val1);//RATA on meml, trivial;
					qrat->QRATA(mem_val1, meml);

					Clause mem_off0;//sets meml true when seloff and l0
					mem_off0.addnode(selonl);
					mem_off0.addnode(-l0);
					mem_off0.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_off0);//RATA on meml, trivial;
					qrat->QRATA(mem_off0, meml);

					Clause mem_off1;//sets meml true when seloff and l1
					mem_off1.addnode(selonl);
					mem_off1.addnode(-l1);
					mem_off1.addnode(meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_off1);//RATA on meml, trivial;
					qrat->QRATA(mem_off1, meml);

					Clause mem_parent;//sets meml false when both parents lack it
					mem_parent.addnode(l0);
					mem_parent.addnode(l1);
					mem_parent.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_parent);//RATA on -meml, blocked by -l1 in 1 clause,, blocked by -l0 in 0 clauses
					qrat->QRATA(mem_parent, -meml);

					Clause mem_on0;//sets meml false when l0 false and sel points to it
					mem_on0.addnode(-selonl);
					mem_on0.addnode(selvall);
					mem_on0.addnode(l0);
					mem_on0.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_on0);//RATA on -meml, blocked by selon in off, by selval in val1, by -l0 in val0
					qrat->QRATA(mem_on0, -meml);
					Clause mem_on1;//sets meml false when 10 false and sel points to it
					mem_on1.addnode(-selonl);
					mem_on1.addnode(-selvall);
					mem_on1.addnode(l1);
					mem_on1.addnode(-meml);
					read.memberships->operator[](lit_counter).def_membership->addnode(mem_on1);//RATA on -meml, blocked by selon in off, by selval in val0, by -l1 in val1
					qrat->QRATA(mem_on1, -meml);
				}
				lit_counter++;
				current = current->next;
			}

			//check if present in parent0 and find index
			//check if present in parent1 and find index




		}
		if (L.rule == REDUCTION) {
			int parent = L.parent0;
			Clause P = pi->operator[](parent).clause;
			//taut
			//Lit tautl = Lit(read.tautological);
			//Lit taut_parent = Lit(I->Idx_Proof->operator[](level).operator[](parent).tautological);

			//Clause taut_forward;
			//taut_forward.addnode(-taut_parent);
			//taut_forward.addnode(tautl);
			//read.def_tautological->addnode(taut_forward);//RATA on tautl: trivial
			//qrat->QRATA(taut_forward, tautl);

			//Clause taut_backward;
			//taut_backward.addnode(taut_parent);
			//taut_backward.addnode(-tautl);
			//read.def_tautological->addnode(taut_backward);//RATA on -tautl: -taut_parent blocked;
			//qrat->QRATA(taut_backward, -tautl);

			Link1<Lit>* current = L.clause.head;
			int lit_counter = 0;
			while (current != NULL) {
				Lit l = current->data;
				int pos = find_a_position(l, P);
				Lit meml = Lit(read.memberships->operator[](lit_counter).membership);
				Lit parl = Lit(SE->main_index->operator[](level).operator[](parent).memberships->operator[](pos).membership);
				Clause mem_forward;
				mem_forward.addnode(-parl);
				mem_forward.addnode(meml);
				read.memberships->operator[](lit_counter).def_membership->addnode(mem_forward);//RATA on meml: trivial
				qrat->QRATA(mem_forward, meml);
				Clause mem_backward;
				mem_backward.addnode(parl);
				mem_backward.addnode(-meml);
				read.memberships->operator[](lit_counter).def_membership->addnode(mem_backward);//RATA on meml: -parl blocked
				qrat->QRATA(mem_backward, meml);
				current = current->next;
				lit_counter++;
			}
		}
		//

		return;
	}
	void backdef_cell(Strategy_Extractor* SE, IndexLine cell, int level, int line_no1, int new_sink, LinkL<int>* backwards_list ) {
		ClausalProof* pi = SE->input_proof;
		Prefix P = SE->input_QBF->prefix;
		int line_no2 = new_sink;
		Lit al = Lit(cell.ancestor);
		Line L1 = pi->operator[](line_no1);
		QRAT_Proof* qrat = SE->output_QRAT;
		if (line_no1 >= line_no2) {
			if (line_no1 == line_no2) {
				Clause a_assert;
				a_assert.addnode(al);
				cell.def_ancestor->addnode(a_assert);//RATA on al: trivial
				qrat->QRATA(a_assert, al);
			}
			else{
				Clause n_assert;
				n_assert.addnode(-al);
				cell.def_ancestor->addnode(n_assert);//RATA on al: trivial
				qrat->QRATA(n_assert, al);
			}
		}
		else {

			Clause a_long;
			a_long.addnode(-al);
			Link1<int>* current_int_container = backwards_list->head;
			while (current_int_container!=NULL) {
				int i = current_int_container->data;
				Line L1child = pi->operator[](i);
				if (L1child.rule == REDUCTION) {
					if (L1child.parent0 == line_no1) {
						Lit a_child = Lit(SE->main_index->operator[](level).operator[](i).ancestor);
						a_long.addnode(a_child);
						Clause a_short = Clause();
						a_short.addnode(-a_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
				}
				if (L1child.rule == RESOLUTION) {
					//output->output_cnf->add_comment("ancestor resolution");
					if (L1child.parent0 == line_no1) {
						Lit cond_child = Lit(SE->main_index->operator[](level).operator[](i).xselval0);
						a_long.addnode(cond_child);
						Clause a_short = Clause();
						a_short.addnode(-cond_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
					if (L1child.parent1 == line_no1) {
						Lit cond_child = Lit(SE->main_index->operator[](level).operator[](i).xselval1);
						a_long.addnode(cond_child);
						Clause a_short = Clause();
						a_short.addnode(-cond_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
				}
				current_int_container = current_int_container->next;
			}
			cell.def_ancestor->addnode(a_long);//RATA on -al: blocked on each cond
			qrat->QRATA(a_long, -al);


		}
		if (L1.rule == RESOLUTION) {
			Lit ext0l = Lit(cell.xselval0);
			Lit ext1l = Lit(cell.xselval1);
			Lit selonl = Lit(SE->main_index->operator[](level).operator[](line_no1).selon);
			Lit selvall = Lit(SE->main_index->operator[](level).operator[](line_no1).selval);


			Clause extOFF0;
			extOFF0.addnode(selonl);
			extOFF0.addnode(-al);
			extOFF0.addnode(ext0l);
			cell.def_xselval0->addnode(extOFF0);//RATA on ext0l: trivial
			qrat->QRATA(extOFF0, ext0l);

			Clause extval0;
			extval0.addnode(selvall);
			extval0.addnode(-al);
			extval0.addnode(ext0l);
			cell.def_xselval0->addnode(extval0);//RATA on ext0l: trivial
			qrat->QRATA(extval0, ext0l);

			Clause extanc0;
			extanc0.addnode(al);
			extanc0.addnode(-ext0l);
			cell.def_xselval0->addnode(extanc0);//RATA on -ext0l: blocked on -al
			qrat->QRATA(extanc0, -ext0l);

			Clause extsel0;
			extsel0.addnode(-selonl);
			extsel0.addnode(-selvall);
			extsel0.addnode(-ext0l);
			cell.def_xselval0->addnode(extsel0);//RATA on -ext0l: blocked on selonl, blocked on selvall
			qrat->QRATA(extsel0, -ext0l);

			Clause extOFF1;
			extOFF1.addnode(selonl);
			extOFF1.addnode(-al);
			extOFF1.addnode(ext1l);
			cell.def_xselval1->addnode(extOFF1);//RATA on ext1l: trivial
			qrat->QRATA(extOFF1, ext1l);

			Clause extval1;
			extval1.addnode(-selvall);
			extval1.addnode(-al);
			extval1.addnode(ext1l);
			cell.def_xselval1->addnode(extval1);//RATA on ext1l: trivial
			qrat->QRATA(extval1, ext1l);

			Clause extanc1;
			extanc1.addnode(al);
			extanc1.addnode(-ext1l);
			cell.def_xselval1->addnode(extanc1);//RATA on -ext1l: blocked on al
			qrat->QRATA(extanc1, -ext1l);

			Clause extsel1;
			extsel1.addnode(-selonl);
			extsel1.addnode(selvall);
			extsel1.addnode(-ext1l);
			cell.def_xselval1->addnode(extsel1);//RATA on -ext1l: blocked on selonl, blocked on -selvall
			qrat->QRATA(extsel1, -ext1l);
		}
	}

	void backdef_cell(Strategy_Extractor* SE, IndexLine cell , int level, int line_no1) {
		ClausalProof* pi = SE->input_proof;
		Prefix P = SE->input_QBF->prefix;
		int line_no2 = pi->tail->position;
		Lit al = Lit(cell.ancestor);
		Line L1 = pi->operator[](line_no1);
		QRAT_Proof* qrat = SE->output_QRAT;
		if (line_no1 == line_no2) {
			Clause a_assert;
			a_assert.addnode(al);
			cell.def_ancestor->addnode(a_assert);//RATA on al: trivial
			qrat->QRATA(a_assert, al);
		}
		else {

			Clause a_long;
			a_long.addnode(-al);
			for (int i = line_no1 + 1; i <= line_no2; i++) {
				Line L1child = pi->operator[](i);
				if (L1child.rule == REDUCTION) {
					if (L1child.parent0 == line_no1) {
						Lit a_child = Lit(SE->main_index->operator[](level).operator[](i).ancestor);
						a_long.addnode(a_child);
						Clause a_short = Clause();
						a_short.addnode(-a_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
				}
				if (L1child.rule == RESOLUTION) {
					//output->output_cnf->add_comment("ancestor resolution");
					if (L1child.parent0 == line_no1) {
						Lit cond_child = Lit(SE->main_index->operator[](level).operator[](i).xselval0);
						a_long.addnode(cond_child);
						Clause a_short = Clause();
						a_short.addnode(-cond_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
					if (L1child.parent1 == line_no1) {
						Lit cond_child = Lit(SE->main_index->operator[](level).operator[](i).xselval1);
						a_long.addnode(cond_child);
						Clause a_short = Clause();
						a_short.addnode(-cond_child);
						a_short.addnode(al);
						cell.def_ancestor->addnode(a_short);//RATA on al: trivial
						qrat->QRATA(a_short, al);
					}
				}
			}
			cell.def_ancestor->addnode(a_long);//RATA on -al: blocked on each cond
			qrat->QRATA(a_long, -al);


		}
		if (L1.rule == RESOLUTION) {
			Lit ext0l = Lit(cell.xselval0);
			Lit ext1l = Lit(cell.xselval1);
			Lit selonl = Lit(SE->main_index->operator[](level).operator[](line_no1).selon);
			Lit selvall = Lit(SE->main_index->operator[](level).operator[](line_no1).selval);


			Clause extOFF0;
			extOFF0.addnode(selonl);
			extOFF0.addnode(-al);
			extOFF0.addnode(ext0l);
			cell.def_xselval0->addnode(extOFF0);//RATA on ext0l: trivial
			qrat->QRATA(extOFF0, ext0l);

			Clause extval0;
			extval0.addnode(selvall);
			extval0.addnode(-al);
			extval0.addnode(ext0l);
			cell.def_xselval0->addnode(extval0);//RATA on ext0l: trivial
			qrat->QRATA(extval0, ext0l);

			Clause extanc0;
			extanc0.addnode(al);
			extanc0.addnode(-ext0l);
			cell.def_xselval0->addnode(extanc0);//RATA on -ext0l: blocked on -al
			qrat->QRATA(extanc0, -ext0l);

			Clause extsel0;
			extsel0.addnode(-selonl);
			extsel0.addnode(-selvall);
			extsel0.addnode(-ext0l);
			cell.def_xselval0->addnode(extsel0);//RATA on -ext0l: blocked on selonl, blocked on selvall
			qrat->QRATA(extsel0, -ext0l);

			Clause extOFF1;
			extOFF1.addnode(selonl);
			extOFF1.addnode(-al);
			extOFF1.addnode(ext1l);
			cell.def_xselval1->addnode(extOFF1);//RATA on ext1l: trivial
			qrat->QRATA(extOFF1, ext1l);

			Clause extval1;
			extval1.addnode(-selvall);
			extval1.addnode(-al);
			extval1.addnode(ext1l);
			cell.def_xselval1->addnode(extval1);//RATA on ext1l: trivial
			qrat->QRATA(extval1, ext1l);

			Clause extanc1;
			extanc1.addnode(al);
			extanc1.addnode(-ext1l);
			cell.def_xselval1->addnode(extanc1);//RATA on -ext1l: blocked on al
			qrat->QRATA(extanc1, -ext1l);

			Clause extsel1;
			extsel1.addnode(-selonl);
			extsel1.addnode(selvall);
			extsel1.addnode(-ext1l);
			cell.def_xselval1->addnode(extsel1);//RATA on -ext1l: blocked on selonl, blocked on -selvall
			qrat->QRATA(extsel1, -ext1l);
		}

	}


	void def_layer(Strategy_Extractor* SE, LinkL<LinkL<IndexLine> >* idx_proof, Prefix P, ClausalProof* pi, int level, int new_sink, LinkL<int>* backwards_list) {// gives every extension variable a number
		LinkL<IndexLine>* read = &SE->main_index->findnode(level)->data;
		Link1<IndexLine>* current = read->head;
		int botpos = pi->tail->position;
		int line_no = 0;
		while (current != NULL) {//cycles through all lines
			def_line(SE, current->data, level, line_no);
			current = current->next;
			line_no++;
		}
		current = read->tail;
		line_no = botpos;// start at end for backwards definitions (ancestors)
		while (current != NULL) {//cycles through all lines
			backdef_cell(SE, current->data, level, line_no, new_sink, backwards_list);
			current = current->prev;
			line_no--;
		}
		//idx_proof->addnode(*temp);
		return;
	};

	void def_layer(Strategy_Extractor* SE, LinkL<LinkL<IndexLine> >* idx_proof, Prefix P, ClausalProof* pi, int level) {
		LinkL<IndexLine>* read = &SE->main_index->findnode(level)->data;
		Link1<IndexLine>* current = read->head;
		int botpos = pi->tail->position;
		int line_no = 0;
		while (current != NULL) {//cycles through all lines
			def_line(SE, current->data, level, line_no);
			current = current->next;
			line_no++;
		}
		current = read->tail;
		line_no = botpos;
		while (current != NULL) {//cycles through all lines
			backdef_cell(SE, current->data, level, line_no);
			current = current->prev;
			line_no--;
		}
		//idx_proof->addnode(*temp);
		return;
	};

	void MemberCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no, int position);

	void SelonCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no) {
		IndexLine* lineidx = &SE->main_index->operator[](level).findnode(line_no)->data;
		ClausalProof* pi = SE->input_proof;
		Line L = pi->operator[](line_no);
		if (lineidx->is_selon_defined == 0) {
			lineidx->is_selon_defined = 1;
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no);
			layer2->data.is_selon_defined = 1;
			MemberCnfLoad(output, SE, level, L.parent0, L.litpos0);
			MemberCnfLoad(output, SE, level, L.parent1, L.litpos1);
			if (level > 0) {
				SelonCnfLoad(output, SE, level - 1, line_no);

			}
			copyinto(output, lineidx->def_selon);
		}
	}

	void Seq_SelonCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no) {
		IndexLine* lineidx = &SE->main_index->operator[](level).findnode(line_no)->data;
		ClausalProof* pi = SE->input_proof;
		Line L = pi->operator[](line_no);
		if (lineidx->is_selon_defined == 0) {
			lineidx->is_selon_defined = 1;
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no);
			layer2->data.is_selon_defined = 1;
			//MemberCnfLoad(output, SE, level, L.parent0, L.litpos0);
			//MemberCnfLoad(output, SE, level, L.parent1, L.litpos1);
			if (level > 0) {
				//SelonCnfLoad(output, SE, level - 1, line_no);

			}
			copyinto(output, lineidx->def_selon);
		}
	}


	void SelvalCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no) {
		IndexLine lineidx = SE->main_index->operator[](level).operator[](line_no);
		ClausalProof* pi = SE->input_proof;
		Line L = pi->operator[](line_no);
		if (lineidx.is_selval_defined == 0) {
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no);
			layer2->data.is_selval_defined = 1;
			MemberCnfLoad(output, SE, level, L.parent0, L.litpos0);
			MemberCnfLoad(output, SE, level, L.parent1, L.litpos1);
			if (level > 0) {
				SelonCnfLoad(output, SE, level - 1, line_no);
				SelvalCnfLoad(output, SE, level - 1, line_no);

			}
			copyinto(output, lineidx.def_selval);
		}
	}

	void Seq_SelvalCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no) {
		IndexLine lineidx = SE->main_index->operator[](level).operator[](line_no);
		ClausalProof* pi = SE->input_proof;
		Line L = pi->operator[](line_no);
		if (lineidx.is_selval_defined == 0) {
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no);
			layer2->data.is_selval_defined = 1;
			//MemberCnfLoad(output, SE, level, L.parent0, L.litpos0);
			//MemberCnfLoad(output, SE, level, L.parent1, L.litpos1);
			if (level > 0) {
				//SelonCnfLoad(output, SE, level - 1, line_no);
				//SelvalCnfLoad(output, SE, level - 1, line_no);

			}
			copyinto(output, lineidx.def_selval);
		}
	}

	void MemberCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no, int position) {
		ClausalProof* pi = SE->input_proof;
		Prefix P = SE->input_QBF->prefix;
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		Lit l = C.operator[](position);
		IndexLine* lineidx = &SE->main_index->operator[](level).findnode(line_no)->data;
		IndexLit* memidx = &(lineidx->memberships->findnode(position)->data);
		if (memidx->is_membership_defined == 0) {
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no);
			Link1<IndexLit>* layer3 = layer2->data.memberships->findnode(position);
			layer3->data.is_membership_defined = 1;
			if (L.rule == AXIOM) {
				//if (P.lvl(C.operator[](position).var)< level) {}
				//else {}


			}
			if (L.rule == REDUCTION) {
				Line<Clause> L0 = pi->operator[](L.parent0);
				Clause P0 = L0.clause;
				int pos0 = find_a_position(l, P0);
				MemberCnfLoad(output, SE, level, L.parent0, pos0);

			}
			if (L.rule == RESOLUTION) {
				Line<Clause> L0 = pi->operator[](L.parent0);
				Clause P0 = L0.clause;
				int pos0 = find_a_position(l, P0);
				Line<Clause> L1 = pi->operator[](L.parent1);
				Clause P1 = L1.clause;
				int pos1 = find_a_position(l, P1);
				SelonCnfLoad(output, SE, level, line_no);
				SelvalCnfLoad(output, SE, level, line_no);
				if (pos0 != -1) {
					MemberCnfLoad(output, SE, level, L.parent0, pos0);
				}
				if (pos1 != -1) {
					MemberCnfLoad(output, SE, level, L.parent1, pos1);
				}
			}
			copyinto(output, memidx->def_membership);
		}

	}

	void Seq_MemberCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no, int position) {
		ClausalProof* pi = SE->input_proof;
		Prefix P = SE->input_QBF->prefix;
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		Lit l = C.operator[](position);
		IndexLine* lineidx = &SE->main_index->operator[](level).findnode(line_no)->data;
		IndexLit* memidx = &(lineidx->memberships->findnode(position)->data);
		if (memidx->is_membership_defined == 0) {
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no);
			Link1<IndexLit>* layer3 = layer2->data.memberships->findnode(position);
			layer3->data.is_membership_defined = 1;
			if (L.rule == AXIOM) {
				//if (P.lvl(C.operator[](position).var)< level) {}
				//else {}


			}
			if (L.rule == REDUCTION) {
				Line<Clause> L0 = pi->operator[](L.parent0);
				Clause P0 = L0.clause;
				int pos0 = find_a_position(l, P0);
				//MemberCnfLoad(output, SE, level, L.parent0, pos0);

			}
			if (L.rule == RESOLUTION) {
				Line<Clause> L0 = pi->operator[](L.parent0);
				Clause P0 = L0.clause;
				int pos0 = find_a_position(l, P0);
				Line<Clause> L1 = pi->operator[](L.parent1);
				Clause P1 = L1.clause;
				int pos1 = find_a_position(l, P1);
				//SelonCnfLoad(output, SE, level, line_no);
				//SelvalCnfLoad(output, SE, level, line_no);
				if (pos0 != -1) {
					//MemberCnfLoad(output, SE, level, L.parent0, pos0);
				}
				if (pos1 != -1) {
					//MemberCnfLoad(output, SE, level, L.parent1, pos1);
				}
			}
			copyinto(output, memidx->def_membership);
		}

	}

	void ConnCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no1);

	void XSelCnfLoad(bool val, Cnf* output, Strategy_Extractor* SE, int level, int line_no1) {
		IndexLine* cell = &SE->main_index->operator[](level).findnode(line_no1)->data;
		ClausalProof* pi = SE->input_proof;
		Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
		Link1<IndexLine>* layer2 = layer1->data.findnode(line_no1);
		if (val) {
			if (cell->is_xselval1_defined == 0) {
				layer2->data.is_xselval1_defined = 1;
				ConnCnfLoad(output, SE, level, line_no1);
				SelonCnfLoad(output, SE, level, line_no1);
				SelvalCnfLoad(output, SE, level, line_no1);
				copyinto(output, cell->def_xselval1);

			}
		}
		else {
			if (cell->is_xselval0_defined == 0) {
				layer2->data.is_xselval0_defined = 1;
				ConnCnfLoad(output, SE, level, line_no1);
				SelonCnfLoad(output, SE, level, line_no1);
				SelvalCnfLoad(output, SE, level, line_no1);
				copyinto(output, cell->def_xselval0);
			}
		}
	}

	void Seq_XSelCnfLoad(bool val, Cnf* output, Strategy_Extractor* SE, int level, int line_no1) {
		IndexLine* cell = &SE->main_index->operator[](level).findnode(line_no1)->data;
		ClausalProof* pi = SE->input_proof;
		Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
		Link1<IndexLine>* layer2 = layer1->data.findnode(line_no1);
		if (val) {
			if (cell->is_xselval1_defined == 0) {
				layer2->data.is_xselval1_defined = 1;
				//ConnCnfLoad(output, SE, level, line_no1);
				//SelonCnfLoad(output, SE, level, line_no1);
				//SelvalCnfLoad(output, SE, level, line_no1);
				copyinto(output, cell->def_xselval1);

			}
		}
		else {
			if (cell->is_xselval0_defined == 0) {
				layer2->data.is_xselval0_defined = 1;
				//ConnCnfLoad(output, SE, level, line_no1);
				//SelonCnfLoad(output, SE, level, line_no1);
				//SelvalCnfLoad(output, SE, level, line_no1);
				copyinto(output, cell->def_xselval0);
			}
		}
	}

	void ConnCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no1) {
		IndexLine cell = SE->main_index->operator[](level).operator[](line_no1);
		if (cell.is_ancestor_defined == 0) {
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no1);
			layer2->data.is_ancestor_defined = 1;
			ClausalProof* pi = SE->input_proof;
			int line_no2 = pi->tail->position;
			if (line_no1 == line_no2) {
			}
			else {
				for (int i = line_no1 + 1; i <= line_no2; i++) {
					Line L1child = pi->operator[](i);
					if (L1child.rule == REDUCTION) {
						if (L1child.parent0 == line_no1) {
							ConnCnfLoad(output, SE, level, i);
						}
					}
					if (L1child.rule == RESOLUTION) {
						if (L1child.parent0 == line_no1) {
							XSelCnfLoad(0, output, SE, level, i);
						}
						if (L1child.parent1 == line_no1) {
							XSelCnfLoad(1, output, SE, level, i);
						}
					}
				}

			}
			copyinto(output, cell.def_ancestor);
		}
	}

	void Seq_ConnCnfLoad(Cnf* output, Strategy_Extractor* SE, int level, int line_no1) {
		IndexLine cell = SE->main_index->operator[](level).operator[](line_no1);
		if (cell.is_ancestor_defined == 0) {
			Link1<LinkL<IndexLine>>* layer1 = SE->main_index->findnode(level);
			Link1<IndexLine>* layer2 = layer1->data.findnode(line_no1);
			layer2->data.is_ancestor_defined = 1;
			ClausalProof* pi = SE->input_proof;
			int line_no2 = pi->tail->position;
			if (line_no1 == line_no2) {
			}
			else {
				for (int i = line_no1 + 1; i <= line_no2; i++) {
					Line L1child = pi->operator[](i);
					if (L1child.rule == REDUCTION) {
						if (L1child.parent0 == line_no1) {
							//ConnCnfLoad(output, SE, level, i);
						}
					}
					if (L1child.rule == RESOLUTION) {
						if (L1child.parent0 == line_no1) {
							//XSelCnfLoad(0, output, SE, level, i);
						}
						if (L1child.parent1 == line_no1) {
							//XSelCnfLoad(1, output, SE, level, i);
						}
					}
				}

			}
			copyinto(output, cell.def_ancestor);
		}
	}

	void StrategyCnfLoad(Cnf* output, Strategy_Extractor* SE, Var u) {
		//StrategyCnfLoad
		Link1<IndexStrat>* current_u = SE->strategy_index->head;
		while (current_u != NULL) {
			if (current_u->data.u == u) {
				if (current_u->data.is_strategy_defined == 0) {
					current_u->data.is_strategy_defined = 1;
					Link1<int>* current_line = current_u->data.axioms->head;
					while (current_line != NULL) {
						int level = SE->input_QBF->prefix.lvl(u) - 1;
						int axpos = current_line->data;
						//int botpos = SE->input_proof->tail->position;
						ConnCnfLoad(output, SE, level, axpos);
						current_line = current_line->next;
					}

					copyinto(output, current_u->data.def_strategy);
				}
			}
			current_u = current_u->next;

		}


	}

	void Seq_StrategyCnfLoad(Cnf* output, Strategy_Extractor* SE, Var u) {
		//StrategyCnfLoad
		Link1<IndexStrat>* current_u = SE->strategy_index->head;
		while (current_u != NULL) {
			if (current_u->data.u == u) {
				if (current_u->data.is_strategy_defined == 0) {
					current_u->data.is_strategy_defined = 1;
					Link1<int>* current_line = current_u->data.axioms->head;
					while (current_line != NULL) {
						int level = SE->input_QBF->prefix.lvl(u) - 1;
						int axpos = current_line->data;
						//int botpos = SE->input_proof->tail->position;
						//ConnCnfLoad(output, SE, level, axpos);
						current_line = current_line->next;
					}

					copyinto(output, current_u->data.def_strategy);
				}
			}
			current_u = current_u->next;

		}


	}

	LinkL<int>* connectedlines(ClausalProof* proof_address, int a_base) {//Adds the line_no of connected lines in reverse,
		//this is not for the dependent connectivity of the levels, but just to get proofs a bit more compact
		LinkL<int>* connected_lines = new LinkL<int>;
		connected_lines->addnode(a_base);
		Link1<int>* current = connected_lines->head;// current checks all the lines
		while (current != NULL) {//finishes loop when reaching past any unparented items, no need to restart
			int parent0 = proof_address->operator[](current->data).parent0; 
			if (parent0 > -1) {//if parent0 is defined
				bool is_repeat = 0;
				Link1<int>* current2 = connected_lines->head;// current2 checks for repeats
				while (current2 != NULL) {

					if (current2->data == parent0) {
						is_repeat = 1;
					}
					current2 = current2->next;
				}
				if (!is_repeat) {
					connected_lines->addnode(parent0);// we add a parent0 to the end of the list if it isn't a repeat of the list
				}
			}
			int parent1 = proof_address->operator[](current->data).parent1;
			if (parent1 > -1) {//if parent1 is defined
				bool is_repeat = 0;
				Link1<int>* current2 = connected_lines->head;// current2 checks for repeats
				while (current2 != NULL) {

					if (current2->data == parent1) {
						is_repeat = 1;
					}
					current2 = current2->next;
				}
				if (!is_repeat) {
					connected_lines->addnode(parent1);// we add a parent1 to the end of the list  if it isn't a repeat of the list
				}
			}
			current = current->next;
		}
		return connected_lines;
	}

	void while_load(Cnf* output, Strategy_Extractor* SE, int a_base, int i, LinkL<int>* connected_lines) {

		//connected_lines->addnode(a_base);
		ClausalProof* proof_address = SE->input_proof;
		// = connectedlines(proof_address, a_base);
		Link1<int>* current = connected_lines->head;


		int max_lvl = SE->input_QBF->prefix.tail->data.level;
			current = connected_lines->tail;
			while (current != NULL) {
				//load all clauses systematically
				IndexLine lineindex = SE->main_index->operator[](i).operator[](current->data);
				Line<Clause> currline= SE->input_proof->operator[](current->data);
				std::string title = "Defining restricted proof line:" + std::to_string(current->data + 1) + " lvl:" + std::to_string(i) + " type:" + currline.rule.str();
				output->add_comment(title);
				if (currline.rule.arity > 0) {
					std::string subtitle = "P0 line_no: " + std::to_string(currline.parent0+1);
					if (currline.rule.arity > 1) {
						subtitle = subtitle + ", P1 line_no: " + std::to_string(currline.parent1+1);
					}
					output->add_comment(subtitle);
				}
				if (currline.rule == RESOLUTION) {
					std::string str_selon = "selon:" + std::to_string(lineindex.selon);
					output->add_comment(str_selon);
					copyinto(output, lineindex.def_selon);
					std::string str_selval = "selval:" + std::to_string(lineindex.selval);
					output->add_comment(str_selval);
					copyinto(output, lineindex.def_selval);

				}
				output->add_comment("membership:");
				Link1<IndexLit>* litindex = lineindex.memberships->head;
				while (litindex != NULL) {
					std::string str_mem = std::to_string(litindex->data.membership) + ":= [" + std::to_string(litindex->data.lit.DIMACS()) +" in "+ SE->input_proof->operator[](current->data).clause.str() + "^" + std::to_string(i) + "]";
					output->add_comment(str_mem);
					copyinto(output, litindex->data.def_membership);
					litindex = litindex->next;
				}

				current = current->prev;
			}
			current = connected_lines->head;
			while (current != NULL) {
				
				IndexLine lineindex = SE->main_index->operator[](i).operator[](current->data);
				Line<Clause> a_baseline = SE->input_proof->operator[](a_base);
				Line<Clause> currline = SE->input_proof->operator[](current->data);
				std::string str_anctitle = "Defining connectivity from ancestor base to line" + std::to_string(current->data+1)+" type:"+ currline.rule.str();
				output->add_comment(str_anctitle);
				std::string str_anc = "anc^" + std::to_string(i) + "_{" + currline.clause.str() + ","+ a_baseline.clause.str() + "}: "+ std::to_string(lineindex.ancestor);
				output->add_comment(str_anc);
				copyinto(output, lineindex.def_ancestor);
				if (currline.rule == RESOLUTION) {
					std::string str_ex0 = "exselval0:"+ std::to_string(lineindex.xselval0);
					output->add_comment(str_ex0);
					copyinto(output, lineindex.def_xselval0);
					std::string str_ex1 = "exselval1:" + std::to_string(lineindex.xselval1);
					output->add_comment(str_ex1);
					copyinto(output, lineindex.def_xselval1);
				}
				current = current->next;
			}
		return;
	}

	void while_load(Cnf* output, Strategy_Extractor* SE, int a_base) {
		//connected_lines->addnode(a_base);
		ClausalProof* proof_address = SE->input_proof;
		LinkL<int>* connected_lines = connectedlines(proof_address, a_base);
		Link1<int>* current = connected_lines->head;

		
		int max_lvl = SE->input_QBF->prefix.tail->data.level;
		for (int i = 0; i <= max_lvl; i++) {
			current = connected_lines->tail;
			while (current != NULL) {
				//load all clauses systematically
				IndexLine lineindex = SE->main_index->operator[](i).operator[](current->data);
				SE->output_cnf->add_comment("Defining restricted proof line:");
				SE->output_cnf->add_comment("selon:");
				copyinto(output, lineindex.def_selon);
				SE->output_cnf->add_comment("selval:");
				copyinto(output, lineindex.def_selval);
				
				SE->output_cnf->add_comment("membership:");
				Link1<IndexLit>* litindex = lineindex.memberships->head;
				while (litindex!=NULL) {
						copyinto(output, litindex->data.def_membership);
					litindex = litindex->next;
				}
				
				current = current->prev;
			}
			current = connected_lines->head;
			while (current != NULL) {
				SE->output_cnf->add_comment("Defining connectivity from a_base");
				IndexLine lineindex = SE->main_index->operator[](i).operator[](current->data);
				SE->output_cnf->add_comment("anc:");
				copyinto(output, lineindex.def_ancestor);
				SE->output_cnf->add_comment("exselval0:");
				copyinto(output, lineindex.def_xselval0);
				SE->output_cnf->add_comment("exselval1:");
				copyinto(output, lineindex.def_xselval1);
				current = current->next;
			}
		}
		return;
	}

	void def_universal(Strategy_Extractor* SE, LinkL <IndexStrat>* idx_strat, Var u, int a_base, bool is_unsat) {//version for a_base
		Link1<IndexStrat>* current_u = idx_strat->head;
		Prefix P = SE->input_QBF->prefix;
		ClausalProof* pi = SE->input_proof;
		QRAT_Proof* qrat = SE->output_QRAT;
		while (current_u != NULL) {
			if (current_u->data.u == u) {
				SE->extension_clauses->add_comment("Strategy clauses:");
				qrat->add_comment("Strategy clauses:");
				int level = P.lvl(u) - 1;
				Link1<int>* current_line = current_u->data.axioms->head;
				Lit ul = Lit(current_u->data.strategy);
				Clause stratlong;
				stratlong.addnode(ul);
				while (current_line != NULL) {
					int axpos = current_line->data;
					int upos = find_a_position(Lit(u), pi->operator[](axpos).clause);
					int botpos = a_base;
					Lit conn = Lit(SE->main_index->operator[](level).operator[](axpos).ancestor);
					Clause stratshort;
					stratshort.addnode(-conn);
					stratshort.addnode(-ul);
					current_u->data.def_strategy->addnode(stratshort);//RATA on -ul; trivial
					qrat->QRATA(stratshort, -ul);
					stratlong.addnode(conn);

					current_line = current_line->next;
				}
				current_u->data.def_strategy->addnode(stratlong);//RATA on ul; each blocked on ex;
				qrat->QRATA(stratlong, ul, "Long Strategy Clause");
				//clauses not destined for qrat, only for propositional checks
				//output->output_cnf->add_comment("equivalence clauses for universal");
				copyinto(SE->extension_clauses, current_u->data.def_strategy);
				Clause uforward;
				uforward.addnode(-ul);
				uforward.addnode(Lit(u));
				SE->negated_assumptions->addnode(uforward);//not acceptable in QRAT
				Clause ubackward;
				ubackward.addnode(ul);
				ubackward.addnode(-Lit(u));
				SE->negated_assumptions->addnode(ubackward);//not acceptable in QRAT
			}
			current_u = current_u->next;
		}
	}

	void def_universal(Strategy_Extractor* SE, LinkL <IndexStrat>* idx_strat,  Var u) {
		Link1<IndexStrat>* current_u = idx_strat->head;
		Prefix P = SE->input_QBF->prefix;
		ClausalProof* pi = SE->input_proof;
		QRAT_Proof* qrat = SE->output_QRAT;
		while (current_u != NULL) {
			if (current_u->data.u == u) {
				SE->output_cnf->add_comment("Strategy clauses:");
				qrat->add_comment("Strategy clauses:");
				int level = P.lvl(u) - 1;
				Link1<int>* current_line = current_u->data.axioms->head;
				Lit ul = Lit(current_u->data.strategy);
				Clause stratlong;
				stratlong.addnode(ul);
				while (current_line != NULL) {
					//define 

					int axpos = current_line->data;
					int upos = find_a_position(Lit(u), pi->operator[](axpos).clause);
					int botpos = pi->tail->position;
					Lit conn = Lit(SE->main_index->operator[](level).operator[](axpos).ancestor);
					//Lit uinA = Lit(I->Idx_Proof->operator[](level).operator[](axpos).memberships->operator[](upos).membership);
					//Lit ex = Lit(current_line->data.xmembership);
					/*
					Clause xdisjunct;
					xdisjunct.addnode(-conn);
					xdisjunct.addnode(-uinA);
					xdisjunct.addnode(-ex);
					output->output_cnf->addnode(xdisjunct);//RATA on -ex; trivial
					qrat->QRATA(xdisjunct, -ex);
					Clause xconn;
					xconn.addnode(conn);
					xconn.addnode(ex);
					output->output_cnf->addnode(xconn);//RATA on ex; blocked on -conn
					qrat->QRATA(xconn, ex);
					Clause xuinA;
					xuinA.addnode(uinA);
					xuinA.addnode(ex);
					output->output_cnf->addnode(xuinA);//RATA on ex; blocked on uinA
					qrat->QRATA(xuinA, ex);
					*/
					Clause stratshort;
					stratshort.addnode(-conn);
					stratshort.addnode(-ul);
					current_u->data.def_strategy->addnode(stratshort);//RATA on -ul; trivial
					qrat->QRATA(stratshort, -ul);
					stratlong.addnode(conn);

					current_line = current_line->next;
				}
				current_u->data.def_strategy->addnode(stratlong);//RATA on ul; each blocked on ex;
				qrat->QRATA(stratlong, ul, "Long Strategy Clause");
				//clauses not destined for qrat, only for propositional checks
				//output->output_cnf->add_comment("equivalence clauses for universal");
				Clause uforward;
				uforward.addnode(-ul);
				uforward.addnode(Lit(u));
				SE->output_cnf->addnode(uforward);//not acceptable in QRAT
				Clause ubackward;
				ubackward.addnode(ul);
				ubackward.addnode(-Lit(u));
				SE->output_cnf->addnode(ubackward);//not acceptable in QRAT

				StrategyCnfLoad(SE->output_cnf, SE, u);

			}
			current_u = current_u->next;
		}

	}


	bool is_last_universal(Link1<Quantifier>* inputQ) {
		if (inputQ==NULL) {
			return 0;
		}
		if (inputQ->data.is_universal==0) {
			return 0;
		}

		Link1<Quantifier>* currentQ = inputQ->next;
		while (currentQ!=NULL) {
			if (currentQ->data.is_universal == 1) {
				return 0;
			}
			currentQ = currentQ->next;
		}
		return 1;
	}

	void negatebase(Cnf* output, Strategy_Extractor* SE, int a_base, bool is_unsat) {
		if (is_unsat) {
			ClausalProof* proof = SE->input_proof;
			Clause clause = proof->operator[](a_base).clause;
			Link1<Lit>* current = clause.head;
			while (current != NULL) {
				Lit l = current->data;
				Clause unit;
				unit.addnode(-l);
				output->addnode(unit);
				current = current->next;
			}
		}
		return;
	}

	Strategy_Extractor* Extract(QCNF* phi, ClausalProof* pi, int a_base, bool is_unsat) {//copy for a_base inclusion, also attempts to avoid stack overflow
		// a_base is for local strategies, so default is usually the line number of the empty clause
		Strategy_Extractor* output = new Strategy_Extractor(phi, pi);
		//*(output->output_cnf) = copy(phi->matrix);
		output->main_index = new LinkL<LinkL<IndexLine>>;
		output->strategy_index = new LinkL<IndexStrat>;
		int max_var = output->base_max_var;//initialised to match the QBF's max variable
		Link1<Quantifier>* currentQ = phi->prefix.head;//start defined things from the outside in
		int layer_level = 0;// level 0 is the proof without restriction
		LinkL<int>* backwards_list = connectedlines(pi, a_base);
		//loads for connected lines only, but definitions and indexes for all lines 
		// add to create numerical names, def to create extension clauses in the indexes and load to add them in order to the big cnf
		max_var = add_layer(max_var, output->main_index, output->long_prefix, pi);
		def_layer(output, output->main_index, output->input_QBF->prefix, pi, layer_level, a_base, backwards_list);
		while_load(output->extension_clauses, output, a_base, layer_level, backwards_list);
		while (currentQ != NULL) {
			if (currentQ->data.is_universal) {// add strategy
				max_var = add_universal(max_var, output->strategy_index, output->long_prefix, pi, currentQ->data.var);
				def_universal(output, output->strategy_index, currentQ->data.var, a_base, is_unsat);
				/*
				if (is_last_universal(currentQ)) {
					negatebase(output->negated_assumptions, output, a_base, is_unsat);
					output->idx_max_var = max_var;
					return output;
				}

				*/
				//look ahead for any more universals
				//while loop for 
				//
			}
			//add the base variables to long_prefix, all variables here are added in order
			if (currentQ->data.is_universal) {
				output->long_prefix->addvar(-currentQ->data.var);
			}
			else {
				output->long_prefix->addvar(currentQ->data.var);
			}
			//detecting if at the end of a block
			bool is_next_quant_a_change = 1;
			if (currentQ->next != NULL) {

				if (currentQ->next->data.is_universal == currentQ->data.is_universal) {
					is_next_quant_a_change = 0;
				}
			}

			if (is_next_quant_a_change) {// add restricted proof of at the end of the block
				layer_level++;
				// add to create numerical names, def to create extension clauses in the indexes and load to add them in order to the big cnf
				max_var = add_layer(max_var, output->main_index, output->long_prefix, pi);
				def_layer(output, output->main_index, output->input_QBF->prefix, pi, layer_level, a_base, backwards_list);
				while_load(output->extension_clauses, output, a_base, layer_level, backwards_list);
			}
				currentQ = currentQ->next;
		}

		negatebase(output->negated_assumptions, output, a_base, is_unsat);
		output->idx_max_var = max_var;
		return output;
	}

	



	Strategy_Extractor* Extract(QCNF* phi, ClausalProof* pi) {
		Strategy_Extractor* output = new Strategy_Extractor(phi, pi);
		*(output->output_cnf) = ccopy(phi->matrix);
		output->main_index = new LinkL<LinkL<IndexLine>>;
		output->strategy_index = new LinkL<IndexStrat>;
		int max_var = output->base_max_var;
		Link1<Quantifier>* currentQ = phi->prefix.head;
		//zeroeth level
		//create a layer (<LinkL<Index1>) for Idx_Proof
			//create lines (<Index1>) for the layer
				//create idx 1_1 for the lines
				//add each idx 1_1 addnode()
			//add each line
		//add each layer
		int layer_level = 0;
		max_var = add_layer(max_var, output->main_index, output->long_prefix, pi);
		def_layer(output, output->main_index, output->input_QBF->prefix, pi, layer_level);
		//add_layer1 but for definition clauses
		//max_var = add_array2(max_var, output->main_index->Idx_Conn, output->main_index->idx_prefix, pi);
		//def_array2(output->main_index, output, output->main_index->Idx_Conn, phi->prefix, pi, layer_level);

		//add_array2 but for definition clauses
		while (currentQ != NULL) {
			if (currentQ->data.is_universal) {// add strategy
				max_var = add_universal(max_var, output->strategy_index, output->long_prefix, pi, currentQ->data.var);
				def_universal (output, output->strategy_index, currentQ->data.var);
				//while loop for 

			}


			//add the base variables to idx_prefix
			if (currentQ->data.is_universal) {
				output->long_prefix->addvar(-currentQ->data.var);
			}
			else {
				output->long_prefix->addvar(currentQ->data.var);
			}
			bool is_next_quant_a_change = 1;
			if (currentQ->next != NULL) {

				if (currentQ->next->data.is_universal == currentQ->data.is_universal) {
					is_next_quant_a_change = 0;
				}
			}

			if (is_next_quant_a_change) {// add restricted proof
				layer_level++;
				max_var = add_layer(max_var, output->main_index, output->long_prefix, pi);
				def_layer(output, output->main_index, output->input_QBF->prefix, pi, layer_level);
			}
			currentQ = currentQ->next;
		}
		output->idx_max_var = max_var;
		return output;
	}


	Cnf* StrategyCnf(const char* formulaname, const char* proofname) {
		FILE* qdimacs = fopen(formulaname, "r");
		QCNF formula = read_qdimacs(qdimacs);
		fclose(qdimacs);
		
		FILE* qrc = fopen(proofname, "r");
		ClausalProof proof = read_qrp(qrc);
		fclose(qrc);

		Strategy_Extractor* ClausalExtractor = Extract(&formula, &proof);
		return ClausalExtractor->output_cnf;
	}
}