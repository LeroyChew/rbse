#pragma once
#include "QRAT.h"
#include "File.h"
#include "Exp.h"
#include "Circuits.h"



namespace localstrategy {
	using namespace ccircuits;
	struct IndexUniversal {

		Var u;
		int vt;
		int vst;
		//primary negated val variables
		int vnL;
		int vnR;
		int vnt;

		//primary negated sel variables
		int vnst;//n for negation
		int vnsL;
		int vnsR;

		//implication set variables
		int vsLt;
		int vstL;
		int vsRt;
		int vstR;

		//implication val variables (under set)
		int vLt;
		int vtL;
		int vRt;
		int vtR;

		//Eq constructs
		int vEqL;
		int vEqR;

		//conflict set variables 
		int vcsLt; //setL and !sett
		int vcstL;
		int vcsRt;
		int vcstR;
		//conflict val variable
		int vrtL; //set and t and L
		int vrLt;
		int vrtR;
		int vrRt;

		//conflict disjunction
		int vcdL;// vcsLt OR vcstL OR vrtL OR vrLt
		int vcdR;

		//conflict conjunction
		int vccL;//EqL AND vcdL
		int vccR;

		//Diff constructs
		int vDiffL;// DiffL(i-1) OR vccL
		int vnDiffL;
		int vDiffR;
		int vnDiffR;

		//WARNING not to use prior to level
		int vnpivot;

		//implications
		int vsLassert;//DiffL-> setL
		int vsRassert;//!DiffL AND DiffR-> setR
		int vsnoassert;//!DiffL AND !DiffR-> setL OR setR
		int vspassert;// !DiffL AND !DiffR AND x-> setL
		int vsnassert;// !DiffL AND !DiffR AND !x-> setR


		int vLassert;//DiffL-> setL
		int vRassert;//!DiffL AND DiffR-> setR
		int vnoassert;//!DiffL AND !DiffR-> setL OR setR
		int vpassert;// !DiffL AND !DiffR AND x-> setL
		int vnassert;// !DiffL AND !DiffR AND !x-> setR

		//Bottom 
		int vsB; //AND implications depending on level
		int vB; //AND implications

		Circuit* ct;
		Circuit* cst;
		//primary negated val variables
		Circuit* cnL;
		Circuit* cnR;
		Circuit* cnt;

		//primary negated sel variables
		Circuit* cnst;//n for negation
		Circuit* cnsL;
		Circuit* cnsR;

		//implication set variables
		Circuit* csLt;
		Circuit* cstL;
		Circuit* csRt;
		Circuit* cstR;

		//implication val variables (under set)
		Circuit* cLt;
		Circuit* ctL;
		Circuit* cRt;
		Circuit* ctR;

		//Eq constructs
		Circuit* cEqL;
		Circuit* cEqR;

		//conflict set variables 
		Circuit* ccsLt; //setL and !sett
		Circuit* ccstL;
		Circuit* ccsRt;
		Circuit* ccstR;
		//conflict val variable
		Circuit* crtL; //set and t and L
		Circuit* crLt;
		Circuit* crtR;
		Circuit* crRt;

		//conflict disjunction
		Circuit* ccdL;// vcsLt OR vcstL OR vrtL OR vrLt
		Circuit* ccdR;

		//conflict conjunction
		Circuit* cccL;//EqL AND vcdL
		Circuit* cccR;

		//Diff constructs
		Circuit* cDiffL;// DiffL(i-1) OR vccL
		Circuit* cnDiffL;
		Circuit* cDiffR;
		Circuit* cnDiffR;

		//WARNING not to use prior to level
		Circuit* cnpivot;

		//implications
		Circuit* csLassert;//DiffL-> setL
		Circuit* csRassert;//!DiffL AND DiffR-> setR
		Circuit* csnoassert;//!DiffL AND !DiffR-> setL OR setR
		Circuit* cspassert;// !DiffL AND !DiffR AND x-> setL
		Circuit* csnassert;// !DiffL AND !DiffR AND !x-> setR


		Circuit* cLassert;//DiffL-> L
		Circuit* cRassert;//!DiffL AND DiffR-> R
		Circuit* cnoassert;//!DiffL AND !DiffR-> L OR R
		Circuit* cpassert;// !DiffL AND !DiffR AND x-> L
		Circuit* cnassert;// !DiffL AND !DiffR AND !x-> R

		//Bottom 
		Circuit* csB; //AND implications depending on level
		Circuit* cB; //AND implications



		IndexUniversal() {
			u=0;
			vt=0;
			vst=0;
			vnL=0;
			vnR = 0;
			vnt = 0;
			vnst = 0;
			vnsL = 0;
			vnsR = 0;

			vsLt = 0;
			vstL = 0;
			vsRt = 0;
			vstR = 0;

			vLt = 0;
			vtL = 0;
			vRt = 0;
			vtR = 0;

			vEqL = 0;
			vEqR = 0;

			//conflict set variables 
			vcsLt = 0; //setL and !sett
			vcstL = 0;
			vcsRt = 0;
			vcstR = 0;
			//conflict val variable
			vrtL = 0; //set and t and L
			vrLt = 0;
			vrtR = 0;
			vrRt = 0;

			//conflict disjunction
			vcdL = 0;// vcsLt OR vcstL OR vrtL OR vrLt
			vcdR = 0;

			//conflict conjunction
			vccL = 0;//EqL AND vcdL
			vccR = 0;

			//Diff constructs
			vDiffL = 0;// DiffL(i-1) OR vccL
			vnDiffL = 0;
			vDiffR = 0;
			vnDiffR = 0;

			//WARNING not to use prior to level
			vnpivot = 0;

			//implications
			vsLassert = 0;//DiffL-> setL
			vsRassert = 0;//!DiffL AND DiffR-> setR
			vsnoassert = 0;//!DiffL AND !DiffR-> setL OR setR
			vspassert = 0;// !DiffL AND !DiffR AND x-> setL
			vsnassert = 0;// !DiffL AND !DiffR AND !x-> setR


			vLassert = 0;//DiffL-> setL
			vRassert = 0;//!DiffL AND DiffR-> setR
			vnoassert = 0;//!DiffL AND !DiffR-> setL OR setR
			vpassert = 0;// !DiffL AND !DiffR AND x-> setL
			 vnassert = 0;// !DiffL AND !DiffR AND !x-> setR

			//Bottom 
			vsB = 0; //AND implications depending on level
			vB = 0; //AND implications


			ct = new Circuit();
			cst = new Circuit();
			cnL = new Circuit();
			cnR = new Circuit();
			cnt = new Circuit();
			cnst = new Circuit();
			cnsL = new Circuit();
			cnsR = new Circuit();

			csLt = new Circuit();
			cstL = new Circuit();
			csRt = new Circuit();
			cstR = new Circuit();

			cLt = new Circuit();
			ctL = new Circuit();
			cRt = new Circuit();
			ctR = new Circuit();

			cEqL = new Circuit();
			cEqR = new Circuit();

			//conflict set variables 
			ccsLt = new Circuit(); //setL and !sett
			ccstL = new Circuit();
			ccsRt = new Circuit();
			ccstR = new Circuit();
			//conflict val variable
			crtL = new Circuit(); //set and t and L
			crLt = new Circuit();
			crtR = new Circuit();
			crRt = new Circuit();

			//conflict disjunction
			ccdL = new Circuit();// vcsLt OR vcstL OR vrtL OR vrLt
			ccdR = new Circuit();

			//conflict conjunction
			cccL = new Circuit();//EqL AND vcdL
			cccR = new Circuit();

			//Diff constructs
			cDiffL = new Circuit();// DiffL(i-1) OR vccL
			cnDiffL = new Circuit();
			cDiffR = new Circuit();
			cnDiffR = new Circuit();

			//WARNING not to use prior to level
			cnpivot = new Circuit();

			//implications
			csLassert = new Circuit();//DiffL-> setL
			csRassert = new Circuit();//!DiffL AND DiffR-> setR
			csnoassert = new Circuit();//!DiffL AND !DiffR-> setL OR setR
			cspassert = new Circuit();// !DiffL AND !DiffR AND x-> setL
			csnassert = new Circuit();// !DiffL AND !DiffR AND !x-> setR


			cLassert = new Circuit();//DiffL-> setL
			cRassert = new Circuit();//!DiffL AND DiffR-> setR
			cnoassert = new Circuit();//!DiffL AND !DiffR-> setL OR setR
			cpassert = new Circuit();// !DiffL AND !DiffR AND x-> setL
			cnassert = new Circuit();// !DiffL AND !DiffR AND !x-> setR

			//Bottom 
			csB = new Circuit(); //AND implications depending on level
			cB = new Circuit(); //AND implications
		}

		void display(int u_no, int line_no) {
			if (ct->list.length>0) {
				std::cout << "line "<< line_no << " val tau^" << u_no << ": ";
				ct->display();
			}
			if (cst->list.length > 0) {
				std::cout << "line " << line_no << " set tau^" << u_no << ": ";
				cst->display();
			}
			if (cnt->list.length > 0) {
				std::cout << "line " << line_no << " not val tau^" << u_no << ": ";
				cnt->display();
			}
			if (cnst->list.length > 0) {
				std::cout << "line " << line_no << " not set tau^" << u_no << ": ";
				cnst->display();
			}
			if (cnL->list.length > 0) {
				std::cout << "line " << line_no << " not valL^" << u_no << ": ";
				cnL->display();
			}
			if (cnsL->list.length > 0) {
				std::cout << "line " << line_no << " not setL^" << u_no << ": ";
				cnsL->display();
			}
			if (cnR->list.length > 0) {
				std::cout << "line " << line_no << " not valR^" << u_no << ": ";
				cnR->display();
			}
			if (cnsR->list.length > 0) {
				std::cout << "line " << line_no << " not setR^" << u_no << ": ";
				cnsR->display();
			}

			if (csLt->list.length > 0) {
				std::cout << "line " << line_no << " SetL^" << u_no << "->Set tau^" << u_no << ": ";
				csLt->display();
			}
			if (cstL->list.length > 0) {
				std::cout << "line " << line_no << " Set tau^" << u_no << "->SetL^" << u_no << ": ";
				cstL->display();
			}
			if (csRt->list.length > 0) {
				std::cout << "line " << line_no << " SetR^" << u_no << "->Set tau^" << u_no << ": ";
				csRt->display();
			}
			if (cstR->list.length > 0) {
				std::cout << "line " << line_no << " Set tau^" << u_no << "->SetR^" << u_no << ": ";
				cstR->display();
			}

			if (cLt->list.length > 0) {
				std::cout << "line " << line_no << " ValL^" << u_no << "->Val tau^" << u_no << ": ";
				cLt->display();
			}
			if (ctL->list.length > 0) {
				std::cout << "line " << line_no << " Val tau^" << u_no << "->ValL^" << u_no << ": ";
				ctL->display();
			}
			if (cRt->list.length > 0) {
				std::cout << "line " << line_no << " ValR^" << u_no << "->Val tau^" << u_no << ": ";
				cRt->display();
			}
			if (ctR->list.length > 0) {
				std::cout << "line " << line_no << " Val tau^" << u_no << "->ValR^" << u_no << ": ";
				ctR->display();
			}

			if (cEqL->list.length > 0) {
				std::cout << "line " << line_no << " EqL^" << u_no << ": ";
				cEqL->display();
			}
			if (cEqR->list.length > 0) {
				std::cout << "line " << line_no << " EqR^" << u_no << ": ";
				cEqR->display();
			}

			if (ccsLt->list.length > 0) {
				std::cout << "line " << line_no << " SetL^" << u_no << "-/->Set tau^" << u_no << ": ";
				ccsLt->display();
			}
			if (ccstL->list.length > 0) {
				std::cout << "line " << line_no << " Set tau^" << u_no << "-/->SetL^" << u_no << ": ";
				ccstL->display();
			}
			if (csRt->list.length > 0) {
				std::cout << "line " << line_no << " SetR^" << u_no << "-/->Set tau^" << u_no << ": ";
				ccsRt->display();
			}
			if (ccstR->list.length > 0) {
				std::cout << "line " << line_no << " Set tau^" << u_no << "-/->SetR^" << u_no << ": ";
				ccstR->display();
			}

			if (crLt->list.length > 0) {
				std::cout << "line " << line_no << " ValL^" << u_no << "-/->Val tau^" << u_no << ": ";
				crLt->display();
			}
			if (crtL->list.length > 0) {
				std::cout << "line " << line_no << " Val tau^" << u_no << "-/->ValL^" << u_no << ": ";
				crtL->display();
			}
			if (crRt->list.length > 0) {
				std::cout << "line " << line_no << " ValR^" << u_no << "-/->Val tau^" << u_no << ": ";
				crRt->display();
			}
			if (crtR->list.length > 0) {
				std::cout << "line " << line_no << " Val tau^" << u_no << "-/->ValR^" << u_no << ": ";
				crtR->display();
			}

			if (ccdL->list.length > 0) {
				std::cout << "line " << line_no << " Left disjunction^" << u_no << ": ";
				ccdL->display();
			}
			if (ccdR->list.length > 0) {
				std::cout << "line " << line_no << " Right disjunction^" << u_no << ": ";
				ccdR->display();
			}
			if (cccL->list.length > 0) {
				std::cout << "line " << line_no << " Left conjunction^" << u_no << ": ";
				cccL->display();
			}
			if (cccR->list.length > 0) {
				std::cout << "line " << line_no << " Right conjunction^" << u_no << ": ";
				cccR->display();
			}

			if (cDiffL->list.length > 0) {
				std::cout << "line " << line_no << " DiffL^" << u_no << ": ";
				cDiffL->display();
			}
			if (cnDiffL->list.length > 0) {
				std::cout << "line " << line_no << " not DiffL^" << u_no << ": ";
				cnDiffL->display();
			}
			if (cDiffR->list.length > 0) {
				std::cout << "line " << line_no << " DiffR^" << u_no << ": ";
				cDiffR->display();
			}
			if (cnDiffR->list.length > 0) {
				std::cout << "line " << line_no << " not DiffR^" << u_no << ": ";
				cnDiffR->display();
			}

			if (cnpivot->list.length > 0) {
				std::cout << "line " << line_no << " not pivot: ";
				cnpivot->display();
			}

			if (csLassert->list.length > 0) {
				std::cout << "line " << line_no << " set L assert^" << u_no << ": ";
				csLassert->display();
			}
			if (csRassert->list.length > 0) {
				std::cout << "line " << line_no << " set R assert^" << u_no << ": ";
				csRassert->display();
			}
			if (csnoassert->list.length > 0) {
				std::cout << "line " << line_no << " set no assert^" << u_no << ": ";
				csnoassert->display();
			}
			if (cspassert->list.length > 0) {
				std::cout << "line " << line_no << " set positive x assert^" << u_no << ": ";
				cspassert->display();
			}
			if (csnassert->list.length > 0) {
				std::cout << "line " << line_no << " set negative x assert^" << u_no << ": ";
				csnassert->display();
			}

			if (cLassert->list.length > 0) {
				std::cout << "line " << line_no << " val L assert^" << u_no << ": ";
				cLassert->display();
			}
			if (cRassert->list.length > 0) {
				std::cout << "line " << line_no << " val R assert^" << u_no << ": ";
				cRassert->display();
			}
			if (cnoassert->list.length > 0) {
				std::cout << "line " << line_no << " val no assert^" << u_no << ": ";
				cnoassert->display();
			}
			if (cpassert->list.length > 0) {
				std::cout << "line " << line_no << " val positive x assert^" << u_no << ": ";
				cpassert->display();
			}
			if (cnassert->list.length > 0) {
				std::cout << "line " << line_no << " val negative x assert^" << u_no << ": ";
				cnassert->display();
			}

			if (csB->list.length > 0) {
				std::cout << "line " << line_no << " set_u^" << u_no << ": ";
				csB->display();
			}
			if (cB->list.length > 0) {
				std::cout << "line " << line_no << " val_u^" << u_no << ": ";
				cB->display();
			}

		}
	};

	struct Strategy_Extractor {
		QCNF* input_QBF;
		ExpResProof* input_proof;
		LinkL<Circuit>* output_circuit;
		Circuit* master_circuit;
		Cnf* extension_clauses;
		Cnf* negated_assumptions;
		Cnf* output_cnf;
		QRAT_Proof* output_QRAT;
		LinkL<LinkL<IndexUniversal>>* main_index;
		//LinkL<IndexStrat>* strategy_index;
		int base_max_var;
		int idx_max_var;
		Prefix* long_prefix;

		Strategy_Extractor() {
			input_QBF = new QCNF;
			input_proof = new ExpResProof;
			output_circuit = new LinkL<Circuit>;
			master_circuit = new Circuit;
			extension_clauses = new Cnf;
			negated_assumptions = new Cnf;
			output_cnf = new Cnf;
			output_cnf = new Cnf;
			output_QRAT = new QRAT_Proof();
			main_index = new LinkL<LinkL<IndexUniversal>>;
			base_max_var = 0;
			idx_max_var = 0;
			long_prefix = new Prefix;
		}
		Strategy_Extractor(QCNF* phi, ExpResProof* pi) {
			input_QBF = new QCNF();
			input_QBF->matrix = ccopy(phi->matrix);
			input_QBF->prefix = copy(phi->prefix);
			input_proof = pi;
			output_circuit = new LinkL<Circuit>;
			master_circuit = new Circuit;
			output_cnf = new Cnf;
			extension_clauses = new Cnf;
			negated_assumptions = new Cnf;
			output_QRAT = new QRAT_Proof();
			output_QRAT->Phi = *input_QBF;
			main_index = new LinkL<LinkL<IndexUniversal>>;
			base_max_var = phi->matrix.mvar;
			idx_max_var = base_max_var;
			long_prefix = new Prefix;
		}

		void load_output_cnf_negated() {
			output_cnf->makeempty();
			copyinto(output_cnf, &(input_QBF->matrix));
			copyinto(output_cnf, extension_clauses);
			copyinto(output_cnf, negated_assumptions);
		}

		void display_index() {
			Link1<LinkL<IndexUniversal>>* current = main_index->head;
			int line_no = 0;
			while(current!=NULL) {
				int u_no = 0;
				Link1<IndexUniversal>* layer = current->data.head;
				while (layer != NULL) {
					layer->data.display(u_no, line_no);
					u_no++;
					layer = layer->next;
				}
				line_no++;
				current = current->next;
			}
		}
	};


	void increment(Var* max_var, Prefix* P, Var* idx) {//adds a new circuit label
		int new_val = *max_var + 1;
		*max_var = new_val;
		P->addvar(new_val);
		*idx = new_val;
	}

	int add_anno_expres(Var max_var, Strategy_Extractor* SE, LinkL<IndexUniversal>* indexline, Var u, int u_no, int line_no) {
		
		Prefix P = SE->input_QBF->prefix;
		IndexUniversal* temp= new IndexUniversal();
		temp->u = u;

		ClausalProof* pi = &(SE->input_proof->pi);
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		if (L.rule == AXIOM) {
			if (u_no > 0) {
				increment(&max_var, &P, &temp->vsB);
				increment(&max_var, &P, &temp->vB);
			}
		}
		if (L.rule == REDUCTION) {
			if (u_no > 0) {
				increment(&max_var, &P, &temp->vsB);
				increment(&max_var, &P, &temp->vB);
			}
		}
		if (L.rule == RESOLUTION) {
			int x1pos = L.litpos1;
			int P1pos = L.parent1;
			int P0pos = L.parent0;
			Lit xt = pi->operator[](P1pos).clause.operator[](x1pos);
			AnnoLit xtau = littoanno(xt, SE->input_proof->index);
			Lit x = xtau.Elit;
			LinkL<Lit> tau = xtau.Aanno;
			if (P.lvl(u) > P.lvl(x.var)) {
				increment(&max_var, &P, &temp->vnpivot);

				increment(&max_var, &P, &temp->vsLassert);
				increment(&max_var, &P, &temp->vLassert);
				increment(&max_var, &P, &temp->vsRassert);
				increment(&max_var, &P, &temp->vRassert);

				increment(&max_var, &P, &temp->vspassert);
				increment(&max_var, &P, &temp->vpassert);
				increment(&max_var, &P, &temp->vsnassert);
				increment(&max_var, &P, &temp->vnassert);

				increment(&max_var, &P, &temp->vsB);
				increment(&max_var, &P, &temp->vB);
			}
			else {
				if (u_no == 0) {
					increment(&max_var, &P, &temp->vEqL);
					increment(&max_var, &P, &temp->vEqR);
					increment(&max_var, &P, &temp->vDiffL);
					increment(&max_var, &P, &temp->vDiffR);
					increment(&max_var, &P, &temp->vnDiffL);
					increment(&max_var, &P, &temp->vnDiffR);
					increment(&max_var, &P, &temp->vsB);
					increment(&max_var, &P, &temp->vB);
				}
				else {
					increment(&max_var, &P, &temp->vnsL );
					increment(&max_var, &P, &temp->vnsR );
					increment(&max_var, &P, &temp->vnL);
					increment(&max_var, &P, &temp->vnR);

					increment(&max_var, &P, &temp->vt);
					increment(&max_var, &P, &temp->vnt);
					increment(&max_var, &P, &temp->vst);
					increment(&max_var, &P, &temp->vnst);

					increment(&max_var, &P, &temp->vsLt);
					increment(&max_var, &P, &temp->vstL);
					increment(&max_var, &P, &temp->vsRt);
					increment(&max_var, &P, &temp->vstR);

					increment(&max_var, &P, &temp->vLt);
					increment(&max_var, &P, &temp->vtL);
					increment(&max_var, &P, &temp->vRt);
					increment(&max_var, &P, &temp->vtR);

					increment(&max_var, &P, &temp->vEqL);
					increment(&max_var, &P, &temp->vEqR);

					increment(&max_var, &P, &temp->vcsLt);
					increment(&max_var, &P, &temp->vcstL);
					increment(&max_var, &P, &temp->vcsRt);
					increment(&max_var, &P, &temp->vcstR);

					increment(&max_var, &P, &temp->vrLt);
					increment(&max_var, &P, &temp->vrtL);
					increment(&max_var, &P, &temp->vrRt);
					increment(&max_var, &P, &temp->vrtR);

					increment(&max_var, &P, &temp->vcdL);
					increment(&max_var, &P, &temp->vcdR);
					increment(&max_var, &P, &temp->vccL);
					increment(&max_var, &P, &temp->vccR);

					increment(&max_var, &P, &temp->vDiffL);
					increment(&max_var, &P, &temp->vDiffR);
					increment(&max_var, &P, &temp->vnDiffL);
					increment(&max_var, &P, &temp->vnDiffR);

					increment(&max_var, &P, &temp->vsLassert);
					increment(&max_var, &P, &temp->vsRassert);
					increment(&max_var, &P, &temp->vsnoassert);

					increment(&max_var, &P, &temp->vLassert);
					increment(&max_var, &P, &temp->vRassert);
					increment(&max_var, &P, &temp->vnoassert);

					increment(&max_var, &P, &temp->vsB);
					increment(&max_var, &P, &temp->vB);
				}
				
			}
		}
		indexline->addnode(*temp);
		return max_var;

	}

	int add_line_expres(Var max_var, Strategy_Extractor* SE,  int line_no) {
		Prefix P = SE->input_QBF->prefix;
		int u_no = 0;
		Link1<Quantifier>* currQ=  P.head;
		
		LinkL<IndexUniversal>* temp = new LinkL<IndexUniversal>();
		Var u = 0;
		max_var = add_anno_expres(max_var, SE, temp, u, 0, line_no);
		u_no++;
		while (currQ!=NULL) {
			u = currQ->data.var;
			if (currQ->data.is_universal) {
				max_var = add_anno_expres(max_var, SE, temp, u, u_no, line_no);
				u_no++;
			}
			
			currQ = currQ->next;
			
		}
		SE->main_index->addnode(*temp);
		return max_var;
	}


	void def_anno_expres(Strategy_Extractor* SE, IndexUniversal read, int u_no, int line_no) {
		Var u = read.u;
		
		
		Prefix P = SE->input_QBF->prefix;
		
		ClausalProof* pi = &(SE->input_proof->pi);
		Line<Clause> L = pi->operator[](line_no);
		Clause C = L.clause;
		//QRAT_Proof* qrat = SE->output_QRAT;

		if (L.rule == AXIOM) {
			int cnf_no = SE->input_proof->findAxiom(line_no);
			if (cnf_no == -1) {
				std::cout << "Error: ";
				C.display();
				std::cout << " ";
				Link1<Lit>* curerr = C.head;
				while (curerr != NULL) {
					AnnoLit p= littoanno(curerr->data, SE->input_proof->index);
					p.display();
					std::cout << " ";
					curerr = curerr->next;
				}
				std::cout << std::endl;
				Link1<Index_Anno>* curerr2 = SE->input_proof->index.head;
				while (curerr2 != NULL) {
					curerr2->data.display();
					std::cout << std::endl;
					curerr2 = curerr2->next;
				}
				std::cout<< "0";
			}
			if (u_no > 0) {
				LinkL<Lit> assignment = SE->input_proof->findAnnotation(cnf_no, line_no);
				Link1<Lit>* currentA = assignment.head;
				while (currentA != NULL) {
					if (currentA->data.var == u) {
						read.csB->def1(read.vsB);
						if (currentA->data.is_pos) {
							read.cB->def1(read.vB);
						}
						else {
							read.cB->def0(read.vB);
						}
					}
					currentA = currentA->next;
				}
			}

		}
		if (L.rule == REDUCTION) {
			if (u_no > 0) {
				int Ppos = L.parent0;
				int vP = SE->main_index->operator[](Ppos).operator[](u_no).vB;
				int vsP = SE->main_index->operator[](Ppos).operator[](u_no).vsB;
				read.cB->defequiv(read.vB, vP);
				read.csB->defequiv(read.vsB, vsP);
			}
		}

		if (L.rule == RESOLUTION) {
			int x1pos = L.litpos1;
			int P1pos = L.parent1;
			int P0pos = L.parent0;
			Lit xt = pi->operator[](P1pos).clause.operator[](x1pos);
			AnnoLit xtau = littoanno(xt, SE->input_proof->index);
			Lit x = xtau.Elit;
			LinkL<Lit> tau = xtau.Aanno;
			int m=0; //u_no that is maximum 
			int vL = SE->main_index->operator[](P0pos).operator[](u_no).vB;
			int vR = SE->main_index->operator[](P1pos).operator[](u_no).vB;
			int vsL = SE->main_index->operator[](P0pos).operator[](u_no).vsB;
			int vsR = SE->main_index->operator[](P1pos).operator[](u_no).vsB;
			if (u_no > 0) {
				if (((vL == 0) || (vR == 0)) || ((vsL == 0) || (vsR == 0))) {
					std::cout << "WARNING vL vR vsL vsR: " << vL << " " << vR << " " << vsL << " " << vsR << std::endl;
				}
			}
			Lit lt = Lit(-u);
			bool is_lt_found = 0;
			Link1<Lit>* currentanno = tau.head;
			while (currentanno != NULL) {
				if (currentanno->data.var == u) {
					lt = currentanno->data;
					is_lt_found = 1;
				}
				currentanno = currentanno->next;
			}

			//fill in others TODO
			

			if (P.lvl(u) > P.lvl(x.var)) {
				Link1<IndexUniversal>* current = SE->main_index->operator[](line_no).head;
				while (current!=NULL) {
					Var v = current->data.u;
					if (P.lvl(v) < P.lvl(x.var)) {
						m = current->position;
					}
					current=current->next;
				}

				
				int vDiffL = SE->main_index->operator[](line_no).operator[](m).vDiffL;
				int vnDiffL = SE->main_index->operator[](line_no).operator[](m).vnDiffL;
				int vDiffR = SE->main_index->operator[](line_no).operator[](m).vDiffR;
				int vnDiffR = SE->main_index->operator[](line_no).operator[](m).vnDiffR;

				read.cnpivot->defNOT(read.vnpivot, x.var);

				read.csLassert->defOR(read.vsLassert, vnDiffL, vsL);//DiffL-> setL

				LinkL<int> list_csRassert = LinkL<int>();
				list_csRassert.addnode(vDiffL);
				list_csRassert.addnode(vnDiffR);
				list_csRassert.addnode(vsR);
				read.csRassert->defOR(read.vsRassert, list_csRassert);//!DiffL AND DiffR-> setR
				list_csRassert.makeempty();

				read.cLassert->defOR(read.vLassert, vnDiffL, vL);//DiffL-> L

				LinkL<int> list_cRassert = LinkL<int>();
				list_cRassert.addnode(vDiffL);
				list_cRassert.addnode(vnDiffR);
				list_cRassert.addnode(vR);
				read.cRassert->defOR(read.vRassert, list_cRassert);//!DiffL AND DiffR-> R
				list_cRassert.makeempty();

				
				LinkL<int> list_passert;
				LinkL<int> list_nassert;
				LinkL<int> list_spassert;
				LinkL<int> list_snassert;
				if (x.is_pos) {
					list_spassert.addnode(read.vnpivot);
					list_snassert.addnode(x.var);
					list_passert.addnode(read.vnpivot);
					list_nassert.addnode(x.var);
				}
				else {
					list_spassert.addnode(x.var);
					list_snassert.addnode(read.vnpivot);
					list_passert.addnode(x.var);
					list_nassert.addnode(read.vnpivot);
				}
				list_spassert.addnode(vDiffL);
				list_snassert.addnode(vDiffL);
				list_passert.addnode(vDiffL);
				list_nassert.addnode(vDiffL);

				list_spassert.addnode(vDiffR);
				list_snassert.addnode(vDiffR);
				list_passert.addnode(vDiffR);
				list_nassert.addnode(vDiffR);

				list_spassert.addnode(vsL);
				list_snassert.addnode(vsR);
				list_passert.addnode(vL);
				list_nassert.addnode(vR);

				read.cspassert->defOR(read.vspassert, list_spassert);
				read.csnassert->defOR(read.vsnassert, list_snassert);

				read.cpassert->defOR(read.vpassert, list_passert);
				read.cnassert->defOR(read.vnassert, list_nassert);
				list_spassert.makeempty();
				list_snassert.makeempty();
				list_passert.makeempty();
				list_nassert.makeempty();

				LinkL<int> list_sB;
				list_sB.addnode(read.vsLassert);
				list_sB.addnode(read.vsRassert);
				list_sB.addnode(read.vspassert);
				list_sB.addnode(read.vsnassert);
				read.csB->defAND(read.vsB, list_sB);
				list_sB.makeempty();

				LinkL<int> list_B;
				list_B.addnode(read.vLassert);
				list_B.addnode(read.vRassert);
				list_B.addnode(read.vpassert);
				list_B.addnode(read.vnassert);
				read.cB->defAND(read.vB, list_B);
				list_B.makeempty();

			}
			else{
				if (u_no == 0) {
					read.cEqL->def1(read.vEqL);
					read.cEqR->def1(read.vEqR);
					read.cDiffL->def0(read.vDiffL);
					read.cDiffR->def0(read.vDiffR);
					read.cnDiffL->defNOT(read.vnDiffL, read.vDiffL);
					read.cnDiffR->defNOT(read.vnDiffR, read.vDiffR);
				}
				else{

					read.cnL->defNOT(read.vnL, vL);
					read.cnR->defNOT(read.vnR, vR);
					read.cnsL->defNOT(read.vnsL, vsL);
					read.cnsR->defNOT(read.vnsR, vsR);

					if (!lt.is_pos) {
						read.ct->def0(read.vt);
						read.cnt->def1(read.vnt);
					}
					else {
						read.ct->def1(read.vt);
						read.cnt->def0(read.vnt);
					}

					if (!is_lt_found) {
						read.cst->def0(read.vst);
						read.cnst->def1(read.vnst);
					}
					else {
						read.cst->def1(read.vst);
						read.cnst->def0(read.vnst);
					}

					//implication set variables
					read.csLt->defOR(read.vsLt, read.vnsL, read.vst);
					read.cstL->defOR(read.vstL, read.vnst, vsL);
					read.csRt->defOR(read.vsRt, read.vnsR, read.vst);
					read.cstR->defOR(read.vstR, read.vnst, vsR);


					//implication val variables (under set)
					LinkL<int> tripleLt = LinkL<int>();
					tripleLt.addnode(read.vnst);
					tripleLt.addnode(read.vnL);
					tripleLt.addnode(read.vt);
					read.cLt->defOR(read.vLt, tripleLt);
					tripleLt.makeempty();

					LinkL<int> tripletL = LinkL<int>();
					tripletL.addnode(read.vnst);
					tripletL.addnode(read.vnt);
					tripletL.addnode(vL);
					read.ctL->defOR(read.vtL, tripletL);
					tripletL.makeempty();

					LinkL<int> tripleRt = LinkL<int>();
					tripleRt.addnode(read.vnst);
					tripleRt.addnode(read.vnR);
					tripleRt.addnode(read.vt);
					read.cRt->defOR(read.vRt, tripleRt);
					tripleRt.makeempty();

					LinkL<int> tripletR = LinkL<int>();
					tripletR.addnode(read.vnst);
					tripletR.addnode(read.vnt);
					tripletR.addnode(vR);
					read.ctR->defOR(read.vtR, tripletR);
					tripletR.makeempty();

					//Eq constructs
					int vprevEqL = SE->main_index->operator[](line_no).operator[](u_no - 1).vEqL;
					LinkL<int> listEqL = LinkL<int>();
					listEqL.addnode(vprevEqL);
					listEqL.addnode(read.vsLt);
					listEqL.addnode(read.vstL);
					listEqL.addnode(read.vLt);
					listEqL.addnode(read.vtL);
					read.cEqL->defAND(read.vEqL, listEqL);
					listEqL.makeempty();

					int vprevEqR = SE->main_index->operator[](line_no).operator[](u_no - 1).vEqR;
					LinkL<int> listEqR = LinkL<int>();
					listEqR.addnode(vprevEqR);
					listEqR.addnode(read.vsRt);
					listEqR.addnode(read.vstR);
					listEqR.addnode(read.vRt);
					listEqR.addnode(read.vtR);
					read.cEqR->defAND(read.vEqR, listEqR);
					listEqR.makeempty();

					//conflict set variables 
					read.ccsLt->defAND(read.vcsLt, vsL, read.vnst); //setL and !sett
					read.ccstL->defAND(read.vcstL, read.vnsL, read.vst);
					read.ccsRt->defAND(read.vcsRt, vsR, read.vnst);
					read.ccstR->defAND(read.vcstR, read.vnsR, read.vst);

					//conflict val variable
					LinkL<int> triplerLt = LinkL<int>();
					triplerLt.addnode(read.vst);
					triplerLt.addnode(read.vnL);
					triplerLt.addnode(read.vt);
					read.crLt->defAND(read.vrLt, triplerLt); //set and t and not L
					triplerLt.makeempty();

					LinkL<int> triplertL = LinkL<int>();
					triplertL.addnode(read.vst);
					triplertL.addnode(vL);
					triplertL.addnode(read.vnt);
					read.crtL->defAND(read.vrtL, triplertL); //set and t and not L
					triplertL.makeempty();

					LinkL<int> triplerRt = LinkL<int>();
					triplerRt.addnode(read.vst);
					triplerRt.addnode(read.vnR);
					triplerRt.addnode(read.vt);
					read.crRt->defAND(read.vrRt, triplerRt); //set and t and not L
					triplerRt.makeempty();

					LinkL<int> triplertR = LinkL<int>();
					triplertR.addnode(read.vst);
					triplertR.addnode(vR);
					triplertR.addnode(read.vnt);
					read.crtR->defAND(read.vrtR, triplertR); //set and t and not L
					triplertR.makeempty();

					//conflict disjunction
					LinkL<int> list_ccdL;
					list_ccdL.addnode(read.vcsLt);
					list_ccdL.addnode(read.vcstL);
					list_ccdL.addnode(read.vrLt);
					list_ccdL.addnode(read.vrtL);
					read.ccdL->defOR(read.vcdL, list_ccdL);// vcsLt OR vcstL OR vrtL OR vrLt
					list_ccdL.makeempty();

					LinkL<int> list_ccdR;
					list_ccdR.addnode(read.vcsRt);
					list_ccdR.addnode(read.vcstR);
					list_ccdR.addnode(read.vrRt);
					list_ccdR.addnode(read.vrtR);
					read.ccdR->defOR(read.vcdR, list_ccdR);// vcsRt OR vcstR OR vrtR OR vrRt
					list_ccdR.makeempty();

					//previous

					//conflict conjunction
					read.cccL->defAND(read.vccL, vprevEqR, read.vcdL);//EqR AND vcdL
					read.cccR->defAND(read.vccR, vprevEqL, read.vcdR);

					//Diff constructs
					int vprevDiffL = SE->main_index->operator[](line_no).operator[](u_no - 1).vDiffL;
					int vprevDiffR = SE->main_index->operator[](line_no).operator[](u_no - 1).vDiffR;

					read.cDiffL->defOR(read.vDiffL, vprevDiffL, read.vccL);// DiffL(i-1) OR vccL
					read.cnDiffL->defNOT(read.vnDiffL, read.vDiffL);

					read.cDiffR->defOR(read.vDiffR, vprevDiffR, read.vccR);
					read.cnDiffR->defNOT(read.vnDiffR, read.vDiffR);

					read.csLassert->defOR(read.vsLassert, read.vnDiffL, vsL);//DiffL-> setL

					LinkL<int> list_csRassert = LinkL<int>();
					list_csRassert.addnode(read.vDiffL);
					list_csRassert.addnode(read.vnDiffR);
					list_csRassert.addnode(vsR);
					read.csRassert->defOR(read.vsRassert, list_csRassert);//!DiffL AND DiffR-> setR
					list_csRassert.makeempty();

					LinkL<int> list_csnoassert;
					list_csnoassert.addnode(read.vDiffL);
					list_csnoassert.addnode(read.vDiffR);
					list_csnoassert.addnode(vsL);
					read.csnoassert->defOR(read.vsnoassert, list_csnoassert);//!DiffL AND !DiffR-> setL OR setR
					list_csnoassert.makeempty();




					read.cLassert->defOR(read.vLassert, read.vnDiffL, vL);//DiffL-> L

					LinkL<int> list_cRassert = LinkL<int>();
					list_cRassert.addnode(read.vDiffL);
					list_cRassert.addnode(read.vnDiffR);
					list_cRassert.addnode(vR);
					read.cRassert->defOR(read.vRassert, list_cRassert);//!DiffL AND DiffR-> R
					list_cRassert.makeempty();

					LinkL<int> list_cnoassert;
					list_cnoassert.addnode(read.vDiffL);
					list_cnoassert.addnode(read.vDiffR);
					list_cnoassert.addnode(vsL);
					read.cnoassert->defOR(read.vnoassert, list_cnoassert);//!DiffL AND !DiffR-> L OR R
					list_cnoassert.makeempty();

					LinkL<int> list_csB;
					list_csB.addnode(read.vsLassert);
					list_csB.addnode(read.vsRassert);
					list_csB.addnode(read.vsnoassert);
					read.csB->defAND(read.vsB, list_csB);
					list_csB.makeempty();

					LinkL<int> list_cB;
					list_cB.addnode(read.vLassert);
					list_cB.addnode(read.vRassert);
					list_cB.addnode(read.vnoassert);
					read.cB->defAND(read.vB, list_cB);
					list_cB.makeempty();
				}
				

			}
		}


	}


	void def_line_expres(Strategy_Extractor* SE, LinkL<IndexUniversal> read, int line_no){
		Prefix P = SE->input_QBF->prefix;
		int u_no = 0;
		Link1<IndexUniversal>* currlevel = read.head;
		Var u = 0;
		//max_var = add_anno_expres(max_var, SE, temp, u, 0, line_no);
		
		
		while (currlevel != NULL) {

			def_anno_expres( SE, currlevel->data, u_no, line_no);
			u_no++;
			currlevel = currlevel->next;
		}
	}

	void load_line_expres(LinkL<Circuit>* output_circuit, Strategy_Extractor* SE, int line_no) {
		//todo

		Link1<Circuit>* currC = output_circuit->head;
		Link1<IndexUniversal>* currI = SE->main_index->findnode(line_no)->data.head;
		Circuit temp;
		while (currI != NULL) {
			/*
			Link1<Circuit>* currCprev = output_circuit->head;
			while (currCprev!=currC) {
				currC->data.addcircuit(currCprev->data);
				currCprev = currCprev->next;
			}
			*/
			IndexUniversal read = currI->data;
			temp.addcircuit(*read.cst);
			temp.addcircuit(*read.ct);
			temp.addcircuit(*read.cnL);
			temp.addcircuit(*read.cnR);
			temp.addcircuit(*read.cnt);

			temp.addcircuit(*read.cnst);
			temp.addcircuit(*read.cnsL);
			temp.addcircuit(*read.cnsR);

			//implication set variables

			temp.addcircuit(*read.csLt);
			temp.addcircuit(*read.cstL);
			temp.addcircuit(*read.csRt);
			temp.addcircuit(*read.cstR);


			//implication val variables (under set)

			temp.addcircuit(*read.cLt);
			temp.addcircuit(*read.ctL);
			temp.addcircuit(*read.cRt);
			temp.addcircuit(*read.ctR);

			//Eq constructs
			temp.addcircuit(*read.cEqL);
			temp.addcircuit(*read.cEqR);

			//conflict set variables 
			temp.addcircuit(*read.ccsLt);
			temp.addcircuit(*read.ccstL);
			temp.addcircuit(*read.ccsRt);
			temp.addcircuit(*read.ccstR);

			//conflict val variable
			temp.addcircuit(*read.crtL);
			temp.addcircuit(*read.crLt);
			temp.addcircuit(*read.crtR);
			temp.addcircuit(*read.crRt);


			//conflict disjunction
			temp.addcircuit(*read.ccdL);
			temp.addcircuit(*read.ccdR);

			//conflict conjunction
			temp.addcircuit(*read.cccL);
			temp.addcircuit(*read.cccR);

			//Diff constructs
			temp.addcircuit(*read.cDiffL);
			temp.addcircuit(*read.cnDiffL);
			temp.addcircuit(*read.cDiffR);
			temp.addcircuit(*read.cnDiffR);


			//WARNING not to use prior to level
			temp.addcircuit(*read.cnpivot);

			//implications
			temp.addcircuit(*read.csLassert);
			temp.addcircuit(*read.csRassert);
			temp.addcircuit(*read.csnoassert);
			temp.addcircuit(*read.cspassert);
			temp.addcircuit(*read.csnassert);

			temp.addcircuit(*read.cLassert);
			temp.addcircuit(*read.cRassert);
			temp.addcircuit(*read.cnoassert);
			temp.addcircuit(*read.cpassert);
			temp.addcircuit(*read.cnassert);
			temp.addcircuit(*read.csB);
			temp.addcircuit(*read.cB);
			if (currC == NULL) {
				output_circuit->addnode(Circuit());
				currC = output_circuit->tail;
			}
			currC->data.addcircuit(temp);

			currI = currI->next;
			currC = currC->next;
		}
		SE->master_circuit->addcircuit(temp);
	}

	void negatebase(Cnf* output, Strategy_Extractor* SE, int a_base, bool is_unsat) {
		if (is_unsat) {
			ClausalProof* proof = &SE->input_proof->pi;
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

	Strategy_Extractor* Extract(QCNF* phi, ExpResProof* pi, int a_base, bool is_unsat) {
		Strategy_Extractor* output = new Strategy_Extractor(phi, pi);
		output->main_index = new LinkL<LinkL<IndexUniversal>>;
		//Circuit* temp = new Circuit();
		//output->strategy_index = new LinkL<IndexStrat>;
		int max_var = output->base_max_var;

		for (int i = 0; i < a_base+1; i++) {
			max_var= add_line_expres(max_var, output, i);
			def_line_expres(output, output->main_index->tail->data, i);
			load_line_expres(output->output_circuit, output, i);
		}
		Cnf extc = extclauses(*output->master_circuit);
		extc.copy(output->extension_clauses);
		
		//copyinto(output->extension_clauses, &extc);
		LinkL<IndexUniversal> end_index= output->main_index->tail->data;
		Link1<IndexUniversal>* current = end_index.head->next;
		while (current!=NULL) {
			Lit u= Lit(current->data.u);
			Lit b = Lit(current->data.vB);
			Clause C1 = Clause();
			C1.addnode(-u);
			C1.addnode(b);
			Clause C2 = Clause();
			C2.addnode(u);
			C2.addnode(-b);
			output->negated_assumptions->addnode(C1);
			output->negated_assumptions->addnode(C2);
			current = current->next;
		}
		output->extension_clauses->update_max_var();
		output->negated_assumptions->update_max_var();
			
		return output;

	}


	

	


}