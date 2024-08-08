// rbse.cpp : Defines the entry point for the application.
//

#include "rbse.h"


#include "Test.h"
#include <ctime>        // std::time

using namespace std;



void pseudomain(int argc, char** argv) {
	bool file_writing = 1;
	bool file_reading = 1;
	//bool verbose = 1;
	char* fname = NULL;
	char* ofname = NULL;
	char outputname[100];
	char extoutputname[100];
	char qratoutputname[100];
	char qdimacsname[100];
	char qrpname[100];
	double duration;
	std::clock_t start;
	if (argc > 1) {
		if (argv[1][0] == '-') { printf("c first parameter needs to be qdimacs file name\n"); return; }
		printf("reading first argument the input name\n");
		fname = argv[1];
		printf("input name loaded:\n");
		printf(fname);
	}
	if (argc > 2) {
		if (argv[1][0] == '-') { printf("c second parameter needs to be qdimacs file name\n"); return; }
		fname = argv[1];
	}
	else {
		printf("Not enough arguments, defaulting to example mode: QPARITY(5)");
		file_reading = 0;
		file_writing = 1;
	}

	for (int i = 1; i < argc; i++) {
		if (argv[i][0] == '-') {
			if (argv[i][1] == 'o') {
				file_writing = 1;
				if (argc == i + 1) {
					printf("c file name missing after -o\n");
					return;
					//strcat(fname, to_cstr(std::move(ss).str()));
				}
				else {
					printf("adding extensions\n");
					ofname = argv[i + 1];
					strcpy(outputname, ofname);
					strcpy(extoutputname, ofname);
					strcpy(qratoutputname, ofname);
					strcat(outputname, ".cnf");
					strcat(extoutputname, "_ext.cnf");
					strcat(qratoutputname, "_qratcheck.qrat");
					//outputname = strcat(argv[i + 1], ".cnf");
					//extoutputname = strcat(argv[i + 1], "_ext.qcnf");
					//qratoutputname = strcat(argv[i + 1], "_qratcheck.qrat");
				}
			}
		}
	}
	Cnf* output;
	QCNF formula;
	QCNF output_formula;
	ClausalProof proof;

	if (file_reading) {
		strcpy(qrpname, fname);
		strcpy(qdimacsname, fname);
		strcat(qrpname, ".qrp");
		strcat(qdimacsname, ".qdimacs");
		printf("searching for .qrp and .qdimacs extension pairs:\n");
		printf(qrpname); printf(" and "); printf(qdimacsname);
		FILE* qdimacs = fopen(qdimacsname, "r");
		printf("found qdimacs file \n");
		printf("loading into formula \n");
		formula = read_qdimacs(qdimacs);
		//formula.matrix.mvar = formula.matrix.calculate_max_var();
		formula.matrix.update_max_var();
		printf("formala succesfully loaded \n");
		fclose(qdimacs);
		printf("closing qdimacs file \n");


		FILE* qrp = fopen(qrpname, "r");
		proof = read_qrp(qrp);
		fclose(qrp);
		printf("found qrp file \n");
	}

	else {
		formula = QParity(5);
		proof = lqrcQParity(5);

		if (file_writing) {
			const char* default_qdimacs = "example.qdimacs";
			const char* default_qrp = "example.qrp";
			if (remove(default_qdimacs) != 0)
			{
				printf("No file to replace creating new %s file\n", default_qdimacs);
			}
			if (remove(default_qrp) != 0)
			{
				printf("No file to replace creating new %s file\n", default_qrp);
			}
			//*qdimacsname = char();

			//qdimacsname[0] = 'e'; qdimacsname[1] = 'x'; qdimacsname[2] = 'a'; qdimacsname[3] = 'm'; qdimacsname[4] = 'p'; qdimacsname[5] = 'l'; qdimacsname[6] = 'e';

			//char* dfname = [ 'e', 'x', 'a','m', 'p', 'l', 'e'];
			strcpy(qrpname, new char());
			strcpy(qdimacsname, new char());
			strcat(qrpname, "example");
			strcat(qdimacsname, "example");
			strcat(qrpname, ".qrp");
			strcat(qdimacsname, ".qdimacs");
			printf("searching for .qrp and .qdimacs extension pairs\n");

			FILE* qdimacsfile = fopen(qdimacsname, "w+");
			formula.print(qdimacsfile);
			fclose(qdimacsfile);

			FILE* qrpfile = fopen(qrpname, "w+");
			print_qrc(qrpfile, formula, proof);
			fclose(qrpfile);
			printf("searching for .qrp and .qdimacs extension pairs\n");

			FILE* qdimacs = fopen(qdimacsname, "r");
			formula = read_qdimacs(qdimacs);
			formula.matrix.update_max_var();
			fclose(qdimacs);
			printf("found qdimacs file \n");

			FILE* qrp = fopen(qrpname, "r");
			proof = read_qrp(qrp);
			fclose(qrp);
			printf("found qrp file \n");
		}
	}

	start = std::clock();
	multilinear::Strategy_Extractor* ClausalExtractor = multilinear::Extract(&formula, &proof, proof.length - 1, 1);
	*(ClausalExtractor->output_cnf) = ccopy(formula.matrix);
	copyinto((ClausalExtractor->output_cnf), (ClausalExtractor->extension_clauses));
	copyinto((ClausalExtractor->output_cnf), (ClausalExtractor->negated_assumptions));
	ClausalExtractor->output_cnf->update_max_var();
	output = ClausalExtractor->output_cnf;//should be this
	output_formula.prefix = copy(*ClausalExtractor->long_prefix);
	copyinto(&output_formula.matrix, &formula.matrix);
	output_formula.matrix.mvar = ClausalExtractor->idx_max_var;
	//output = ClausalExtractor->extension_clauses;//remove this later
	duration = (std::clock() - start) / (double)CLOCKS_PER_SEC;

	Link1<Clause>* current = ClausalExtractor->output_cnf->head;
	while (current != NULL) {
		if (current->data.length == 0) {
			printf("Found empty clause in output");
			//printf()
		}
		current = current->next;
	}

	if (file_writing) {
		if (file_reading) {
			FILE* cnffile = fopen(outputname, "w+");
			output->print_dimacs(cnffile);
			fclose(cnffile);
			FILE* pcnffile = fopen(extoutputname, "w+");
			output_formula.print(pcnffile);
			fclose(pcnffile);
			FILE* qratfile = fopen(qratoutputname, "w+");
			ClausalExtractor->output_QRAT->print(qratfile);
			fclose(qratfile);
		}
		else {
			FILE* cnffile = fopen("output.cnf", "w+");
			output->print_dimacs(cnffile);
			fclose(cnffile);
			FILE* pcnffile = fopen("output_ext.pcnf", "w+");
			output_formula.print(pcnffile);
			fclose(pcnffile);
			FILE* qratfile = fopen("output_qratcheck.qrat", "w+");
			ClausalExtractor->output_QRAT->print(qratfile);
			fclose(qratfile);
		}

	}
	else {//comment out for release
		//std::cout << endl << "DEBUG TOOL: printing to output.cnf, DISABLE on release"<< endl;
		//FILE* cnffile = fopen("output.cnf", "w+");
		//output->print_dimacs(cnffile);
		//fclose(cnffile);
	}
	std::cout << std::endl << "time for constructing CNF " << duration << std::endl;
	std::cout << std::endl << "number of new variables " << output->calculate_max_var() - formula.matrix.mvar << std::endl;
}

int main(int argc, char** argv)
{
	//whilemultitest(5);
	//exprestest(5);
	//circuittest(0);
	//localtest(0);
	pseudomain(argc, argv);
	//cout << "Hello CMake." << endl;
	//testmultilinear(5);
	return 0;
}
