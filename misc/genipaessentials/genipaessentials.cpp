/*
 * essentials.cpp
 *
 *  Created on: Feb 3, 2015
 *      Author: Tomas Balyo, KIT
 */

extern "C" {
    #include "ipasir.h"
}

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <vector>

int getDualRailName(int lit) {
	if (lit == 0) {
		return 0;
	}
	if (lit > 0) {
		return 2*lit;
	} else {
		return 2*(-lit) - 1;
	}
}

/**
 * Reads a formula from a given file and transforms it using the dual rail encoding,
 * i.e., replaces each x by px and each \overline{x} by nx. Also adds clauses
 * of the form (\overline{px} \vee \overline{nx})
 */
bool loadFormulaDualRailed(void* solver, const char* filename, int* outVariables) {
	FILE* f = fopen(filename, "r");
	if (f == NULL) {
		return false;
	}
	int maxVar = 0;
	int c = 0;
	bool neg = false;
	while (c != EOF) {
		c = fgetc(f);

		// comment or problem definition line
		if (c == 'c' || c == 'p') {
			// skip this line
			while(c != '\n') {
				c = fgetc(f);
			}
			continue;
		}
		// whitespace
		if (isspace(c)) {
			continue;
		}
		// negative
		if (c == '-') {
			neg = true;
			continue;
		}

		// number
		if (isdigit(c)) {
			int num = c - '0';
			c = fgetc(f);
			while (isdigit(c)) {
				num = num*10 + (c-'0');
				c = fgetc(f);
			}
			if (neg) {
				num *= -1;
			}
			neg = false;

			if (abs(num) > maxVar) {
				maxVar = abs(num);
			}
			// add to the solver
			ipasir_add(solver, getDualRailName(num));
		}
	}
	fclose(f);
	// add the extra clauses
	for (int var = 1; var <= maxVar; var++) {
		ipasir_add(solver, -getDualRailName(var));
		ipasir_add(solver, -getDualRailName(-var));
		ipasir_add(solver, 0);
	}
	*outVariables = maxVar;
	return true;
}

int lunits = 0;
int lbins = 0;
int lterns = 0;

void learnCb(void* state, int* clause) {
	if (clause[1] == 0) lunits++;
	if (clause[2] == 0) lbins++;
	if (clause[3] == 0) lterns++;
}

int main(int argc, char **argv) {
	printf("Using the incremental SAT solver %s.\n", ipasir_signature());

	if (argc != 2) {
		puts("USAGE: ./genipaessentials <dimacs.cnf>");
		return 0;
	}

	puts("Given a satisfiable formula F and a variable x, we say that x is");
	puts("essential for the satisfiability of F if a truth value (True or False)");
	puts("must be assigned to x in each satisfying assignment of F. This application");
	puts("finds all the variables essential for the satisfiability of a given formula.");

	void *solver = ipasir_init();
	ipasir_set_learn(solver, NULL, 3, learnCb);
	int variables = 0;
	bool loaded = loadFormulaDualRailed(solver, argv[1], &variables);

	if (!loaded) {
		printf("The input formula \"%s\" could not be loaded.\n", argv[1]);
		return 0;
	}

	int satRes = ipasir_solve(solver);

	if (satRes == 20) {
		puts("The input formula is unsatisfiable.");
		return 0;
	}

	std::vector<int> essentialVariables;
	for (int var = 1; var <= variables; var++) {
		printf("Testing if variable %d (out of %d) is essential for satisfiability.\n", var, variables);
		ipasir_assume(solver, -getDualRailName(var));
		ipasir_assume(solver, -getDualRailName(-var));
		satRes = ipasir_solve(solver);
		if (satRes == 10) {
			printf("Variable %d IS NOT essential for satisfiability.\n", var);
		} else {
			printf("Variable %d IS essential for satisfiability.\n", var);
			essentialVariables.push_back(var);
		}
	}
	int essentials = (int)essentialVariables.size();
	printf("SUMMARY: %d of %d (%0.2f%%) of variables is essential for satisfiability.\n",
			essentials, variables, 100.0*essentials/variables);
	puts("The list of variables eseential for satisfiability:");
	for (size_t i = 0; i < essentialVariables.size(); i++) {
		printf("%d ", essentialVariables[i]);
	}
	printf("\n");
	printf("The solver shared %d unit, %d binary and %d ternary clauses.\n", lunits, lbins, lterns);
	return 0;
}
