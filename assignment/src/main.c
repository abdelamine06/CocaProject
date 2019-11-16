/**
* @file main.c contains the main function of the program
* @author Bah elhadj amadou and Abdelamine
* @date 2019
*/


#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>

#include "Graph.h"
#include "Parsing.h"
#include "Solving.h"
#include "Z3Tools.h"

bool PRINT_PATH = false;
bool WRITE_PATH_IN_DOT_FILE = false;
bool TEST_SEPARATLY_BY_DEEPTH = false; 
bool TEST_ALL = false;
bool PRINT_FORMULA = false;
bool DECREASING_ORDER = false;


/**
* @brief usage print a help to the user of the program
*/
void usage();

/**
* @brief findPath find paths by testing formula separatly by depth
* @param ctx the context of the solver
* @param graphs all graphs
* @param numGraphs number of graphs
*/
void findPath( Z3_context ctx, Graph *graphs,unsigned int numGraphs);


int main(int argc, char* argv[])
{
	int VERBOSE = false;
	if(argc < 2) {
		usage();
		exit(EXIT_FAILURE);
	}
	
    Z3_context context = makeContext();
	Graph graphs[argc - 1];

	int numberGraphs = 0;
	for(int i=0; i<argc-1; i++)
	{
		bool option = false;
		if(strcmp("-h", argv[i+1])==0){
			usage();
			exit(EXIT_SUCCESS);
		}
		if(strcmp("-v", argv[i+1])==0){
			VERBOSE = true;
			option = true;
		}
		if(strcmp("-F", argv[i+1])==0){
			PRINT_FORMULA = true;
			option = true;
		}
		if(strcmp("-t", argv[i+1])==0){
			PRINT_PATH = true;
			option = true;
		}
		if(strcmp("-f", argv[i+1])==0){
			WRITE_PATH_IN_DOT_FILE= true;
			option = true;
		}
		if(strcmp("-s", argv[i+1])==0){
			TEST_SEPARATLY_BY_DEEPTH = true;
			option = true;
		}
		if(strcmp("-a", argv[i+1])==0){
			if(TEST_SEPARATLY_BY_DEEPTH == true){
				TEST_ALL= true;
				option = true;
			}else{
				fprintf(stderr, "You must use -s before -a\n");
				exit(EXIT_FAILURE);
			}
		}
		if(strcmp("-d", argv[i+1])==0){
			if(TEST_SEPARATLY_BY_DEEPTH == true){
				DECREASING_ORDER = true;
				option = true;
			}else
			{
				fprintf(stderr, "You must use -s before -d\n");
				exit(EXIT_FAILURE);
			}
		}

		if(!option){
			graphs[numberGraphs++] = getGraphFromFile(argv[i+1]); 
		}
	}
	
	if(VERBOSE)
	{
		for(int i=0; i<numberGraphs; i++)
			printGraph(graphs[i]);
		printf("\n");
	}
	if(TEST_SEPARATLY_BY_DEEPTH)
		findPath(context, graphs, numberGraphs);
	else
	{
		Z3_ast fullFormula = graphsToFullFormula(context, graphs, numberGraphs);	
		if(isFormulaSat(context, fullFormula))
		{
			printf("OUI\n");
		}
		else
			printf("NON\n");
		if(PRINT_FORMULA)
			printf("FULL FORMULA: %s\n", Z3_ast_to_string(context, fullFormula));
	}

	Z3_del_context(context);
	return EXIT_SUCCESS;
}

void usage(){
	printf("Use: equalPath [options] files...\neach file should contain a graph in dot format.\ntest if there exists a length n such that each input graph has a valid simple path of length n.\n");
	printf("OPTIONS:\n");
	printf("-h	displays this help\n");	
	printf("-v	activate verbose mode (display graphs)\n");
	printf("-F	displays the formula computed\n");
	printf("-s	tests separatly all formulas by depth\n");
	printf("-d	only if -s is present. Explore the length by decreasing order\n");
	printf("-a	only if -s is present. Computes a result for every length\n");
	printf("-t	displays the path found on the terminal\n");
	printf("-f	write the result with color in a dot file\n");
} 

void findPath( Z3_context ctx, Graph *graphs,unsigned int numGraphs)
{
	int min_vertices = orderG(graphs[0]);
	
	for(int i=1; i<numGraphs; i++)
	{
		if(orderG(graphs[i]) < min_vertices)
			min_vertices = orderG(graphs[i]);	
	}

	Z3_ast formula;
	Z3_ast tabFormula[min_vertices];

	int k=0, step = 1;
	if(DECREASING_ORDER)
	{
		k=min_vertices-1;
		step = -1;
	}
	int count = 0;
	while(count <= min_vertices - 1)
	{
		tabFormula[k] = graphsToPathFormula(ctx, graphs, numGraphs, k);
		if(isFormulaSat(ctx, tabFormula[k]) == Z3_L_TRUE)
		{
			printf("There is a simple valide path of length %d in all graphs.\n", k);
			if(PRINT_PATH){
				Z3_model model = getModelFromSatFormula(ctx, tabFormula[k]);
				printPathsFromModel(ctx, model, graphs, numGraphs, k);	
			}
			if(WRITE_PATH_IN_DOT_FILE){
				Z3_model model = getModelFromSatFormula(ctx, tabFormula[k]);
				char name[15];
				sprintf(name, "result-l%d.dot%c", k, '\0');
				createDotFromModel(ctx, model, graphs, numGraphs, k, name); 
			}
			if(PRINT_FORMULA)
				printf("FORMULA FOR PATH OF LENGHT %d : %s\n", k, Z3_ast_to_string(ctx, tabFormula[k]));
			if(!TEST_ALL)
				break;
		}
		else if(isFormulaSat(ctx, tabFormula[k]) == Z3_L_FALSE)
		{
			if(TEST_SEPARATLY_BY_DEEPTH || TEST_ALL)
				printf("no simple valide path of length %d.\n", k);
		}
		k += step;
		count++;
	}
}
