/**
 * @file Solving.c
 * @author Bah Elhadj amadou et Abdelamine Mehdaoui 
 * @brief An implementation of \ref Solving.h function's
 * @date 2019
 */


#include "Solving.h"
#include "Z3Tools.h"
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>


#define MAX_ORDER_G			100				// represents the maximum of nodes which can have a graph. In this project it's 90. Increase it if necessary
#define OPTIMIZE			true// if true formulas will be optimized for the solver (reducing the number of variables in the formulas). \ref optimizeAndMakeFormula
#define FILE_SIZE			1000
#define NODE_VARIABLE_SIZE  10 

/**
*\struct nodePos 
*\brief represents a node and its position wich is the type of elements in \ref File_t
*/
typedef struct nodePos{
	unsigned int node;
	unsigned int position;
}fileElement_t;

/**
*\struct File_s 
*\brief represents a file
*/
typedef struct File_s{
	fileElement_t tab[FILE_SIZE];
	unsigned int size;
	unsigned int currentPos;
}File_t;

/**
* @brief isEmpty tests if a file is empty or not
* @param file is the file to check
* @return true if the file is empty and False otherwise
*/
bool isEmpty(File_t *file);

/**
* @brief pull get and delete the element at the top of the file
* @param file is the file
* @return the element on the top of the file
*/
fileElement_t pull(File_t *file);

/**
* @brief push add an element at the end of the file
* @param file is the file
* @param element is the element to add
*/
void push(File_t *file, fileElement_t element);

/**
* @brief print a file
* @param file the file to print
*
* This function is used for debug
*/
void printFile(File_t *file);

/**
* @brief get the first element in the file
* @param file the file
* @return the element
*
* this function don't delete the element in the file
*/
fileElement_t top(File_t* file);

/**
* @brief get the source node in a graph
* @param graph the graph
* @return the source node in the graph @p graph
*/
int getSouceNode(Graph graphe);

/**
* @brief get the target node in a graph
* @param graph the graph
* @return the target node in the graph @p graph
*/
int getTargetNode(Graph graphe);

/**
* @brief makeValidFormula make a formula wich is satisfiable only if the the graph has a valid path of @p pathLength
* @param ctx the context of the solver
* @param graph the graph 
* @param number the graph number
* @param pathLength the pathLength of the path
* @return a formula wich is satisfiable if the graph has a valid path of length pathLengh
*/
Z3_ast makeValidFormula(Z3_context ctx, Graph graph, int number, int pathLength);

/**
* @brief makeSimpleFormula make a formula wich is satisfiable only if the graph has a simple path of length @p pathLength 
* @param ctx the context of the solver
* @param graph the graph 
* @param number the graph number
* @param pathLength the pathLength of the path
* @param nodeTab an array of arrays wich contain the possible nodes for each position in the path
* @return the maked formula 
*/
Z3_ast makeSimpleFormula(Z3_context ctx, Graph graph, int number, int pathLength, int nodeTab[][MAX_ORDER_G]);

/**
* @brief makePathFormula make a formula wich is satisfiable only if the graph has a path of length @p pathLength
* @param ctx the context of the solver
* @param graph the graph 
* @param number the graph number
* @param pathLength the pathLength of the path
* @param nodeTab an array of arrays wich contain the possible nodes for each position in the path
* @return the maked formula 
*/
Z3_ast makePathFormula(Z3_context ctx, Graph graph, int number, int pathLength, int nodeTab[][MAX_ORDER_G]);


/**
* @brief optimizeAndMakeFormula optimize or not the formula by reducing the number of nodes to use in the formula and then make formula
* @param graph the graph used to make formula
* @param ctx the context of the solver
* @param number the graph number
* @param pathLength the path's length
* @return a formula witch is satisfiable only if the graph has a simple accepting path of length @p pathLength
*/
Z3_ast optimizeAndMakeFormula(Graph graph, Z3_context ctx, int number, int pathLength);

/**
* @brief makeAnd make a formula wich is an AND between two formulas
* @param ctx the context of the solver
* @param formula1 the first formula
* @param formula2 the second formula
*/
Z3_ast makeAnd(Z3_context ctx,Z3_ast formula1, Z3_ast formula2);

/*
* used just for debug
*/
void printIsSat(Z3_context contex, Z3_ast	formula, char* formulaName);



Z3_ast getNodeVariable(Z3_context ctx, int number, int position, int k, int node)
{
	char varName[NODE_VARIABLE_SIZE];
	sprintf(varName,"X%d,%d,%d,%d", number, position, k, node);
	Z3_ast var = mk_bool_var(ctx, varName);
	return var;
}

Z3_ast graphsToPathFormula( Z3_context ctx, Graph *graphs,unsigned int numGraphs, int pathLength)
{
	Z3_ast formula;
	Z3_ast tabFormula[numGraphs];
	for(int i=0; i<numGraphs; i++)
	{
		int node = getSouceNode(graphs[i]);
		tabFormula[i] = optimizeAndMakeFormula(graphs[i], ctx, i ,pathLength);	
	}
	formula = Z3_mk_and(ctx, numGraphs, tabFormula);
	return formula;
}



Z3_ast graphsToFullFormula( Z3_context ctx, Graph *graphs,unsigned int numGraphs)
{
	int min_vertices = orderG(graphs[0]);
	for(int i=1; i<numGraphs; i++)
	{
		if(orderG(graphs[i]) < min_vertices)
			min_vertices = orderG(graphs[i]);	
	}
	Z3_ast formula;
	Z3_ast tabFormula[min_vertices];
	int k=0;
	while(k <= min_vertices - 1)
	{
		tabFormula[k] = graphsToPathFormula(ctx, graphs, numGraphs, k);
		if(isFormulaSat(ctx, tabFormula[k]) == Z3_L_TRUE)
			break;
		k++;
	}
	formula = Z3_mk_or(ctx, k+1, tabFormula);
	return formula;
}

void printPathsFromModel(Z3_context ctx, Z3_model model, Graph *graphs, int numGraph, int pathLength)
{
	int nodesPath[numGraph][pathLength + 1];	// will contain the path for each graph

	/* for each graph, for each node check if it is true between 0 to pathLength. IF it's true this node belongs to the path */
	for(int numCurrentGraph=0; numCurrentGraph<numGraph; numCurrentGraph++)
	{
		for(int node=0; node<orderG(graphs[numCurrentGraph]); node++)
		{
			for(int posInPath=0; posInPath<=pathLength; posInPath++)
			{
				char varName[NODE_VARIABLE_SIZE];
				sprintf(varName,"X%d,%d,%d,%d", numCurrentGraph, posInPath, pathLength, node);
				Z3_ast var = mk_bool_var(ctx, varName);
				int nodeValuation = valueOfVarInModel(ctx, model, var);
				if(nodeValuation == 1)
				{
					nodesPath[numCurrentGraph][posInPath] = node;
					break;
				}
			}
		}
	}

	/* for each graph print the path found*/
	for(int numCurrentGraph=0; numCurrentGraph<numGraph; numCurrentGraph++)
	{
		printf("path in graph%d.\n", numCurrentGraph);
		for(int posInPath=0; posInPath<=pathLength; posInPath++)
		{
			if(posInPath<pathLength)
				printf("%s-->", getNodeName(graphs[numCurrentGraph], nodesPath[numCurrentGraph][posInPath]));
			else
				printf("%s\n", getNodeName(graphs[numCurrentGraph], nodesPath[numCurrentGraph][posInPath]));
		}
	}
}


void createDotFromModel(Z3_context ctx, Z3_model model, Graph *graphs, int numGraph, int pathLength, char* name)
{
	int nodesPath[numGraph][pathLength + 1];
	char pathName[strlen(name) + 5];
	sprintf(pathName, "sol/");
	
	FILE *fd = fopen(strcat(pathName, name), "w");

	if(fd == NULL){
		fprintf(stderr, "Error when opening file\n");
		exit(EXIT_FAILURE);
	}

	char line[100];
	char solutionName[13];
	sprintf(solutionName, "Sol_Length%d", pathLength);
	sprintf(line, "digraph %s {\n", solutionName);
	fputs(line, fd);

	/* for each graph, write it in a dot file with colors witch show the path */
	for(int i=0; i<numGraph; i++)
	{
		/* checking the path for the graph */
		for(int node=0; node<orderG(graphs[i]); node++)
		{
			for(int posInPath=0; posInPath<=pathLength; posInPath++)
			{
				char varName[NODE_VARIABLE_SIZE];
				sprintf(varName,"X%d,%d,%d,%d", i, posInPath, pathLength, node);
				Z3_ast var = mk_bool_var(ctx, varName);
				int nodeValuation = valueOfVarInModel(ctx, model, var);
				if(nodeValuation == 1)
				{
					nodesPath[i][posInPath] = node;
					break;
				}
			}
		}
		
		/* writing the source node and the target node */
		int sourceNode = getSouceNode(graphs[i]);
		int targetNode = getTargetNode(graphs[i]);
		sprintf(line, "\t_%d_%s [initial=1, color=green] [style=filled, fillcolor=lightblue];\n", i, getNodeName(graphs[i], sourceNode)); 
		fputs(line, fd);
		sprintf(line, "\t_%d_%s [final=1, color=red] [style=filled, fillcolor=lightblue];\n", i, getNodeName(graphs[i], targetNode)); 
		fputs(line, fd);

		/* writing all nodes (without the source and the target) */
		for(int node=0; node<orderG(graphs[i]); node++)
		{

			if(node != sourceNode && node != targetNode){
				int k = 0;
				while(k<pathLength+1 && nodesPath[i][k] != node)
					k++;	
				if(k == pathLength + 1)
					fprintf(fd, "\t_%d_%s ;\n", i, getNodeName(graphs[i], node));
				else
					fprintf(fd, "\t_%d_%s [style=filled, fillcolor=lightblue];\n", i, getNodeName(graphs[i], node));
			}
		}

		/* writting edges */
		for(int node=0; node<orderG(graphs[i]); node++)
		{
			for(int nodeBis=0; nodeBis<orderG(graphs[i]); nodeBis++)
			{
				if(isEdge(graphs[i], node, nodeBis))
				{
					int k=0;
					while(k<pathLength+1 && nodesPath[i][k] != node)
						k++;
					
					if(k<pathLength+1 && nodesPath[i][k+1] == nodeBis && node != targetNode)
						fprintf(fd, "\t_%d_%s -> _%d_%s [color=blue];\n", i, getNodeName(graphs[i], node), i, getNodeName(graphs[i], nodeBis));
					else
						fprintf(fd, "\t_%d_%s -> _%d_%s ;\n", i, getNodeName(graphs[i], node), i, getNodeName(graphs[i], nodeBis));
				}
			}
		}
	}
	fprintf(fd, "}\n");
	fclose(fd);
}


int getSolutionLengthFromModel(Z3_context ctx, Z3_model model, Graph *graphs)
{	
	unsigned int graphNumber = 0;
	unsigned int solutionLength = 0;
	int sourceNode = getSouceNode(graphs[graphNumber]);
	int targetNode = getTargetNode(graphs[graphNumber]);
	
	/*
	* we search the size of the solution just by using the graph 0 . It is not necessary to check the path for each graph
	* because they all have the same pathLength in the model
	*/

	/* tring from solutionLength equal to 0 until we find the right solutionLength */
	while(solutionLength < orderG(graphs[graphNumber]))
	{
		int currentNode = sourceNode;
		for(int pos=0; pos<=solutionLength; pos++)
		{
			if(pos == solutionLength)
			{
				Z3_ast varSourceNode = getNodeVariable(ctx, graphNumber, 0, solutionLength, sourceNode);
				Z3_ast varTargetNode= getNodeVariable(ctx, graphNumber, solutionLength, solutionLength, targetNode);
				if(valueOfVarInModel(ctx, model, varSourceNode) == 1 && valueOfVarInModel(ctx, model, varTargetNode) == 1)
					return solutionLength;
				else
					break;
			}
			int lastCurrentNode = currentNode;
			for(int neighbour=0; neighbour<orderG(graphs[graphNumber]); neighbour++)
			{
				if(isEdge(graphs[graphNumber], currentNode, neighbour))
				{
					Z3_ast var = getNodeVariable(ctx, graphNumber, pos + 1, solutionLength, neighbour);
					if(valueOfVarInModel(ctx, model, var) == 1)
					{
						currentNode = neighbour;	
						break;
					}
				}
			}
			if(currentNode == lastCurrentNode)
				break;
		}
		
		solutionLength +=1;
	}

	fprintf(stderr, "this case should not happen\n"); /* this case will not happen */
	exit(EXIT_FAILURE);
	return solutionLength;			// just to make gcc happy (desabling warnings)
}

Z3_ast makeValidFormula(Z3_context ctx, Graph graph, int number, int pathLength)
{
	unsigned int tabFormulaSize = orderG(graph) + 1;
	Z3_ast tabFormulaOr[tabFormulaSize];
	int source = getSouceNode(graph);
	int target = getTargetNode(graph);
	tabFormulaOr[0] = getNodeVariable(ctx, number, 0, pathLength, source);
	tabFormulaOr[1] = getNodeVariable(ctx, number, pathLength, pathLength, target);
	int node;
	Z3_ast formula; 

	int i=2;
	for(int node=0; node<orderG(graph); node++){
		if(node != target)
		{
			formula = getNodeVariable(ctx, number, pathLength, pathLength, node); 
			tabFormulaOr[i++] = Z3_mk_not(ctx, formula);
		}
	}
	formula = Z3_mk_and(ctx, tabFormulaSize ,tabFormulaOr);
	return formula;
}

Z3_ast makeSimpleFormula(Z3_context ctx, Graph graph, int number, int pathLength, int nodeTab[][MAX_ORDER_G])
{
	int sizeTabFormulaAnd1 = pathLength + 1;	
	Z3_ast tabFormulaAnd1[sizeTabFormulaAnd1];
	int indiceTabFormulaAnd1 = 0;
	Z3_ast formula;

	for(int pos=0; pos<=pathLength; pos++)
	{
		int sizeTabFormulaOr = 0;
		while(nodeTab[pos][sizeTabFormulaOr] != -1)
			sizeTabFormulaOr += 1;
		int sizeTabFormulaAnd2 = pathLength + sizeTabFormulaOr;
		Z3_ast tabFormulaOr[sizeTabFormulaOr];

		int indiceTabFormulaOr = 0;
		for(int i=0; i<sizeTabFormulaOr; i++)
		{
			Z3_ast tabFormulaAnd2[sizeTabFormulaAnd2];
			int indiceTabFormulaAnd2 = 0;
			tabFormulaAnd2[indiceTabFormulaAnd2++] = getNodeVariable(ctx, number, pos, pathLength,nodeTab[pos][i]);
			for(int j=0; j<sizeTabFormulaOr; j++)
			{
				if(i != j)
				{
					Z3_ast var = getNodeVariable(ctx, number, pos, pathLength,nodeTab[pos][j]);
					var = Z3_mk_not(ctx, var);
					tabFormulaAnd2[indiceTabFormulaAnd2++] = var;
				}
			}

			for(int j=0; j<=pathLength; j++)
			{
				if(j!=pos)
				{
					Z3_ast var = getNodeVariable(ctx, number, j, pathLength,nodeTab[pos][i]);
					var = Z3_mk_not(ctx, var);
					tabFormulaAnd2[indiceTabFormulaAnd2++] = var;
				}
			}
			tabFormulaOr[indiceTabFormulaOr++] = Z3_mk_and(ctx, sizeTabFormulaAnd2, tabFormulaAnd2);
		}
		if(sizeTabFormulaOr != 1)
			tabFormulaAnd1[indiceTabFormulaAnd1++] = Z3_mk_or(ctx, sizeTabFormulaOr, tabFormulaOr);
		else
			tabFormulaAnd1[indiceTabFormulaAnd1++] = tabFormulaOr[0];
	}
	formula = Z3_mk_and(ctx, sizeTabFormulaAnd1, tabFormulaAnd1); 
	return formula;
}

Z3_ast makePathFormula(Z3_context ctx, Graph graph, int number, int pathLength, int nodeTab[][MAX_ORDER_G])
{
	Z3_ast tabAnd1[pathLength];
	int indiceTabAnd1 = 0;
	for(int pos=0; pos<pathLength; pos++)
	{
		int sizeTabAnd2= 0;
		while(nodeTab[pos][sizeTabAnd2] != -1)
			sizeTabAnd2+= 1;
		Z3_ast tabAnd2[sizeTabAnd2];
		int indiceTabAnd2 = 0;

		for(int i=0; i<sizeTabAnd2; i++)
		{
			int numberNeighbours = 0;
			int tabNeighbour[orderG(graph)];
			for(int node=0; node<orderG(graph); node++)
			{
				if(isEdge(graph, nodeTab[pos][i], node))
				{
					tabNeighbour[numberNeighbours++] = node;
				}
			}
			Z3_ast tabOr[numberNeighbours];
			unsigned int indiceTabOr = 0;

			Z3_ast var = getNodeVariable(ctx, number, pos, pathLength, nodeTab[pos][i]);
			var = Z3_mk_not(ctx, var);
			tabOr[indiceTabOr++] = var;
			
			for(int k=0; k<numberNeighbours; k++)
			{
				Z3_ast var = getNodeVariable(ctx, number, pos+1, pathLength, tabNeighbour[k]);
				tabOr[indiceTabOr++] = var;
			}

			tabAnd2[indiceTabAnd2++] = Z3_mk_or(ctx, numberNeighbours+1, tabOr);
		}
		tabAnd1[indiceTabAnd1++] = Z3_mk_and(ctx, sizeTabAnd2, tabAnd2);
	}
	
	Z3_ast formula = Z3_mk_and(ctx, pathLength, tabAnd1);

	return formula;
}

Z3_ast makeAnd(Z3_context ctx,Z3_ast formula1, Z3_ast formula2)
{
	Z3_ast tabFormula[2] = {formula1, formula2};
	Z3_ast formula = Z3_mk_and(ctx, 2, tabFormula);
	return formula;
}

Z3_ast optimizeAndMakeFormula(Graph graph, Z3_context ctx, int number, int pathLength)
{
	int possibilities[pathLength+1][MAX_ORDER_G];
	int fathers[orderG(graph)][orderG(graph)];

	if(OPTIMIZE){
		for(int i=0; i<=pathLength; i++)
		{
			for(int j=0; j<MAX_ORDER_G; j++)
			{
				possibilities[i][j] = -1;
			}
		}

		for(int i=0; i<orderG(graph); i++)
		{
			for(int j=0; j<orderG(graph); j++)
			{
				fathers[i][j] = -1;
			}
		}

		File_t file;
		file.currentPos = 0;

		fileElement_t element = {getSouceNode(graph), 0};
		push(&file, element);

		while(!isEmpty(&file))
		{
			fileElement_t element = top(&file);
			if(element.position > pathLength)
				break;

			int exist = 0;
			for(int i=0; i<orderG(graph); i++){
				if(possibilities[element.position][i] == element.node)
				{
					exist = 1;	
					break;
				}
				if(possibilities[element.position][i] == -1){
					possibilities[element.position][i] = element.node;
					break;
				}
			}
			if(exist == 0){
				for(int neighbour=0; neighbour<orderG(graph); neighbour++)
				{
					if(isEdge(graph, element.node, neighbour) && (neighbour != element.node))
					{
						fileElement_t newElement = {neighbour, element.position + 1};
						push(&file, newElement);	
					}
				}
			}
			pull(&file);
		}
	}else{
		for(int i=0; i<=pathLength; i++)
		{
			for(int j=0; j<MAX_ORDER_G; j++)
			{
				if(j<orderG(graph))
					possibilities[i][j] = j;
				else
					possibilities[i][j] = -1;
			}
		}
	}

	Z3_ast formulaValide = makeValidFormula(ctx, graph, number, pathLength);
	Z3_ast formulaSimple = makeSimpleFormula(ctx, graph, number, pathLength, possibilities);
	Z3_ast formulaPath = makePathFormula(ctx, graph, number, pathLength, possibilities); 
	Z3_ast formula = makeAnd(ctx, formulaValide, formulaSimple); 
	formula = makeAnd(ctx, formulaPath, formula);

	return formula;
}

bool isEmpty(File_t *file)
{
	return file->currentPos == 0;
}

fileElement_t top(File_t* file)
{
	fileElement_t element;
	if(!isEmpty(file))
		element = file->tab[0];
	else{
		fprintf(stderr, "error: you can't call 'top' in an empty file\n");
		exit(EXIT_FAILURE);
	}
	return element;

}

fileElement_t pull(File_t *file)
{
	fileElement_t element;
	if(!isEmpty(file))
		element = file->tab[0];
	else{
		fprintf(stderr, "error: you can't call 'pull' in an empty file\n");
		exit(EXIT_FAILURE);
	}
	for(int i=1; i<file->currentPos; i++)
		file->tab[i-1] = file->tab[i];
	file->currentPos -= 1;
	return element;
}

void push(File_t *file, fileElement_t element)
{
	if(file->currentPos<FILE_SIZE)
		file->tab[file->currentPos] = element;
	else
	{
		printf("Erreur: full file\n");
		exit(EXIT_FAILURE);
	}
	file->currentPos += 1;
}

void printFile(File_t *file)
{
	for(int i=0; i<file->currentPos; i++)
	{
		printf(" %d", file->tab[i]);
	}
	printf("\n");
	if(file->currentPos == 0)
		printf("empty file\n");
}



int getSouceNode(Graph graphe)
{
	int node;
	for(node=0;node<orderG(graphe) && !isSource(graphe,node);node++);
	return node;
	
}

int getTargetNode(Graph graphe)
{
	int node;
	for(node=0;node<orderG(graphe) && !isTarget(graphe,node);node++);
	return node;
}

void printIsSat(Z3_context contex, Z3_ast	formula, char* formulaName)
{
	printf("==> %s:\n", formulaName);
	switch(isFormulaSat(contex, formula)){
		case Z3_L_FALSE:
			printf("==> %s is not satisfiable.\n", Z3_ast_to_string(contex, formula));
			break;
		case Z3_L_TRUE:
			printf("==> %s is satisfiable.\n", Z3_ast_to_string(contex, formula));
			break;
		case Z3_L_UNDEF:
			printf("==> We don't know if %s is satisfiable.\n",Z3_ast_to_string(contex, formula));
			break;
	}
}
