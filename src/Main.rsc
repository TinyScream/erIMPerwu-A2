/*
	Author: Hong Zhang, Pieter Derks
	2IMP25 A2
*/
module Main

import IO;
import ListRelation;
import vis::Figure; 
import vis::Render;
import Set;
import List;
import Type;
import Map;
import Relation;
import String;
import util::ValueUI;
import util::Math;
import vis::Figure;

import lang::java::flow::JavaToObjectFlow;
import analysis::flow::ObjectFlow;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;

import util::Benchmark; //time records

import Suggestion;

public M3 m3Model; //M3 model from project
public FlowProgram prog; 
public OFG ofg;
public OFG proOfg; //propagate ofg

public OFG typeDependency;
public OFG typeDependencyInterface;
public OFG derivedType;
public OFG typeMissed;
public OFG declaration;

private lrel[loc field, set[loc] classSet, loc interface] SuggestionRelList1 = [];

public void tellSuggestion() = tellSuggestion(|project://eLib|);

public void tellSuggestion(loc project_loc){
	before = userTime();

	setUpModel(project_loc);	//m3, p, ofg proOfg...
        
    OFG tem = {pair|pair <- proOfg, 
    					   pair[0].scheme == "java+field" && pair[1].scheme == "java+class"};
    typeMissed = {t|t <- tem, td <- typeDependency, td[0] == t[0] && td[1].scheme == "java+interface"};
    	
    	
   	SuggestionRelList1 =  Suggestion::getSuggestionList(typeMissed, typeDependencyInterface);
    
    Suggestion::printSuggestion(declaration, derivedType);
    
    println("time taken: " + toString(userTime() - before));
    
    Suggestion::testing();
    
}

private void setUpModel(loc project_loc){
	/*
	ofg and propagate ofg part
	*/
	m3Model = createM3FromEclipseProject(project_loc);
	ast = createAstsFromEclipseProject(project_loc, true);
	prog = createOFG(ast);
	ofg = buildFlowGraph(prog);
	proOfg = propagateOFG(m3Model, ofg); 

	/*
	get relevant data from modelM3
	*/
	typeDependency = {pair|pair <- m3Model.typeDependency, pair[0].scheme == "java+field"};
	
	typeDependencyInterface = {pair|pair <- typeDependency, pair[1].scheme == "java+interface"}; 
	
	declaration = {pair|pair <- m3Model.declarations, pair[0].scheme == "java+field"};
    //get mapget and removee method
	OFG MapGetRemove =  {pair | pair <- m3Model.methodInvocation, contains(pair[1].path, "Map/get")}
					 +  {pair | pair <- m3Model.methodInvocation, contains(pair[1].path, "Map/remove")};

		// get java/lang method
	OFG methodType = {pair |pair <- m3Model.methodInvocation, method <- MapGetRemove.from,  
						pair[0] == method && contains(pair[1].path, "java/lang")};
	
	 	// get the filed and correspond type
	derivedType = {<field[1], typ[1]> | typ <- methodType, field <- m3Model.fieldAccess, field[0] == typ[0]};
}


private OFG propagateOFG(M3 m, OFG ofg){
		//typeDependency from +variable -> +class
    OFG Variable2Class = {pair | pair <- m3Model.typeDependency, 
    						pair[0].scheme == "java+variable" && 
    						pair[1].scheme == "java+class"};	
    	//rel[loc,&T] propagate(OFG g, rel[loc,&T] gen, rel[loc,&T] kill, bool back) 					
	OFG temOFG = propagate(ofg, Variable2Class, {}, false);
		//text(propogateOFG);
	
	propogateOFG = {pair | pair <- temOFG, 
							!(pair[0].scheme == "java+method" && 
							//pair[0].parent.parent.parent == |java+method:///java/util|)
							contains(pair[0].path, "java/util"))
							};
	return propogateOFG;
}