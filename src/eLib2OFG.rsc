module eLib2OFG

import IO;
import List;
import Relation;


import lang::java::flow::JavaToObjectFlow;
import analysis::flow::ObjectFlow;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;

//import module analysis::flow::ObjectFlow;




//import FlowGraphsAndClassDiagrams;

loc loc_eLib = |project://eLib|;

alias OFG = rel[loc from, loc to];


void main(){
	m = createM3FromEclipseProject(loc_eLib);
	ast = createAstsFromEclipseProject(loc_eLib, true);
	p = createOFG(ast);
	//println(method(m));
	ofg = buildFlowGraph(p);
	
	
	
}