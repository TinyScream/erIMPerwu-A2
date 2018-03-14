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
//import Visualisation;

import lang::java::flow::JavaToObjectFlow;
import analysis::flow::ObjectFlow;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;

//import ClassDiagram;
import FlowGraphsAndClassDiagrams;


alias OFG = rel[loc from, loc to];

void main(){
	loc loc_eLib = |project://eLib|;
	M3 m = createM3FromEclipseProject(loc_eLib);
	ast = createAstsFromEclipseProject(loc_eLib, true);
	FlowProgram p = createOFG(ast);
	ofg = buildFlowGraph(p);
	//ofg = buildGraph(p);
	
	proOfg = propagateOFG(p, ofg);
	text(proOfg);
	
	
	//text(proOfg);
	//graph(ofg);
	
	//writeFile(|project://data/proOFG.txt|, proOfg);
	
	//edges = getEdges(ofg);
	//proEdges = getEdges(proOfg);
	//
	//nodes = getNodes(ofg);
	//proNodes = getNodes(proOfg);
	
	
	
	
	//nodes=[ box("<e>", box(fig=text("<e>"))) | e <- (proOfg<from> + proOfg<to>)];
	//
	//edges=[edge("<f>","<t>") | <f,t> <- proOfg];
	//text(nodes);
	//text(edges);
	
	//println(proNodes);
	//rendNE(proNodes, proEdges);
	//graph(proOfg);
}

//private void rendNE(list[Edge] E){
//	
//	
//	render(graph(nodes, [ ], hint("layered"), gap(100)));
//}

private list[Edge] getEdges (OFG ofg){
	return [edge("<from>", "<to>") | <from, to> <- ofg];
}

private list[str] getNodes (OFG ofg){
	return dup(["<from>"|<from, to> <- ofg]+["<to>"|<from, to> <- ofg]);
}


private OFG propagateOFG(FlowProgram p, OFG ofg){
	genFor = { <c + "this", cl> | newAssign(_, cl, c, _) <- p.statements,  constructor(constr, _) <- p.decls}; 
	//genFor = {<cl  , x>|newAssign(x, cl, c, as)  <- p.statements};
	//genBac = { <s, ca> | assign(t, ca, s) <- p.statements, ca != emptyId }
 //          + { <m + "return", ca> | call(t, ca, _, m, _) <- p.statements, ca != emptyId };
	
	genBac = { <x, caller> | assign(y, caller, x) <- p.statements, caller != emptyId}
            + { <m + "return", caller> | call(caller, _, _, m, _) <- p.statements, caller != emptyId};
    
    text(genFor);
        
	OFG IN = { };
	OFG OUTFor = genFor;
	OFG OUTBac = genBac;
	
	iOfg = {<to, from> | <from, to> <- ofg};
	
	set[loc] pred(loc n) = iOfg[n];
	set[loc] succ(loc n) = ofg[n];
	
	solve (IN, OUTFor) {
        IN = { <n,\o> | n <- carrier(ofg), x <- (pred(n)), \o <- OUTFor[x] };
        OUTFor = genFor + IN;
    }
    solve (IN, OUTBac) {
        IN = { <n,\o> | n <- carrier(ofg), x <- (succ(n)), \o <- OUTBac[x] };
        OUTBac = genBac + IN;
    }
	
	return genFor + genBac;
}

	// as an example
private OFG buildGraph(FlowProgram p) {
    return { <as[i], fps[i]> | newAssign(x, cl, c, as) <- p.statements, constructor(c, fps) <- p.decls, i <- index(as) } 
    + { <cl + "this", x> | newAssign(x, cl, _, _) <- p.statements } 
    + { <cs + "this", x> | newAssign(x, _, cs, _) <- p.statements }
    + { <y, x> | assign(x, _, y) <- p.statements} 
    + { <as[i], fps[i]> | call(_, _, _, m, as) <- p.statements, method(m, fps) <- p.decls, i <- index(as) } 
    + { <y, m + "this"> | call(_, _, y, m, _) <- p.statements } 
    + { <m + "return", x> | call(x, _, _, m, _) <- p.statements, x != emptyId}
    ;
}




