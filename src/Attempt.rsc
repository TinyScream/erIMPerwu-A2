module Attempt

import IO;
import Set;
import List;
//import lang::ofg::ast::FlowLanguage;
import analysis::flow::ObjectFlow;
import lang::java::m3::TypeSymbol;
import lang::java::jdt::m3::AST;
import lang::java::jdt::m3::Core;
import lang::java::flow::JavaToObjectFlow;
import analysis::flow::ObjectFlow;
//import lang::ofg::ast::Java2OFG;
import lang::java::flow::JavaToObjectFlow;
import Relation;
import vis::Figure;
import String;
import util::ValueUI;

alias OFG = rel[loc from, loc to]; //OFG alias

//Declare variables
private M3 projectM3; //M3 from project
private FlowProgram projectProgram; //Program from project
private OFG ofg; //Project OFG
private OFG propagatedOfg = {}; //Project OFG, propagated using propagation algorithm
private list[Edge] ofgEdges = []; //Stores the edges of original OFG
private list[Edge] propagatedOfgEdges = []; //Stores the edges of propagated OFG
private set[str] ofgNodes = {}; //Stores the nodes of OFG
private set[str] propagatedOfgNodes = {}; //Stores the nodes of propagated OFG
private list[Edge] interfaceEdges = []; //Stores the interfaces edges
private list[Edge] typeDependencies = []; //Stores type dependencies
private list[Edge] edgeToModify = []; //Stores edge to modify, i.e. uses interfaces
private list[Edge] declarations = []; //stores declaration edges
private lrel[str field, set[str] class, str interface, int counter] fieldRelation = []; //stores field relations for changing
private lrel[str superClass, set[str] subClass] extendClasses = []; //stores extend classes

loc loc_eLib = |project://eLib|;

//A main entry to invoke all procedure
//It invokes all other stuffs

public void main(){
	M3 m = createM3FromEclipseProject(loc_eLib);
	ast = createAstsFromEclipseProject(loc_eLib, true);
	FlowProgram p = createOFG(ast);
	ofg = buildFlowGraph(p);
	//ofg = buildFlowGraph0(p);
	
	
}



public void getAdvices(loc projectLocation) {
    createM3AndFlowProgram(projectLocation); //Create OFG
    
    //Get all edges and nodes we need
    getEdgesAndNodes();
    getExtendClasses(projectM3);
    
    //Check which one will be modified
    checkOfgInflow(propagatedOfgEdges); 
    checkEdgeToModify(edgeToModify);
    declarations = makeDeclarations(projectM3);
    buildRelation(edgeToModify, interfaceEdges);

    getSuggestions();
}

//Create M3 and a flow program
//Slides getting facts
private void createM3AndFlowProgram(loc projectLoc) {
    projectM3 = createM3FromEclipseProject(projectLoc);
    ast = createAstsFromEclipseProject(projectLoc, true);
    projectProgram = createOFG(ast);
    ofg = buildGraph(projectProgram); //original OFG
    ofg0 = buildGraph0(projectProgram);
    
    //println(size(ofg-ofg0));
    propagatedOfg = propagate(ofg); //propagatedOFG
}

//Get edges and nodes
//From ofg, propagated ofg and M3
private void getEdgesAndNodes() {
    ofgEdges = makeOfgEdges();
    propagatedOfgEdges = makePropagatedOfgEdges();
    makeOfgNodes();
    makePropagatedOfgNodes();
    typeDependencies = makeTypeDependencyEdges(projectM3);
    interfaceEdges = makeDependencyWithInterface(typeDependencies);
}

//Check ofg edges, such that field flows to Classes
//Indicates that data flows to/from that class
private void checkOfgInflow(list[Edge] edges) {
    for (e <- edges) {
        if (contains(e.from, "class") && contains(e.to, "field")) {
            edgeToModify += e;
        }
    }
}

//We only care about the build-in Java containers
//i.e. uses an interface like Map, Collection, etc. 
private void checkEdgeToModify(list[Edge] edges) {
    list[Edge] temp = [];
    for (e <- edges) {
        for (t <- typeDependencies) {
            if (e.to == t.to && contains(t.from, "interface")) {
                temp += e;
            }
        }
    }
    edgeToModify = temp;
}

//Initial flow graph 
//According to slides "TipsAndTricks"
//Slightly changed from ObjectFlow.rsc
//In Jurgen Vinju's Github repository
//Apply theory of Figure 2.2 in Tonella
private OFG buildGraph(FlowProgram p) {	//new one
    return { <as[i], fps[i]> | newAssign(x, cl, c, as) <- p.statements, constructor(c, fps) <- p.decls, i <- index(as) } 
    + { <cl + "this", x> | newAssign(x, cl, _, _) <- p.statements } 
    + { <cs + "this", x> | newAssign(x, _, cs, _) <- p.statements } //diff
    + { <y, x> | assign(x, _, y) <- p.statements} 
    + { <as[i], fps[i]> | call(x, _, _, m, as) <- p.statements, method(m, fps) <- p.decls, i <- index(as) } 
    + { <y, m + "this"> | call(_, _, y, m, _) <- p.statements } 
    + { <m + "return", x> | call(x, _, _, m, _) <- p.statements, x != emptyId}
    ;
}


private OFG buildGraph0(FlowProgram p) //Standard
  = { <as[i], fps[i]> | newAssign(x, cl, c, as) <- p.statements, constructor(c, fps) <- p.decls, i <- index(as) }
  + { <cl + "this", x> | newAssign(x, cl, _, _) <- p.statements }
  + { <y, x> | assign(x, _, y) <- p.statements}
  + { <as[i], fps[i]> | call(x, _, y, m, as) <- p.statements, method(m, fps) <- p.decls, i <- index(as) }
  + { <y, m + "this"> | call(_, _, y, m, _) <- p.statements }
  + { <m + "return", x> | call(x, _, _, m, _) <- p.statements, x != emptyId}
  ;

//Propagation algorithm
//Both forward and backward
private OFG propagate(OFG ofg) {
    rel[loc, loc] genFor;
    rel[loc, loc] genBack;
    genFor = { <constr + "this", class> | newAssign(_, class, constr, _) <- projectProgram.statements, constructor(constr, _) <- projectProgram.decls };
    genBack = { <x, caller> | assign(y, caller, x) <- projectProgram.statements, caller != emptyId}
            + { <m + "return", caller> | call(caller, _, _, m, _) <- projectProgram.statements, caller != emptyId};
    
    //text(genFor);
    text(genBack);
        
    OFG IN = { };
    OFG OUTFor = genFor;
    OFG OUTBack = genBack;
  
    invertedOfg = { <to,from> | <from, to> <- ofg};
    set[loc] pred(loc n) = invertedOfg[n];
    set[loc] succ(loc n) = ofg[n];
      
    solve (IN, OUTFor) {
        IN = { <n,\o> | n <- carrier(ofg), x <- (pred(n)), \o <- OUTFor[x] };
        OUTFor = genFor + IN;
    }
    solve (IN, OUTBack) {
        IN = { <n,\o> | n <- carrier(ofg), x <- (succ(n)), \o <- OUTBack[x] };
        OUTBack = genBack + IN;
    }
  
    return OUTFor + OUTBack;           
}

//Get all classes from M3
public set[loc] getClasses(M3 m) {
    set[loc] allClasses = classes(m);
    for (cl <- basicClasses) {
        allClasses += cl;
    }
    return allClasses;
}

//Get all edges of OFG
private list[Edge] makeOfgEdges() {
    return [edge("<to>", "<from>") | <from, to> <- ofg ];
}
//Get all edges of propagated OFG
private list[Edge] makePropagatedOfgEdges() {
    return [edge("<to>", "<from>") | <from, to> <- propagatedOfg ];
}
//Store all OFG nodes
private void makeOfgNodes() {
    for (e <- ofgEdges) {
        ofgNodes += e.from;
        ofgNodes += e.to;
    }
}
//Store all propagated OFG nodes
private void makePropagatedOfgNodes() {
    for (e <- propagatedOfgEdges) {
        propagatedOfgNodes += e.from;
        propagatedOfgNodes += e.to;
    }
}
//Store all m3 type dependency edges
private list[Edge] makeTypeDependencyEdges(M3 m) {
    list[Edge] dependency = [edge("<to>", "<from>") | <from, to> <- m.typeDependency ];
    for (e <- dependency) {
        if (! contains(e.to, "field")) {
            dependency -= e;
        }
    }
    return dependency;
}
//Store all m3 type dependency with interfaces
private list[Edge] makeDependencyWithInterface(list[Edge] typeDependency) {
    for (e <- typeDependency) {
        if (! contains(e.from, "interface")) {
            typeDependency -= e;
        }
    }
    return typeDependency;
}
//Store all m3 declarations
//Only with java+field
private list[Edge] makeDeclarations(M3 m) {
    list[Edge] declarations = [edge("<to>", "<from>") | <from, to> <- m.declarations ];
    list[Edge] declarationsOutput = [];
    for (d <- declarations) {
        if (! contains(d.to, "field")) {
            declarations -= d;
        }
    }
    for (d <- declarations) {
        for (e <- edgeToModify) {
            if (e.to == d.to) {
                declarationsOutput += d;
                break;
            }
        }
    }
    return declarationsOutput;
}

//Change the edge string to a e.g. class, interface, field name for correction
private str edgeToString(str edge) {
    int length = size(edge);
    int startIndex;
    int endIndex;
    str newString = "";
    for (int i <- [length - 1..0]) {
        if (! (charAt(edge, i) == 124)) {
            endIndex = i + 1;
            break;
        }
    }
    for (int i <- [length - 1..0]) {
        if (charAt(edge, i) == 47) {
            startIndex = i + 1;
            break;
        }
    }
    for (int j <- [startIndex..endIndex]) {
        newString += stringChar(charAt(edge, j));
    }
    return newString;
}

//Build relation of correction
//The relation includes the field that need to be modified, 
//The related class, i.e. value type
//The used interface and counter
private void buildRelation(list[Edge] edgeToModify, list[Edge] interfaceEdges) {
    lrel[str field, str class, str interface, int counter] tempRel = [];
    for (e <- edgeToModify) {
        str field = e.to;
        str class = edgeToString(e.from);
        int counter = 1;
        str interface = "";
        for (i <- interfaceEdges) {
            if (e.to == i.to) {
                interface = edgeToString(i.from);
            }
        }
        for (r <- tempRel) {
            if (r.field == field) {
                counter = r.counter + 1;
            }
        }
        tempRel += <field, class, interface, counter>;
    }
    for (r <- tempRel) {
        set[str] class = {};
        if (r.counter == 1) {
            int counter = 0;
            for (t <- tempRel) {
                if (r.field == t.field) {
                    class += t.class;
                    counter += 1;
                }
            }
            fieldRelation += <r.field, class, r.interface, counter>;
        }
    }
}

//Generate suggestions
private void getSuggestions() {
    for (f <- fieldRelation) {
        switch(f.interface) {
            case "Map": 
                for (d <- declarations) {
                    if (f.field == d.to) {
                        print("Code at" + d.from + " should be changed to: ");
                        print(f.interface);
                        print("\<");
                        print("Integer, ");
                        print(getSuperClass(f.class));
                        print("\> ");
                        println(edgeToString(f.field));                
                    }
                }
            case "Collection":
                for (d <- declarations) {
                    if (f.field == d.to) {
                        print("Code at" + d.from + " should be changed to: ");
                        print(f.interface);
                        print("\<");
                        print(getSuperClass(f.class));
                        print("\> ");
                        println(edgeToString(f.field));                
                    }
                }
        }
    }
}

//Constraint solver
private void getExtendClasses(M3 m) {
    list[Edge] extends = [edge("<to>", "<from>") | <from, to> <- m.extends ];
    for (e <- extends) {
        if (! containsClass(e.from)) {
            extendClasses += <e.from, {e.to}>;
        } else {
            for (ec <- extendClasses) {
                if (e.from == ec.superClass) {
                    set[str] tmp = ec.subClass;
                    extendClasses -= <e.from, tmp>;
                    tmp += e.to;
                    extendClasses += <e.from, tmp>;
                }
            }
        }        
    }        
}

//Get super class
//Now only support that there are inheritance between two classes
private str getSuperClass(set[str] classSet) {
    if (size(classSet) == 1) {
        return oneElementSetToString(classSet);
    } else {
        for (c <- classSet) {
            for (e <- extendClasses) {
                if (c == edgeToString(e.superClass)) {
                    return edgeToString(e.superClass);
                } else {
                    for (s <- e.subClass) {
                        if (c == edgeToString(s)) {
                            return edgeToString(e.superClass);
                        }
                    }
                }
            }
        }
        return "Object";
    }
}

private bool containsClass(str class) {
    for (e <- extendClasses) {
        if (e.superClass == class) {
            return true;
        }
    }
    return false;
}
private str oneElementSetToString(set[str] input) {
    int startIndex = 0;
    int endIndex = 0;
    str newString = "";
    str tmp = toString(input);
    for (i <- [0..size(tmp)]) {
        if ((charAt(tmp, i) == 123) && (charAt(tmp, i + 1) == 34)) {
            startIndex = i + 2;
        }
        if ((charAt(tmp, i) == 34) && (charAt(tmp, i + 1) == 125)) {
            endIndex = i;
        }
    }
    for (int j <- [startIndex..endIndex]) {
        newString += stringChar(charAt(tmp, j));
    }
    return newString;
}