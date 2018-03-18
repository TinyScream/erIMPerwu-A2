module Suggestion

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
import Main;

public void testing(){
	println("hello");
}

private lrel[loc field, set[loc] classSet, loc interface] SuggestionRelList1 = [];

public lrel[loc field, set[loc] classSet, loc interface] getSuggestionList(OFG typeMissed, OFG typeDependencyInterface){	
	lrel [loc field, loc class, loc interface] suggestionRel1 = [];
    for(n <- toList(typeMissed)){
    	loc field = n[0];
    	loc class = n[1];
    	loc interface;
    	for(tdi <- toList(typeDependencyInterface)){
    		if(n[0] == tdi[0])
    			interface = tdi[1];
    	}
    	suggestionRel1 += <field, class, interface>;
    }
       
    for(sr <- suggestionRel1){
    	set[loc] setCls = {};
    	for(r <- suggestionRel1){
    		if(sr.field == r.field)
    		setCls += r.class;
    	}
    	SuggestionRelList1 += <sr.field, setCls, sr.interface>;
    }
    SuggestionRelList1 = dup (SuggestionRelList1);
    return SuggestionRelList1;
}

public void printSuggestion(OFG declaration, OFG derivedType){
	for(s <- SuggestionRelList1){
		switch (s.interface.file) {
			case"Collection":
				for(d <- toList(declaration)){
					if(s.field == d[0]){
						print("code at");
						print(d[1]);
						print(" ==\> ");
						print(s.interface.file);
						print("\<");
						print(getSuperClass(s.classSet));
						print("\> ");
						print(s.field.file);
						println();
					}
				}
			case"Map":
				for(d <- toList(declaration)){
					for(dt  <- toList(derivedType)){
						if(s.field == d[0] && s.field == dt[0]){
							print("code at");
							print(d[1]);
							print(" ==\> ");
							print(s.interface.file);
							print("\<");
							print(dt[1].parent.file);  //eg: java/lang/Integer/Integer(int)|
							print(", ");
							print(getSuperClass(s.classSet));
							print("\> ");
							print(s.field.file);
							println();
						}
					}
				}
			
		}
	}	
}

private str getSuperClass(set[loc] classSet) {
    if (size(classSet) == 1) {
    	//println(classSet);
        return (toList(classSet)[0].file);
    } else {
    	//TODO
        return "Object";
    }
}