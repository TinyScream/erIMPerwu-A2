module ClassDiagram

import lang::ofg::ast::FlowLanguage;
import lang::ofg::ast::Java2OFG;
import lang::java::jdt::m3::Core;
import lang::java::jdt::m3::AST;
import lang::java::m3::TypeSymbol;

import Program2OFG;
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

data Project = project(set[Class] classes, set[ClassRelation] relations);
alias OFG = rel[loc from, loc to];
set[str] containerClasses =  {
	 "/java/util/Map"
	,"/java/util/HashMap"
	,"/java/util/Collection"
	,"/java/util/Set"
	,"/java/util/HashSet"
	,"/java/util/LinkedHashSet"
	,"/java/util/List"
	,"/java/util/ArrayList"
	,"/java/util/LinkedList"
};

set[str] hiddenTypes = {
	"Byte" ,"/java/lang/Byte"
	,"Character" ,"/java/lang/Character"
	,"Short" ,"/java/lang/Short"
	,"Integer" ,"/java/lang/Integer"
	,"Long" ,"/java/lang/Long"
	,"Float" ,"/java/lang/Float"
	,"Double" ,"/java/lang/Double"
	,"String","/java/lang/String", *containerClasses
};


public Project makeProject(loc projectLocation){
	
	println("Creating project");
	// Obtain M3 and OFG
	println("Creating project :: creating m3 model");
	m = createM3FromEclipseProject(projectLocation);
	println("Creating project :: creating OFG");
	ofg = createOFGFromProgram(createOFG(projectLocation));
	
	println("Creating project :: creating all classes");
	allClasses = makeClasses(m);
	
	println("Creating project :: creating all relations between classes");
	allRelations = makeClassRelations(allClasses, m, ofg);
	println("Creating project :: done");
	return project(allClasses, allRelations);
	
}

// Creates a set of all classes from the given M3. 
private set[Class] makeClasses(M3 m){
	set[Class] allClasses = {};
	
	// Create a set of all interfaces
	for(cl <- interfaces(m)){
		allClasses += getClasses(m,cl, "Interface");
	}
	
	// Create a set of all enumerations
	for(cl <- m@declarations<name>, cl.scheme == "java+enum"){
		allClasses += getClasses(m,cl, "Enumeration");	
	}
	
	// Create a set of all anonymous classes
	for(cl <- anonymousClasses(m)){
		allClasses += getClasses(m,cl, "Anonymous class");
	}
	
	// Create a set of all normal classes
	for(cl <- classes(m)){
		allClasses += getClasses(m,cl, "Class");
	}
	return allClasses;
}
private Class getClasses(M3 m, loc cl, str cType){
	// get all methods 
	set[Method] allMethods = getMethods(m,cl);
	// get all attributes
	set[Attribute ] allAttributes = getAttributes(m,cl);
	// get all inner classes
	set[loc] innerClassSet = { e | e <- m@containment[cl], isClass(e)};
	for(l<- innerClassSet){
		getClasses(m,l,cType);
	}
	return class(cl,cl.path[1..], cType, getIM(m,cl), getAM(m,cl),allAttributes, allMethods);
}


private set[Attribute] getAttributes(M3 m, loc l){
	set[Attribute] allAttributes = {};
	// get all attributes
	set[loc] attributeSet = {e | e<- m@containment[l], isField(e)}; 
	
	// get the types that mather
	typeAttribute = domainR(m@types, attributeSet);
	modifierAttribute = domainR(m@modifiers, attributeSet);
	iNames = invert(m@names);
	
	// get the name, return type and modifiers that define an attribute
	for( att <- attributeSet){
		allAttributes += 
		attribute(
			getOneFrom(iNames[att]),
			getReturnType(getOneFrom(typeAttribute[att]), iNames),
			getModiMeth(modifierAttribute[att])
		) ;
	}
	return allAttributes;
}

private set[Method] getMethods(M3 m, loc l){
	set[Method] allMethods = {};
	// get all methods
	set[loc] methodSet = { e | e <- m@containment[l], isMethod(e)};
	
	// get all the types that mather
	typeMethod = domainR(m@types, methodSet);
	modifierMethod = domainR(m@modifiers, methodSet);
	iNames= invert(m@names);
	
	// get the name, return type and modifiers that define a method
	for(met <- methodSet){
		allMethods += 
			method(
				getOneFrom(iNames[met]),
				getReturnType(getOneFrom(typeMethod[met]), iNames),
				getModiMeth(modifierMethod[met])
			); 
	}
	return allMethods;
}

// translate modifiers to readable format
private str getModiMeth(set[Modifier] modi){
	str result = "";
	for(m<- modi){
		if(m == \static()){
			result += "s";
		}
	}
	for(m<- modi){
		switch(m){
			case \public(): result += "+";
			case \private(): result += "-"; 
			case \protected(): result += "#"; 
			case \package(): result += "~";
			case \derived(): result += "/";  
		}
	}
	return result;
}

// translate access modifiers to readable format
private str getAM(M3 m, loc l ){
  	for(modi <- m@modifiers[l] ){
		switch(modi){
			case \final(): ;
			case \abstract(): ;
			case \public(): return "public";
			case \protected(): return "protected";
			case \private(): return "private";
		}
	}
	return "";
}
 
// translate inheretance modifiers to readable format
private str getIM(M3 m, loc l ){
	for(modi <- m@modifiers[l] ){
		switch(modi){
			case \final(): return "final";
			case \abstract(): return "abstract";
			case \public(): ;
			case \protected(): ;
			case \private(): ;
		}
	}
	return "";
}

// translate return types to readable format
private str getReturnType(TypeSymbol t, rel[loc,str] iNames){
	switch(t){
		case \int(): return "int";
		case \short(): return "short";
		case \boolean(): return "boolean";
		case \long(): return "long";
		case \char(): return "char";
		case \byte(): return "byte";
		case \object(): return "object";
		case \void(): return "void";
		case \class(clName, clList) : 
			return getOneFrom(iNames[clName]);
		case \interface(clName, clList) : 
			return getOneFrom(iNames[clName]);
		case \method(ml, fp, returnType, x) :
			return getReturnType(returnType, iNames);
		case \array(oName, dim) : 
			return getReturnType(oName, iNames) + "[<dim>]";
		case \constructor(loc clName, cType) : 
			return getOneFrom(iNames[clName]); 
	}
	
	return "Return type not readable <t>";
}

private set[ClassRelation] makeClassRelations(set[Class] allClasses, M3 m, OFG ofg){

	set[ClassRelation] relations = {};

	// Determine all generalization relations
	for(<child, parent> <- m@extends){
		relations += generalization(parent, child);
	}
	
	// Determine all realization relations
	for(<interface, implementation> <- m@implements){
		relations += realization(implementation, interface);
	}
	
	// Determine all inner class type relations
	for(<innerClass, containingClass>  <- { <innerClass, containingClass> | containingClass <- classes(m), innerClass <- nestedClasses(m, containingClass) }){
		relations += inner(innerClass, containingClass); 
	}
	
	/* 	Mapping containing dependencies and a count of those dependencies.
		A relation between two classes is mapped to two integers. The two integers 
		indicate a high and low multiplicity count. The count can indicate multiple things:
			<0,false> = A dependency exist. The a class does not have an attribute of the b type. 
			<x,false> = A dependency exists as a form of association. The a class has exactly x instances of an attribute with type b. 
			<x,true> = A dependency exists as a form of association. The a class has at least x instances of an attribute with type b.
	*/	
	map[tuple[loc a, loc b], tuple[int multiplicity, bool hasUpperLimit]] associations = ();
  	
	// find all classes that have a relation through a variable/parameter, but skip any primitives
	for(<source, target> <- m@typeDependency, source.scheme == "java+field", sourceClass <- getClass(source, m), sourceClass != target) {	

		set[loc] targetClasses;
		bool wasContainer = false;
		if(target.path in containerClasses){
			wasContainer = true;
			targetClasses = ofg[source];
			//println("Found containerClass <target>. Linked to: <for(cl <- targetClasses){> <cl> <}>");
		} else {
			targetClasses = [target];
		}
		
		// Link the target with the sourcce. 
		for(targetClass <- targetClasses, targetClass.scheme == "java+class", targetClass.path notin hiddenTypes){
		
			if(<sourceClass, targetClass> notin associations){
		    	associations[<sourceClass, targetClass>] = <0, true>;
		    	//println("Added new association for <sourceClass> <targetClass>");
			}
			
			counter = associations[<sourceClass, targetClass>];
			
			if(wasContainer){
				// In case of a container the upper limit is removed, the lower limit remains
		    	associations[<sourceClass, targetClass>] = <counter.multiplicity, false>;
		    	//println("Added association <sourceClass> <targetClass> <counter.multiplicity> false");
		  	} else {
		    	// In case of a regular field the upper limit remains, and the lower limit is increased
		    	associations[<sourceClass, targetClass>] = <counter.multiplicity + 1, counter.hasUpperLimit>;
		    	//println("Added association <sourceClass> <targetClass> <counter.multiplicity + 1> <counter.hasUpperLimit>");
		  	}
	  	}
			
	}
	
	// Determine multiplicity for fields and the like
	
	/*
	for ( ... )
	{
		dependencies += (x:y);
	}
	*/
	
	// Turn the aggregrations into the relations
	for(<<a,b>,<c,d>> <- toRel(associations)){
		// The relationship comes from attributes.
		if(c == 0 && !d || c == 1 && d)
			// The attribute is a single attribute, that may be a container. 
			// Use the name of the attribute for the association
			relations += association(a,b,"",c,d);
		else if(c > 0)
			// If there are multiple attributes, don't use a name at all. 
			// (Possible expansion: add a relation for every attribute)
			relations += association(a,b,"",c,d);		
	}
	
	
	// Add dependencies
	for(<source, targetClass> <- ofg, source != targetClass, targetClass in classes(m), source.scheme == "java+parameter" || source.scheme == "java+variable"){
		for(sourceClass <- getClass(source, m), sourceClass != targetClass, dependency(sourceClass,targetClass) notin relations,
		// Prevent dependencies that are already covered through other means 
		<sourceClass, targetClass> notin associations, generalization(targetClass, sourceClass) notin relations, realization(sourceClass, targetClass) notin relations)
			relations += dependency(sourceClass, targetClass);
	}
	
	
	return relations;
}

set[loc] anonymousClasses(M3 m) = { e | e <- m@declarations<name>, e.scheme == "java+anonymousClass" };

//finds class of given location
set[loc] getClass(loc location, M3 m) {	 
  if (isClass(location))
    return {location}; 
  if (isField(location))
    return {cl | cl <- classes(m), location in fields(m, cl)};
  if (isMethod(location))
    return {cl | cl <- classes(m), location in methods(m, cl)};

  //either parameter or local variable
  return {cl | cl <- classes(m), method <- elements(m, cl), isMethod(method), paramOrVar <- elements(m, method), location == paramOrVar};
}

data Class = class(loc id, str name, str cType, str cIModifier, str cAModifier,set[Attribute] attributeSet, set[Method] methodset);


// Each class has a type, a modifier for that type and a set of declarations
data Method = method(str name, str returntype, str mModifier);
data Attribute = attribute(str name, str aType, str aModififier);
data ClassType 
 	= enum()
 	| interface()
 	| class()
 	;
 	
data AccessModifier 
	= pub()
	| pro()
	| pri()
	| def()
	;

data InheritanceModifier
	= final()
	| abstract()
	| none();
	
data ClassRelation
	= association(loc a, loc b, str name, int multiplicity, bool hasUpperBound)
	| dependency(loc a, loc b)
	| generalization(loc a, loc b)
	| realization(loc a, loc b)
	| inner(loc a, loc b);