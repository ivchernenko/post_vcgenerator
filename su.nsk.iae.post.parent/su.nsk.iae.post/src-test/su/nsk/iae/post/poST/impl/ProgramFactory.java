package su.nsk.iae.post.poST.impl;

import su.nsk.iae.post.poST.*;
import java.util.Arrays;
import java.util.List;

import org.eclipse.emf.common.util.*;

public class ProgramFactory {
	public static VarInitDeclaration createSimpleVarDeclaration(String type, Expression value, SymbolicVariable ... vars ) {
		SimpleSpecificationInit spec = new SimpleSpecificationInitImpl();
		spec.setType(type);
		spec.setValue(value);
		VarInitDeclaration varInitDeclaration = new VarInitDeclarationImpl();
		varInitDeclaration.setSpec(spec);
		VarListImpl varList = new VarListImpl();
		EList<SymbolicVariable> listOfVars = new BasicEList<>(Arrays.asList(vars));
		varList.vars = listOfVars;
		varInitDeclaration.setVarList(varList);
		return varInitDeclaration;
	}

	public static VarInitDeclaration createArrayVarDeclaration(Expression start, Expression end, String type, List<Expression> elements, SymbolicVariable ... vars) {
		ArraySpecification arrSpec = new ArraySpecificationImpl();
		arrSpec.setType(type);
		ArrayInterval interval = new ArrayIntervalImpl();
		interval.setStart(start);
		interval.setEnd(end);
		arrSpec.setInterval(interval);
		ArraySpecificationInit arrSpecInit = new ArraySpecificationInitImpl();
		arrSpecInit.setInit(arrSpec);
		ArrayInitializationImpl initialization = new ArrayInitializationImpl();
		if (elements == null)
			initialization.elements = null;
		else 
			initialization.elements = new BasicEList<>(elements);
		arrSpecInit.setValues(initialization);
		VarInitDeclaration varInitDeclaration = new VarInitDeclarationImpl();
		varInitDeclaration.setArrSpec(arrSpecInit);
		VarListImpl varList = new VarListImpl();
		EList<SymbolicVariable> listOfVars = new BasicEList<>(Arrays.asList(vars));
		varList.vars = listOfVars;
		varInitDeclaration.setVarList(varList);
		return varInitDeclaration;
	}

	public static InputVarDeclaration createInputVarDeclaration(List<VarInitDeclaration> varDecl) {
		InputVarDeclarationImpl inVars = new InputVarDeclarationImpl();
		inVars.vars = new BasicEList<>(varDecl);
		return inVars;
	}

	public static OutputVarDeclaration createOutputVarDeclaration(List<VarInitDeclaration> varDecl) {
		OutputVarDeclarationImpl outVars = new OutputVarDeclarationImpl();
		outVars.vars = new BasicEList<>(varDecl);
		return outVars;
	}

	public static InputOutputVarDeclaration createInOutVarDeclaration(List<VarInitDeclaration> varDecl) {
		InputOutputVarDeclarationImpl inOutVars = new InputOutputVarDeclarationImpl();
		inOutVars.vars = new BasicEList<>(varDecl);
		return inOutVars;
	}

	public static VarDeclaration createVarDeclaration(boolean isConst, List<VarInitDeclaration> varDecl) {
		VarDeclarationImpl vars = new VarDeclarationImpl();
		vars.setConst(isConst);
		vars.vars = new BasicEList<>(varDecl);
		return vars;
	}

	public static State createState(String name, List<Statement> statement, TimeoutStatement timeout) {
		State state = new StateImpl();
		state.setStatement(StatementFactory.createStatementList(statement));
		state.setTimeout(timeout);
		state.setName(name);
		return state;
	}

	public static su.nsk.iae.post.poST.Process createProcess(String name, List<InputVarDeclaration> inVars, 
			List<OutputVarDeclaration> outVars, List<InputOutputVarDeclaration> inOutVars, List<VarDeclaration> vars, 
			List<State> states) {
		ProcessImpl process = new ProcessImpl();
		process.setName(name);
		if (inVars != null)
			process.procInVars = new BasicEList<>(inVars);
		if (outVars != null)
			process.procOutVars = new BasicEList<>(outVars);
		if (inOutVars != null)
			process.procInOutVars = new BasicEList<>(inOutVars);
		if (vars != null)
			process.procVars = new BasicEList<>(vars);
		process.states = new BasicEList<>(states);
		return process;
	}

}
