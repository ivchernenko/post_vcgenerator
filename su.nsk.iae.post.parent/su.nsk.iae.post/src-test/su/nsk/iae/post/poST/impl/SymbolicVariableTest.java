package su.nsk.iae.post.poST.impl;

import org.eclipse.emf.common.util.*;

import org.junit.Assert;
import org.junit.Test;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;

; public class SymbolicVariableTest {

	@Test
	public void testGenerateVariableBool() {
		String variableName = "a";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable variable = new SymbolicVariableImpl();
		variable.setName(variableName);
		VarListImpl varList = new VarListImpl();
		EList<SymbolicVariable> vars = new BasicEList<>();
		vars.add(variable);
		varList.vars = vars;
		SimpleSpecificationInit spec = new SimpleSpecificationInitImpl();
		spec.setType("BOOL");
		VarInitDeclaration varDecl = new VarInitDeclarationImpl();
		varDecl.setVarList(varList);
		varDecl.setSpec(spec);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant varCode = globVars.getVariable(variableName);
		Term expected = getVarBool(currentState, varCode);
		Term result = variable.generateVariable(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
		Assert.assertEquals(DataType.BOOL, result.getType());	
	}
	
	@Test
	public void testGenerateVariableInt() {
		String variableName = "a";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable variable = new SymbolicVariableImpl();
		variable.setName(variableName);
		VarListImpl varList = new VarListImpl();
		EList<SymbolicVariable> vars = new BasicEList<>();
		vars.add(variable);
		varList.vars = vars;
		SimpleSpecificationInit spec = new SimpleSpecificationInitImpl();
		spec.setType("INT");
		VarInitDeclaration varDecl = new VarInitDeclarationImpl();
		varDecl.setVarList(varList);
		varDecl.setSpec(spec);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant varCode = globVars.getVariable(variableName);
		Term expected = getVarInt(currentState, varCode);
		Term result = variable.generateVariable(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
		Assert.assertEquals(DataType.INT, result.getType());	
	}
	
	@Test
	public void testGenerateVariableReal() {
		String variableName = "a";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable variable = new SymbolicVariableImpl();
		variable.setName(variableName);
		VarListImpl varList = new VarListImpl();
		EList<SymbolicVariable> vars = new BasicEList<>();
		vars.add(variable);
		varList.vars = vars;
		SimpleSpecificationInit spec = new SimpleSpecificationInitImpl();
		spec.setType("REAL");
		VarInitDeclaration varDecl = new VarInitDeclarationImpl();
		varDecl.setVarList(varList);
		varDecl.setSpec(spec);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant varCode = globVars.getVariable(variableName);
		Term expected = getVarReal(currentState, varCode);
		Term result = variable.generateVariable(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
		Assert.assertEquals(DataType.REAL, result.getType());	
	}
	
	@Test
	public void testGenerateVariableTime() {
		String variableName = "a";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable variable = new SymbolicVariableImpl();
		variable.setName(variableName);
		VarListImpl varList = new VarListImpl();
		EList<SymbolicVariable> vars = new BasicEList<>();
		vars.add(variable);
		varList.vars = vars;
		SimpleSpecificationInit spec = new SimpleSpecificationInitImpl();
		spec.setType("TIME");
		VarInitDeclaration varDecl = new VarInitDeclarationImpl();
		varDecl.setVarList(varList);
		varDecl.setSpec(spec);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant varCode = globVars.getVariable(variableName);
		Term expected = getVarInt(currentState, varCode);
		Term result = variable.generateVariable(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
		Assert.assertEquals(DataType.INT, result.getType());	
	}
	
	@Test
	public void testGenerateVariableConstant() {
		String variableName = "a";
		boolean value = true;
		DataType expectedType = DataType.BOOL;
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable variable = new SymbolicVariableImpl();
		variable.setName(variableName);
		VarListImpl varList = new VarListImpl();
		EList<SymbolicVariable> vars = new BasicEList<>();
		vars.add(variable);
		varList.vars = vars;
		SimpleSpecificationInit spec = new SimpleSpecificationInitImpl();
		spec.setType("BOOL");
		su.nsk.iae.post.poST.Constant constantValue = new ConstantImpl();
		constantValue.setOth(Boolean.toString(value).toUpperCase());
		PrimaryExpression expr = new PrimaryExpressionImpl();
		expr.setConst(constantValue);
		spec.setValue(expr);
		VarInitDeclaration varDecl = new VarInitDeclarationImpl();
		varDecl.setVarList(varList);
		varDecl.setSpec(spec);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.CONSTANT);
		su.nsk.iae.post.vcgenerator.Constant varCode = globVars.getVariable(variableName);
		Term expected = globVars.getConstantValue(varCode);
		Term result = variable.generateVariable(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
		Assert.assertEquals(expectedType, result.getType());
	}
}
