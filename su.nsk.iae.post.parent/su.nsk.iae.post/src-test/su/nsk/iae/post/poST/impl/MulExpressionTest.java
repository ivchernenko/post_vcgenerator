package su.nsk.iae.post.poST.impl;

import org.junit.Assert;
import org.junit.Test;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;

public class MulExpressionTest {
	@Test
	public void testGenerateExpressionIntMul() {
		String leftName = "a";
		String rightName = "b";
		String variableType = "INT";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable leftVar = ExpressionFactory.createSymbolicVariable(leftName);
		SymbolicVariable rightVar = ExpressionFactory.createSymbolicVariable(rightName);
		PrimaryExpression left = ExpressionFactory.createVariableExpression(leftVar);
		PrimaryExpression right = ExpressionFactory.createVariableExpression(rightVar);
		Expression expression = ExpressionFactory.createMulExpression(MulOperator.MUL, left, right);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, leftVar, rightVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant leftVarCode = globVars.getVariable(leftName);
		su.nsk.iae.post.vcgenerator.Constant rightVarCode = globVars.getVariable(rightName);
		Term expected = mul(getVarInt(currentState, leftVarCode), getVarInt(currentState, rightVarCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.INT, result.getType());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testGenerateExpressionIntDiv() {
		String leftName = "a";
		String rightName = "b";
		String variableType = "INT";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable leftVar = ExpressionFactory.createSymbolicVariable(leftName);
		SymbolicVariable rightVar = ExpressionFactory.createSymbolicVariable(rightName);
		PrimaryExpression left = ExpressionFactory.createVariableExpression(leftVar);
		PrimaryExpression right = ExpressionFactory.createVariableExpression(rightVar);
		Expression expression = ExpressionFactory.createMulExpression(MulOperator.DIV, left, right);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, leftVar, rightVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant leftVarCode = globVars.getVariable(leftName);
		su.nsk.iae.post.vcgenerator.Constant rightVarCode = globVars.getVariable(rightName);
		Term expected = div(getVarInt(currentState, leftVarCode), getVarInt(currentState, rightVarCode));
		Term expectedPrecondition = noteq(getVarInt(currentState, rightVarCode), new su.nsk.iae.post.vcgenerator.Constant(0));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.INT, result.getType());
		Assert.assertEquals(expectedPrecondition, result.getPrecondition());
	}
	
	@Test
	public void testGenerateExpressionRealDiv() {
		String leftName = "a";
		String rightName = "b";
		String variableType = "REAL";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable leftVar = ExpressionFactory.createSymbolicVariable(leftName);
		SymbolicVariable rightVar = ExpressionFactory.createSymbolicVariable(rightName);
		PrimaryExpression left = ExpressionFactory.createVariableExpression(leftVar);
		PrimaryExpression right = ExpressionFactory.createVariableExpression(rightVar);
		Expression expression = ExpressionFactory.createMulExpression(MulOperator.DIV, left, right);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, leftVar, rightVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant leftVarCode = globVars.getVariable(leftName);
		su.nsk.iae.post.vcgenerator.Constant rightVarCode = globVars.getVariable(rightName);
		Term expected = rdiv(getVarReal(currentState, leftVarCode), getVarReal(currentState, rightVarCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.REAL, result.getType());
	}
	
	@Test
	public void testGenerateExpressionMod() {
		String leftName = "a";
		String rightName = "b";
		String variableType = "INT";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable leftVar = ExpressionFactory.createSymbolicVariable(leftName);
		SymbolicVariable rightVar = ExpressionFactory.createSymbolicVariable(rightName);
		PrimaryExpression left = ExpressionFactory.createVariableExpression(leftVar);
		PrimaryExpression right = ExpressionFactory.createVariableExpression(rightVar);
		Expression expression = ExpressionFactory.createMulExpression(MulOperator.MOD, left, right);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, leftVar, rightVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant leftVarCode = globVars.getVariable(leftName);
		su.nsk.iae.post.vcgenerator.Constant rightVarCode = globVars.getVariable(rightName);
		Term expected = mod(getVarInt(currentState, leftVarCode), getVarInt(currentState, rightVarCode));
		Term expectedPrecondition = noteq(getVarInt(currentState, rightVarCode), new su.nsk.iae.post.vcgenerator.Constant(0));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.INT, result.getType());
		Assert.assertEquals(expectedPrecondition, result.getPrecondition());
	}
}