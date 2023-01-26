package su.nsk.iae.post.poST.impl;

import org.junit.Assert;
import org.junit.Test;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;

public class EquExpressionTest {
	@Test
	public void testGenerateExpressionLess() {
		String leftName = "a";
		String rightName = "b";
		String variableType = "INT";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable leftVar = ExpressionFactory.createSymbolicVariable(leftName);
		SymbolicVariable rightVar = ExpressionFactory.createSymbolicVariable(rightName);
		PrimaryExpression left = ExpressionFactory.createVariableExpression(leftVar);
		PrimaryExpression right = ExpressionFactory.createVariableExpression(rightVar);
		Expression expression = ExpressionFactory.createEquExpression(EquOperator.LESS, left, right);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, leftVar, rightVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant leftVarCode = globVars.getVariable(leftName);
		su.nsk.iae.post.vcgenerator.Constant rightVarCode = globVars.getVariable(rightName);
		Term expected = less(getVarInt(currentState, leftVarCode), getVarInt(currentState, rightVarCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testGenerateExpressionGreater() {
		String leftName = "a";
		String rightName = "b";
		String variableType = "INT";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable leftVar = ExpressionFactory.createSymbolicVariable(leftName);
		SymbolicVariable rightVar = ExpressionFactory.createSymbolicVariable(rightName);
		PrimaryExpression left = ExpressionFactory.createVariableExpression(leftVar);
		PrimaryExpression right = ExpressionFactory.createVariableExpression(rightVar);
		Expression expression = ExpressionFactory.createEquExpression(EquOperator.GREATER, left, right);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, leftVar, rightVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant leftVarCode = globVars.getVariable(leftName);
		su.nsk.iae.post.vcgenerator.Constant rightVarCode = globVars.getVariable(rightName);
		Term expected = greater(getVarInt(currentState, leftVarCode), getVarInt(currentState, rightVarCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testGenerateExpressionLessEqu() {
		String leftName = "a";
		String rightName = "b";
		String variableType = "INT";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable leftVar = ExpressionFactory.createSymbolicVariable(leftName);
		SymbolicVariable rightVar = ExpressionFactory.createSymbolicVariable(rightName);
		PrimaryExpression left = ExpressionFactory.createVariableExpression(leftVar);
		PrimaryExpression right = ExpressionFactory.createVariableExpression(rightVar);
		Expression expression = ExpressionFactory.createEquExpression(EquOperator.LESS_EQU, left, right);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, leftVar, rightVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant leftVarCode = globVars.getVariable(leftName);
		su.nsk.iae.post.vcgenerator.Constant rightVarCode = globVars.getVariable(rightName);
		Term expected = leq(getVarInt(currentState, leftVarCode), getVarInt(currentState, rightVarCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testGenerateExpressionGreaterEqu() {
		String leftName = "a";
		String rightName = "b";
		String variableType = "INT";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable leftVar = ExpressionFactory.createSymbolicVariable(leftName);
		SymbolicVariable rightVar = ExpressionFactory.createSymbolicVariable(rightName);
		PrimaryExpression left = ExpressionFactory.createVariableExpression(leftVar);
		PrimaryExpression right = ExpressionFactory.createVariableExpression(rightVar);
		Expression expression = ExpressionFactory.createEquExpression(EquOperator.GREATER_EQU, left, right);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, leftVar, rightVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant leftVarCode = globVars.getVariable(leftName);
		su.nsk.iae.post.vcgenerator.Constant rightVarCode = globVars.getVariable(rightName);
		Term expected = geq(getVarInt(currentState, leftVarCode), getVarInt(currentState, rightVarCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
	}

}
