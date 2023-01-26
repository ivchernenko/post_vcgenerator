package su.nsk.iae.post.poST.impl;

import org.junit.Assert;
import org.junit.Test;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;

public class UnaryExpressionTest {
	@Test
	public void testGenerateExpressionNot() {
		String variableName = "a";
		String variableType = "BOOL";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable variable = ExpressionFactory.createSymbolicVariable(variableName);
		PrimaryExpression varExpr = ExpressionFactory.createVariableExpression(variable);
		Expression expression = ExpressionFactory.createUnaryExpression(UnaryOperator.NOT, varExpr);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, variable);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant varCode = globVars.getVariable(variableName);
		Term expected = not(getVarBool(currentState, varCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.BOOL, result.getType());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testGenerateExpressionUnMinusInt() {
		String variableName = "a";
		String variableType = "INT";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable variable = ExpressionFactory.createSymbolicVariable(variableName);
		PrimaryExpression varExpr = ExpressionFactory.createVariableExpression(variable);
		Expression expression = ExpressionFactory.createUnaryExpression(UnaryOperator.UNMINUS, varExpr);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, variable);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant varCode = globVars.getVariable(variableName);
		Term expected = unminus(getVarInt(currentState, varCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.INT, result.getType());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testGenerateExpressionUnMinusReal() {
		String variableName = "a";
		String variableType = "REAL";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable variable = ExpressionFactory.createSymbolicVariable(variableName);
		PrimaryExpression varExpr = ExpressionFactory.createVariableExpression(variable);
		Expression expression = ExpressionFactory.createUnaryExpression(UnaryOperator.UNMINUS, varExpr);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, variable);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant varCode = globVars.getVariable(variableName);
		Term expected = unminus(getVarReal(currentState, varCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.REAL, result.getType());
		Assert.assertNull(result.getPrecondition());
	}
}
