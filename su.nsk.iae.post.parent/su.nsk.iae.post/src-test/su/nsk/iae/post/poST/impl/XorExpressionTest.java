package su.nsk.iae.post.poST.impl;

import org.junit.Assert;
import org.junit.Test;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;

public class XorExpressionTest {
	@Test
	public void testGenerateExpressionLeftAndRightTotal() {
		String leftName = "a";
		String rightName = "b";
		String variableType = "BOOL";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable leftVar = ExpressionFactory.createSymbolicVariable(leftName);
		SymbolicVariable rightVar = ExpressionFactory.createSymbolicVariable(rightName);
		PrimaryExpression left = ExpressionFactory.createVariableExpression(leftVar);
		PrimaryExpression right = ExpressionFactory.createVariableExpression(rightVar);
		Expression expression = ExpressionFactory.createXorExpression(left, right);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, leftVar, rightVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant leftVarCode = globVars.getVariable(leftName);
		su.nsk.iae.post.vcgenerator.Constant rightVarCode = globVars.getVariable(rightName);
		Term expected = noteq(getVarBool(currentState, leftVarCode), getVarBool(currentState, rightVarCode));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testGenerateExpressionLeftNotTotal() {
		String aName = "a";
		String bName = "b";
		String cName = "c";
		String abType = "INT";
		String cType = "BOOL";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable aVar = ExpressionFactory.createSymbolicVariable(aName);
		SymbolicVariable bVar = ExpressionFactory.createSymbolicVariable(bName);
		SymbolicVariable cVar = ExpressionFactory.createSymbolicVariable(cName);
		PrimaryExpression a = ExpressionFactory.createVariableExpression(aVar);
		PrimaryExpression b = ExpressionFactory.createVariableExpression(bVar);
		PrimaryExpression c = ExpressionFactory.createVariableExpression(cVar);
		MulExpression aDivb = ExpressionFactory.createMulExpression(MulOperator.DIV, a, b);
		su.nsk.iae.post.poST.Constant twoConst = ExpressionFactory.createIntConstant(2);
		PrimaryExpression two = ExpressionFactory.createConstantExpression(twoConst);
		CompExpression aDivbEq2 = ExpressionFactory.createCompExpression(CompOperator.EQUAL, aDivb, two);
		Expression expression = ExpressionFactory.createXorExpression(aDivbEq2, c);
		VarInitDeclaration abDecl = ProgramFactory.createSimpleVarDeclaration(abType, null, aVar, bVar);
		VarInitDeclaration cDecl = ProgramFactory.createSimpleVarDeclaration(cType, null, cVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(abDecl, null, ModificationType.VAR);
		globVars.addVars(cDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant aCode = globVars.getVariable(aName);
		su.nsk.iae.post.vcgenerator.Constant bCode = globVars.getVariable(bName);
		su.nsk.iae.post.vcgenerator.Constant cCode = globVars.getVariable(cName);
		Term expected = noteq(
				eq(div(getVarInt(currentState, aCode), getVarInt(currentState, bCode)), new su.nsk.iae.post.vcgenerator.Constant(2)), 
				getVarBool(currentState, cCode));
		Term expectedPrecondition = noteq(getVarInt(currentState, bCode), new su.nsk.iae.post.vcgenerator.Constant(0));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedPrecondition, result.getPrecondition());
	}
	
	@Test
	public void testGenerateExpressionRightNotTotal() {
		String aName = "a";
		String bName = "b";
		String cName = "c";
		String abType = "INT";
		String cType = "BOOL";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable aVar = ExpressionFactory.createSymbolicVariable(aName);
		SymbolicVariable bVar = ExpressionFactory.createSymbolicVariable(bName);
		SymbolicVariable cVar = ExpressionFactory.createSymbolicVariable(cName);
		PrimaryExpression a = ExpressionFactory.createVariableExpression(aVar);
		PrimaryExpression b = ExpressionFactory.createVariableExpression(bVar);
		PrimaryExpression c = ExpressionFactory.createVariableExpression(cVar);
		MulExpression aDivb = ExpressionFactory.createMulExpression(MulOperator.DIV, a, b);
		su.nsk.iae.post.poST.Constant twoConst = ExpressionFactory.createIntConstant(2);
		PrimaryExpression two = ExpressionFactory.createConstantExpression(twoConst);
		CompExpression aDivbEq2 = ExpressionFactory.createCompExpression(CompOperator.EQUAL, aDivb, two);
		Expression expression = ExpressionFactory.createXorExpression(c, aDivbEq2);
		VarInitDeclaration abDecl = ProgramFactory.createSimpleVarDeclaration(abType, null, aVar, bVar);
		VarInitDeclaration cDecl = ProgramFactory.createSimpleVarDeclaration(cType, null, cVar);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(abDecl, null, ModificationType.VAR);
		globVars.addVars(cDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant aCode = globVars.getVariable(aName);
		su.nsk.iae.post.vcgenerator.Constant bCode = globVars.getVariable(bName);
		su.nsk.iae.post.vcgenerator.Constant cCode = globVars.getVariable(cName);
		Term expected = noteq(
				getVarBool(currentState, cCode),
				eq(div(getVarInt(currentState, aCode), getVarInt(currentState, bCode)), new su.nsk.iae.post.vcgenerator.Constant(2)));
		Term expectedPrecondition =	noteq(getVarInt(currentState, bCode), new su.nsk.iae.post.vcgenerator.Constant(0));
		Term result = expression.generateExpression(currentState, globVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedPrecondition, result.getPrecondition());
	}

}