package su.nsk.iae.post.poST.impl;

import org.junit.Assert;
import org.junit.Test;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;


public class IfStatementTest {
	@Test
	public void testApplyToWithoutElseIfAndElse() {
		/*a, b: BOOL;
		 * statement: IF a THEN b:= TRUE; END_IF
		 * result: [{getVarBool(s0, a), setVarBool(s0, b, True)}, {not(getVarBool(s0, a)), s0}]
		 */
		String aName = "a";
		String bName = "b";
		String type = "BOOL";
		boolean value = true;
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable aVar = ExpressionFactory.createSymbolicVariable(aName);
		Expression a = ExpressionFactory.createVariableExpression(aVar);
		SymbolicVariable b = ExpressionFactory.createSymbolicVariable(bName);
		su.nsk.iae.post.poST.Constant valueConst = ExpressionFactory.createBooleanConstant(value);
		Expression valueExpr = ExpressionFactory.createConstantExpression(valueConst);
		Statement mainStatement = StatementFactory.createVariableAssignmentStatement(b, valueExpr);
		List<Statement> mainStatements = new ArrayList<>();
		mainStatements.add(mainStatement);
		Statement ifStatement = StatementFactory.createIfStatement(a, mainStatements, null, null, null);
		Path path = new Path(null, currentState);
		List<Path> paths = new ArrayList<>();
		paths.add(path);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(type, null, aVar, b);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant aCode = vcGenVars.getVariable(aName);
		su.nsk.iae.post.vcgenerator.Constant bCode = vcGenVars.getVariable(bName);
		List<Path> expected = new ArrayList<>();
		expected.add(new Path(getVarBool(currentState, aCode), setVarBool(currentState, bCode, su.nsk.iae.post.vcgenerator.Constant.True)));
		expected.add(new Path(not(getVarBool(currentState, aCode)), currentState));
		List<Path> result = ifStatement.applyTo(paths, vcGenVars);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testApplyTo1ElseIfAndElse() {
		/*a, b: BOOL;
		 * x: INT;
		 * statement: IF a THEN x:=1; ELSIF b THEN x:=2; ELSE x:=3; END_IF
		 * result: 
		 * [{getVarBool(s0, a), setVarInt(s0, x, 1)},
		 *  {not(getVarBool(s0, a)) /\ getVarBool(s0, b), setVarInt(s0, x, 2)}
		 *  {not(getVarBool(s0, a)) /\ not(getVarBool(s0, b)), setVarInt(s0, x, 3)}]
		 */
		String aName = "a";
		String bName = "b";
		String xName = "x";
		String abType = "BOOL";
		String xType = "INT";
		int x1 = 1, x2 = 2, x3 = 3;
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable aVar = ExpressionFactory.createSymbolicVariable(aName);
		Expression a = ExpressionFactory.createVariableExpression(aVar);
		SymbolicVariable bVar = ExpressionFactory.createSymbolicVariable(bName);
		Expression b = ExpressionFactory.createVariableExpression(bVar);
		SymbolicVariable x = ExpressionFactory.createSymbolicVariable(xName);
		su.nsk.iae.post.poST.Constant x1Const = ExpressionFactory.createIntConstant(x1);
		su.nsk.iae.post.poST.Constant x2Const = ExpressionFactory.createIntConstant(x2);
		su.nsk.iae.post.poST.Constant x3Const = ExpressionFactory.createIntConstant(x3);
		Expression x1Expr = ExpressionFactory.createConstantExpression(x1Const);
		Expression x2Expr = ExpressionFactory.createConstantExpression(x2Const);
		Expression x3Expr = ExpressionFactory.createConstantExpression(x3Const);
		Statement assignX1 = StatementFactory.createVariableAssignmentStatement(x, x1Expr);
		Statement assignX2 = StatementFactory.createVariableAssignmentStatement(x, x2Expr);
		Statement assignX3 = StatementFactory.createVariableAssignmentStatement(x, x3Expr);
		List<Statement> mainStatements = new ArrayList<>();
		mainStatements.add(assignX1);
		List<Statement> elseIf1 = new ArrayList<>();
		elseIf1.add(assignX2);
		List<Statement> elseStatement = new ArrayList<>();
		elseStatement.add(assignX3);
		List<List<Statement>> elseIfStatements = new ArrayList<>();
		elseIfStatements.add(elseIf1);
		List<Expression> elseIfCond = new ArrayList<>();
		elseIfCond.add(b);
		Statement ifStatement = StatementFactory.createIfStatement(a, mainStatements, elseIfCond, elseIfStatements, elseStatement);
		Path path = new Path(null, currentState);
		List<Path> paths = new ArrayList<>();
		paths.add(path);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration abDecl = ProgramFactory.createSimpleVarDeclaration(abType, null, aVar, bVar);
		VarInitDeclaration xDecl = ProgramFactory.createSimpleVarDeclaration(xType, null, x);
		vcGenVars.addVars(abDecl, null, ModificationType.VAR);
		vcGenVars.addVars(xDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant aCode = vcGenVars.getVariable(aName);
		su.nsk.iae.post.vcgenerator.Constant bCode = vcGenVars.getVariable(bName);
		su.nsk.iae.post.vcgenerator.Constant xCode = vcGenVars.getVariable(xName);
		List<Path> expected = new ArrayList<>();
		expected.add(new Path(
				getVarBool(currentState, aCode), 
				setVarInt(currentState, xCode, new su.nsk.iae.post.vcgenerator.Constant(x1))));
		expected.add(new Path(
				and(not(getVarBool(currentState, aCode)), getVarBool(currentState, bCode)),
				setVarInt(currentState, xCode, new su.nsk.iae.post.vcgenerator.Constant(x2))));
		expected.add(new Path(
				and(not(getVarBool(currentState, aCode)), not(getVarBool(currentState, bCode))),
				setVarInt(currentState, xCode, new su.nsk.iae.post.vcgenerator.Constant(x3))));
		List<Path> result = ifStatement.applyTo(paths, vcGenVars);
		Assert.assertEquals(expected, result);
	}

}
