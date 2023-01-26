package su.nsk.iae.post.poST.impl;

import org.junit.Assert;
import org.junit.Test;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;
import su.nsk.iae.post.vcgenerator.Variable;

import static su.nsk.iae.post.vcgenerator.TermFactory.*;

import java.util.ArrayList;
import java.util.List;


public class CaseStatementTest {
	@Test
	public void testApplyTo2CaseElements1ElementInCaseListWithoutElse() {
		/*cond, x: INT;
		 * statement: CASE cond OF l11: x:= x1 END_CASE
		 * expected result:
		 * [{getVarInt(s0, cond) = l11, setVarInt(s0, x, x1)},
		 * {not(getVarInt(s0, cond) = l11), s0}]
		 */
		String condName = "cond";
		String xName = "x";
		int x1 = 1, x2 = 2;
		int l11 = -1, l21 = 1;
		String type = "INT";
		Term currentState = new Variable("s0");
		SymbolicVariable condVar = ExpressionFactory.createSymbolicVariable(condName);
		SymbolicVariable x = ExpressionFactory.createSymbolicVariable(xName);
		Expression cond = ExpressionFactory.createVariableExpression(condVar);
		su.nsk.iae.post.poST.Constant x1Const = ExpressionFactory.createIntConstant(x1);
		su.nsk.iae.post.poST.Constant x2Const = ExpressionFactory.createIntConstant(x2);
		Expression x1Expr = ExpressionFactory.createConstantExpression(x1Const);
		Expression x2Expr = ExpressionFactory.createConstantExpression(x2Const);
		Statement assignX1 = StatementFactory.createVariableAssignmentStatement(x, x1Expr);
		Statement assignX2 = StatementFactory.createVariableAssignmentStatement(x, x2Expr);
		List<Integer> caseList1 = new ArrayList<>();
		caseList1.add(l11);
		List<Integer> caseList2 = new ArrayList<>();
		caseList2.add(l21);
		List<Statement> caseStatement1 = new ArrayList<>();
		caseStatement1.add(assignX1);
		List<Statement> caseStatement2 = new ArrayList<>();
		caseStatement2.add(assignX2);
		CaseElement caseElement1 = StatementFactory.createCaseElement(caseList1, caseStatement1);
		CaseElement caseElement2 = StatementFactory.createCaseElement(caseList2, caseStatement2);
		List<CaseElement> caseElements = new ArrayList<>();
		caseElements.add(caseElement1);
		caseElements.add(caseElement2);
		Statement statement = StatementFactory.createCaseStatement(cond, caseElements, null);
		Path path = new Path(null, currentState);
		List<Path> paths = new ArrayList<>();
		paths.add(path);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(type, null, condVar, x);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant condCode = vcGenVars.getVariable(condName);
		su.nsk.iae.post.vcgenerator.Constant xCode = vcGenVars.getVariable(xName);
		List<Path> expected = new ArrayList<>();
		expected.add(new Path(
				eq(getVarInt(currentState, condCode), new su.nsk.iae.post.vcgenerator.Constant(l11)),
				setVarInt(currentState, xCode, new su.nsk.iae.post.vcgenerator.Constant(x1))));
		expected.add(new Path(
				eq(getVarInt(currentState, condCode), new su.nsk.iae.post.vcgenerator.Constant(l21)),
				setVarInt(currentState, xCode, new su.nsk.iae.post.vcgenerator.Constant(x2))));
		expected.add(new Path(
				and(
						not(eq(getVarInt(currentState, condCode), new su.nsk.iae.post.vcgenerator.Constant(l11))),
						not(eq(getVarInt(currentState, condCode), new su.nsk.iae.post.vcgenerator.Constant(l21)))),
				currentState));
		List<Path> result = statement.applyTo(paths, vcGenVars);
		Assert.assertEquals(expected,  result);
	}

	@Test
	public void testApplyTo1CaseElement2ElementsInCaseListWithElse() {
		/*cond, x: INT;
		 * statement: CASE cond OF l11, l12: x:= x1 END_CASE
		 * expected result:
		 * [{getVarInt(s0, cond) = l11 \/ getVarInt(s0, cond) = l12, setVarInt(s0, x, x1)},
		 * {not(getVarInt(s0, cond) = l11 \/ getVarInt(s0, cond) = l12), s0}]
		 */
		String condName = "cond";
		String xName = "x";
		int x1 = 1, x2 = 2;
		int l11 = 1, l12 = 2;
		String type = "INT";
		Term currentState = new Variable("s0");
		SymbolicVariable condVar = ExpressionFactory.createSymbolicVariable(condName);
		SymbolicVariable x = ExpressionFactory.createSymbolicVariable(xName);
		Expression cond = ExpressionFactory.createVariableExpression(condVar);
		su.nsk.iae.post.poST.Constant x1Const = ExpressionFactory.createIntConstant(x1);
		su.nsk.iae.post.poST.Constant x2Const = ExpressionFactory.createIntConstant(x2);
		Expression x1Expr = ExpressionFactory.createConstantExpression(x1Const);
		Expression x2Expr = ExpressionFactory.createConstantExpression(x2Const);
		Statement assignX1 = StatementFactory.createVariableAssignmentStatement(x, x1Expr);
		Statement assignX2 = StatementFactory.createVariableAssignmentStatement(x, x2Expr);
		List<Integer> caseList1 = new ArrayList<>();
		caseList1.add(l11);
		caseList1.add(l12);
		List<Statement> caseStatement1 = new ArrayList<>();
		caseStatement1.add(assignX1);
		CaseElement caseElement1 = StatementFactory.createCaseElement(caseList1, caseStatement1);
		List<CaseElement> caseElements = new ArrayList<>();
		caseElements.add(caseElement1);
		List<Statement> elseStatement = new ArrayList<>();
		elseStatement.add(assignX2);
		Statement statement = StatementFactory.createCaseStatement(cond, caseElements, elseStatement);
		Path path = new Path(null, currentState);
		List<Path> paths = new ArrayList<>();
		paths.add(path);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(type, null, condVar, x);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant condCode = vcGenVars.getVariable(condName);
		su.nsk.iae.post.vcgenerator.Constant xCode = vcGenVars.getVariable(xName);
		List<Path> expected = new ArrayList<>();
		expected.add(new Path(
				or(
						eq(getVarInt(currentState, condCode), new su.nsk.iae.post.vcgenerator.Constant(l11)), 
						eq(getVarInt(currentState, condCode), new su.nsk.iae.post.vcgenerator.Constant(l12))),
				setVarInt(currentState, xCode, new su.nsk.iae.post.vcgenerator.Constant(x1))));
		expected.add(new Path(
				not(or(eq(getVarInt(currentState, condCode), new su.nsk.iae.post.vcgenerator.Constant(l11)), 
						eq(getVarInt(currentState, condCode), new su.nsk.iae.post.vcgenerator.Constant(l12)))),
				setVarInt(currentState, xCode, new su.nsk.iae.post.vcgenerator.Constant(x2))));
		List<Path> result = statement.applyTo(paths, vcGenVars);
		Assert.assertEquals(expected,  result);
	}
	
	@Test
	public void testApplyToAfterExit() {
		/*cond, x: INT;
		 * statement: EXIT; CASE cond OF l11: x:= x1 END_CASE
		 * expected result:
		 * [{null, s0}]
		 */
		String condName = "cond";
		String xName = "x";
		int x1 = 1;
		int l11 = -1;
		String type = "INT";
		Term currentState = new Variable("s0");
		SymbolicVariable condVar = ExpressionFactory.createSymbolicVariable(condName);
		SymbolicVariable x = ExpressionFactory.createSymbolicVariable(xName);
		Expression cond = ExpressionFactory.createVariableExpression(condVar);
		su.nsk.iae.post.poST.Constant x1Const = ExpressionFactory.createIntConstant(x1);
		Expression x1Expr = ExpressionFactory.createConstantExpression(x1Const);
		Statement assignX1 = StatementFactory.createVariableAssignmentStatement(x, x1Expr);
		List<Integer> caseList1 = new ArrayList<>();
		caseList1.add(l11);
		List<Statement> caseStatement1 = new ArrayList<>();
		caseStatement1.add(assignX1);
		CaseElement caseElement1 = StatementFactory.createCaseElement(caseList1, caseStatement1);
		List<CaseElement> caseElements = new ArrayList<>();
		caseElements.add(caseElement1);
		Statement statement = StatementFactory.createCaseStatement(cond, caseElements, null);
		Path path = new Path(null, currentState);
		path.doExit();
		List<Path> paths = new ArrayList<>();
		paths.add(path);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(type, null, condVar, x);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		List<Path> result = statement.applyTo(paths, vcGenVars);
		Assert.assertEquals(paths,  result);
	}

}
