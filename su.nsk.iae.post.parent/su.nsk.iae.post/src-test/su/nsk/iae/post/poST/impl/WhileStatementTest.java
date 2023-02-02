package su.nsk.iae.post.poST.impl;

import org.junit.Assert;

import org.junit.Test;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;
import su.nsk.iae.post.vcgenerator.Variable;

import static su.nsk.iae.post.vcgenerator.TermFactory.*;

import java.util.ArrayList;
import java.util.List;
import static su.nsk.iae.post.vcgenerator.Constant.*;

;public class WhileStatementTest {
	@Test
	public void testApplyToAllPathsInLoopBodyNotContainReturn() {
		/*cond: BOOL;
		 * loop precondition^ [{inv1(s0), s0, NORMAL}, {inv2(s0), s0, RETURN}]
		 * statement: {loopin} WHILE cond DO x:= TRUE; END_WHILE
		 * expected result: [{inv2(s0), s0, RETURN}, {loopinv(s0) /\ not(getVarBool(s0, cond)), s0, NORMAL}]
		 * vcs = [{inv1(s0) --> loopinv(s0), loopinv(s0) /\ getVarBool(s0, cond) --> loopinv(setVarBool(s0, x, True))]
		 */
		String condName = "cond";
		String xName = "x";
		String type = "BOOL";
		Term s0 = new Variable("s0");
		SymbolicVariable condVar = ExpressionFactory.createSymbolicVariable(condName);
		SymbolicVariable x = ExpressionFactory.createSymbolicVariable(xName);
		Expression cond = ExpressionFactory.createVariableExpression(condVar);
		su.nsk.iae.post.poST.Constant valueConst = ExpressionFactory.createBooleanConstant(true);
		Expression valueExpr = ExpressionFactory.createConstantExpression(valueConst);
		Statement loopBodyStatement = StatementFactory.createVariableAssignmentStatement(x, valueExpr);
		List<Statement> loopBody = new ArrayList<>();
		loopBody.add(loopBodyStatement);
		Statement whileStatement = StatementFactory.createWhileStatement(cond, loopBody);
		FunctionSymbol inv1 = new FunctionSymbol("inv1", true);
		FunctionSymbol inv2 = new FunctionSymbol("inv2", true);
		FunctionSymbol loopinv = new FunctionSymbol("loopinv", true);
		Term inv1s0 = new ComplexTerm(inv1, s0);
		Term inv2s0 = new ComplexTerm(inv2, s0);
		Term loopinvs0 = new ComplexTerm(loopinv, s0);
		List<Path> loopPrecondition = new ArrayList<>();
		loopPrecondition.add(new Path(inv1s0, s0));
		Path path2 = new Path(inv2s0, s0);
		path2.doReturn();
		loopPrecondition.add(path2);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(type, null, condVar, x);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant condCode = vcGenVars.getVariable(condName);
		su.nsk.iae.post.vcgenerator.Constant xCode = vcGenVars.getVariable(xName);
		List<Path> expected = new ArrayList<>();
		expected.add(path2);
		Path loopPostcondition = new Path(and(loopinvs0, not(getVarBool(s0, condCode))), s0);
		expected.add(loopPostcondition);
		List<Term> expectedVC = new ArrayList<>();
		expectedVC.add(impl(inv1s0, loopinvs0));
		expectedVC.add(impl(and(loopinvs0, getVarBool(s0, condCode)), new ComplexTerm(loopinv, setVarBool(s0, xCode, True))));
		List<Path> result = whileStatement.applyTo(loopPrecondition, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedVC, vcGenVars.getVcSet());		
	}
	
	@Test
	public void testApplyToNotAllPathsInLoopBodyContainReturn() {
		/*whileCond, ifCond: BOOL;
		 * loop precondition^ [{inv1(s0), s0, NORMAL}, {inv2(s0), s0, RETURN}]
		 * statement: {loopin} WHILE whileCond DO IF ifCond THEN RETURN; END_IF END_WHILE
		 * expected result:
		 *  [{inv2(s0), s0, RETURN}, 
		 * {loopinv(s0) /\ getVarBool(s0, whileCond) /\ getVarBool(s0, ifCond), s0, RETURN},
		 * {loopinv(s0) /\ not(getVarBool(s0, whileCond))]
		 * vcs = [{inv1(s0) --> loopinv(s0), loopinv(s0) /\ getVarBool(s0, whileCond) /\ not(getVarBool(s0, ifCond)) --> loopinv(s0)]
		 */
		String whileCondName = "whileCond";
		String ifCondName = "ifCond";
		String type = "BOOL";
		Term s0 = new Variable("s0");
		SymbolicVariable whileCondVar = ExpressionFactory.createSymbolicVariable(whileCondName);
		SymbolicVariable ifCondVar = ExpressionFactory.createSymbolicVariable(ifCondName);
		Expression whileCond = ExpressionFactory.createVariableExpression(whileCondVar);
		Expression ifCond = ExpressionFactory.createVariableExpression(ifCondVar);
		Statement mainStatement = StatementFactory.createReturnStatement();
		List<Statement> mainStatements = new ArrayList<>();
		mainStatements.add(mainStatement);
		Statement ifStatement = StatementFactory.createIfStatement(ifCond, mainStatements, null, null, null);
		List<Statement> loopBody = new ArrayList<>();
		loopBody.add(ifStatement);
		Statement whileStatement = StatementFactory.createWhileStatement(whileCond, loopBody);
		FunctionSymbol inv1 = new FunctionSymbol("inv1", true);
		FunctionSymbol inv2 = new FunctionSymbol("inv2", true);
		FunctionSymbol loopinv = new FunctionSymbol("loopinv", true);
		Term inv1s0 = new ComplexTerm(inv1, s0);
		Term inv2s0 = new ComplexTerm(inv2, s0);
		Term loopinvs0 = new ComplexTerm(loopinv, s0);
		List<Path> loopPrecondition = new ArrayList<>();
		loopPrecondition.add(new Path(inv1s0, s0));
		Path path2 = new Path(inv2s0, s0);
		path2.doReturn();
		loopPrecondition.add(path2);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(type, null, whileCondVar, ifCondVar);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant whileCondCode = vcGenVars.getVariable(whileCondName);
		su.nsk.iae.post.vcgenerator.Constant ifCondCode = vcGenVars.getVariable(ifCondName);
		List<Path> expected = new ArrayList<>();
		expected.add(path2);
		Path mainBranch = new Path(and(loopinvs0, getVarBool(s0, whileCondCode), getVarBool(s0, ifCondCode)), s0);
		mainBranch.doReturn();
		expected.add(mainBranch);
		Path loopPostcondition = new Path(and(new ComplexTerm(loopinv, s0), not(getVarBool(s0, whileCondCode))), s0);
		expected.add(loopPostcondition);
		List<Term> expectedVC = new ArrayList<>();
		expectedVC.add(impl(inv1s0, loopinvs0));
		expectedVC.add(impl(and(loopinvs0, getVarBool(s0, whileCondCode), not(getVarBool(s0, ifCondCode))), loopinvs0));
		List<Path> result = whileStatement.applyTo(loopPrecondition, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedVC, vcGenVars.getVcSet());		
	}
	
	@Test
	public void testApplyToSomePathsInLoopBodyContainExit() {
		/*whileCond, ifCond: BOOL;
		 * loop precondition^ [{inv1(s0), s0, NORMAL}, {inv2(s0), s0, RETURN}]
		 * statement: {loopin} WHILE whileCond DO IF ifCond THEN EXIT; END_IF END_WHILE
		 * expected result:
		 *  [{inv2(s0), s0, RETURN}, 
		 * {loopinv(s0) /\ getVarBool(s0, whileCond) /\ getVarBool(s0, ifCond), s0, NORMAL},
		 * {loopinv(s0) /\ not(getVarBool(s0, whileCond))]
		 * vcs = [{inv1(s0) --> loopinv(s0), loopinv(s0) /\ getVarBool(s0, whileCond) /\ not(getVarBool(s0, ifCond)) --> loopinv(s0)]
		 */
		String whileCondName = "whileCond";
		String ifCondName = "ifCond";
		String type = "BOOL";
		Term s0 = new Variable("s0");
		SymbolicVariable whileCondVar = ExpressionFactory.createSymbolicVariable(whileCondName);
		SymbolicVariable ifCondVar = ExpressionFactory.createSymbolicVariable(ifCondName);
		Expression whileCond = ExpressionFactory.createVariableExpression(whileCondVar);
		Expression ifCond = ExpressionFactory.createVariableExpression(ifCondVar);
		Statement mainStatement = StatementFactory.createExitStatement();
		List<Statement> mainStatements = new ArrayList<>();
		mainStatements.add(mainStatement);
		Statement ifStatement = StatementFactory.createIfStatement(ifCond, mainStatements, null, null, null);
		List<Statement> loopBody = new ArrayList<>();
		loopBody.add(ifStatement);
		Statement whileStatement = StatementFactory.createWhileStatement(whileCond, loopBody);
		FunctionSymbol inv1 = new FunctionSymbol("inv1", true);
		FunctionSymbol inv2 = new FunctionSymbol("inv2", true);
		FunctionSymbol loopinv = new FunctionSymbol("loopinv", true);
		Term inv1s0 = new ComplexTerm(inv1, s0);
		Term inv2s0 = new ComplexTerm(inv2, s0);
		Term loopinvs0 = new ComplexTerm(loopinv, s0);
		List<Path> loopPrecondition = new ArrayList<>();
		loopPrecondition.add(new Path(inv1s0, s0));
		Path path2 = new Path(inv2s0, s0);
		path2.doReturn();
		loopPrecondition.add(path2);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(type, null, whileCondVar, ifCondVar);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant whileCondCode = vcGenVars.getVariable(whileCondName);
		su.nsk.iae.post.vcgenerator.Constant ifCondCode = vcGenVars.getVariable(ifCondName);
		List<Path> expected = new ArrayList<>();
		expected.add(path2);
		Path mainBranch = new Path(and(loopinvs0, getVarBool(s0, whileCondCode), getVarBool(s0, ifCondCode)), s0);
		expected.add(mainBranch);
		Path loopPostcondition = new Path(and(new ComplexTerm(loopinv, s0), not(getVarBool(s0, whileCondCode))), s0);
		expected.add(loopPostcondition);
		List<Term> expectedVC = new ArrayList<>();
		expectedVC.add(impl(inv1s0, loopinvs0));
		expectedVC.add(impl(and(loopinvs0, getVarBool(s0, whileCondCode), not(getVarBool(s0, ifCondCode))), loopinvs0));
		List<Path> result = whileStatement.applyTo(loopPrecondition, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedVC, vcGenVars.getVcSet());		
	}
}
