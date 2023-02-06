package su.nsk.iae.post.poST.impl;

import static su.nsk.iae.post.vcgenerator.Constant.True;
import static su.nsk.iae.post.vcgenerator.TermFactory.and;
import static su.nsk.iae.post.vcgenerator.TermFactory.getVarBool;
import static su.nsk.iae.post.vcgenerator.TermFactory.impl;
import static su.nsk.iae.post.vcgenerator.TermFactory.not;
import static su.nsk.iae.post.vcgenerator.TermFactory.setVarBool;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import su.nsk.iae.post.poST.Expression;
import su.nsk.iae.post.poST.InputOutputVarDeclaration;
import su.nsk.iae.post.poST.InputVarDeclaration;
import su.nsk.iae.post.poST.OutputVarDeclaration;
import su.nsk.iae.post.poST.State;
import su.nsk.iae.post.poST.Statement;
import su.nsk.iae.post.poST.SymbolicVariable;
import su.nsk.iae.post.poST.VarDeclaration;
import su.nsk.iae.post.poST.VarInitDeclaration;
import su.nsk.iae.post.vcgenerator.ComplexTerm;
import su.nsk.iae.post.vcgenerator.FunctionSymbol;
import su.nsk.iae.post.vcgenerator.ModificationType;
import su.nsk.iae.post.vcgenerator.Path;
import su.nsk.iae.post.vcgenerator.Term;
import su.nsk.iae.post.vcgenerator.VCGeneratorState;
import su.nsk.iae.post.vcgenerator.Variable;

public class RepeatStatementTest {
	@Test
	public void testApplyToAllPathsInLoopBodyNotContainReturn() {
		/*cond: BOOL;
		 * loop precondition^ [{inv1(s0), s0, NORMAL}, {inv2(s0), s0, RETURN}]
		 * statement: {loopin} REPEAT x:= TRUE; UNTIL cond END_REPEAT
		 * expected result: [{inv2(s0), s0, RETURN}, {loopinv(s0) /\ not(getVarBool(s0, cond)), s0, NORMAL}]
		 * vcs = [{inv1(s0) --> loopinv(setVarBool(s0, x, True)), loopinv(s0) /\ getVarBool(s0, cond) --> loopinv(setVarBool(s0, x, True))]
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
		Statement repeatStatement = StatementFactory.createRepeatStatement(loopBody, cond);
		State currentProcessState = ProgramFactory.createState("state1", loopBody, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(currentProcessState);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess("process1", inVars, outVars, inOutVars, vars, states);
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
		vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant condCode = vcGenVars.getVariable(condName);
		su.nsk.iae.post.vcgenerator.Constant xCode = vcGenVars.getVariable(xName);
		List<Path> expected = new ArrayList<>();
		expected.add(path2);
		Path loopPostcondition = new Path(and(loopinvs0, not(getVarBool(s0, condCode))), s0);
		expected.add(loopPostcondition);
		List<Term> expectedVC = new ArrayList<>();
		expectedVC.add(impl(inv1s0, new ComplexTerm(loopinv, setVarBool(s0, xCode, True))));
		expectedVC.add(impl(and(loopinvs0, getVarBool(s0, condCode)), new ComplexTerm(loopinv, setVarBool(s0, xCode, True))));
		List<Path> result = repeatStatement.applyTo(loopPrecondition, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedVC, vcGenVars.getVcSet());		
	}
	
	@Test
	public void testApplyToNotAllPathsInLoopBodyContainReturn() {
		/*whileCond, ifCond: BOOL;
		 * loop precondition^ [{inv1(s0), s0, NORMAL}, {inv2(s0), s0, RETURN}]
		 * statement: {loopin} REPEAT IF ifCond THEN RETURN; END_IF UNTIL cond END_REPEAT
		 * expected result:
		 *  [{inv1(s0) /\ getVarBool(s0, repeatCond) /\ getVarBool(s0, ifCond), s0, RETURN},
		 *  {inv2(s0), s0, RETURN}, 
		 * {loopinv(s0) /\ getVarBool(s0, repeatCond) /\ getVarBool(s0, ifCond), s0, RETURN},
		 * {loopinv(s0) /\ not(getVarBool(s0, repeatCond))]
		 * vcs = [{inv1(s0) /\ getVarBool(s0, repeatCond) /\ not(getVarBool(s0, ifCond)) --> loopinv(s0),
		 *  loopinv(s0) /\ getVarBool(s0, repeatCond) /\ not(getVarBool(s0, ifCond)) --> loopinv(s0)]
		 */
		String whileCondName = "whileCond";
		String ifCondName = "ifCond";
		String type = "BOOL";
		Term s0 = new Variable("s0");
		SymbolicVariable whileCondVar = ExpressionFactory.createSymbolicVariable(whileCondName);
		SymbolicVariable ifCondVar = ExpressionFactory.createSymbolicVariable(ifCondName);
		Expression repeatCond = ExpressionFactory.createVariableExpression(whileCondVar);
		Expression ifCond = ExpressionFactory.createVariableExpression(ifCondVar);
		Statement mainStatement = StatementFactory.createReturnStatement();
		List<Statement> mainStatements = new ArrayList<>();
		mainStatements.add(mainStatement);
		Statement ifStatement = StatementFactory.createIfStatement(ifCond, mainStatements, null, null, null);
		List<Statement> loopBody = new ArrayList<>();
		loopBody.add(ifStatement);
		Statement repeatStatement = StatementFactory.createRepeatStatement(loopBody, repeatCond);
		State currentProcessState = ProgramFactory.createState("state1", loopBody, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(currentProcessState);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess("process1", inVars, outVars, inOutVars, vars, states);
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
		vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant repeatCondCode = vcGenVars.getVariable(whileCondName);
		su.nsk.iae.post.vcgenerator.Constant ifCondCode = vcGenVars.getVariable(ifCondName);
		List<Path> expected = new ArrayList<>();
		Path mainBranchFirstIter = new Path(and(inv1s0, getVarBool(s0, ifCondCode)), s0);
		mainBranchFirstIter.doReturn();
		expected.add(mainBranchFirstIter);
		expected.add(path2);
		Path mainBranch = new Path(and(loopinvs0, getVarBool(s0, repeatCondCode), getVarBool(s0, ifCondCode)), s0);
		mainBranch.doReturn();
		expected.add(mainBranch);
		Path loopPostcondition = new Path(and(new ComplexTerm(loopinv, s0), not(getVarBool(s0, repeatCondCode))), s0);
		expected.add(loopPostcondition);
		List<Term> expectedVC = new ArrayList<>();
		expectedVC.add(impl(and(inv1s0, not(getVarBool(s0, ifCondCode))), loopinvs0));
		expectedVC.add(impl(and(loopinvs0, getVarBool(s0, repeatCondCode), not(getVarBool(s0, ifCondCode))), loopinvs0));
		List<Path> result = repeatStatement.applyTo(loopPrecondition, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedVC, vcGenVars.getVcSet());		
	}
	
	@Test
	public void testApplyToSomePathsInLoopBodyContainExit() {
		/*whileCond, ifCond: BOOL;
		 * loop precondition^ [{inv1(s0), s0, NORMAL}, {inv2(s0), s0, RETURN}]
		 * statement: {loopin} REPEAT IF ifCond THEN EXIT; END_IF UNTIL cond END_REPEAT
		 * expected result:
		 *  [{inv1(s0) /\ getVarBool(s0, repeatCond) /\ getVarBool(s0, ifCond), s0, NORMAL},
		 *  {inv2(s0), s0, RETURN}, 
		 * {loopinv(s0) /\ getVarBool(s0, repeatCond) /\ getVarBool(s0, ifCond), s0, NORMAL},
		 * {loopinv(s0) /\ not(getVarBool(s0, repeatCond)), s0, NORMAL}]
		 * vcs = [{inv1(s0) /\ getVarBool(s0, repeatCond) /\ not(getVarBool(s0, ifCond)) --> loopinv(s0),
		 *  loopinv(s0) /\ getVarBool(s0, repeatCond) /\ not(getVarBool(s0, ifCond)) --> loopinv(s0)]
		 */
		String whileCondName = "whileCond";
		String ifCondName = "ifCond";
		String type = "BOOL";
		Term s0 = new Variable("s0");
		SymbolicVariable whileCondVar = ExpressionFactory.createSymbolicVariable(whileCondName);
		SymbolicVariable ifCondVar = ExpressionFactory.createSymbolicVariable(ifCondName);
		Expression repeatCond = ExpressionFactory.createVariableExpression(whileCondVar);
		Expression ifCond = ExpressionFactory.createVariableExpression(ifCondVar);
		Statement mainStatement = StatementFactory.createExitStatement();
		List<Statement> mainStatements = new ArrayList<>();
		mainStatements.add(mainStatement);
		Statement ifStatement = StatementFactory.createIfStatement(ifCond, mainStatements, null, null, null);
		List<Statement> loopBody = new ArrayList<>();
		loopBody.add(ifStatement);
		Statement repeatStatement = StatementFactory.createRepeatStatement(loopBody, repeatCond);
		State currentProcessState = ProgramFactory.createState("state1", loopBody, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(currentProcessState);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess("process1", inVars, outVars, inOutVars, vars, states);
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
		vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant repeatCondCode = vcGenVars.getVariable(whileCondName);
		su.nsk.iae.post.vcgenerator.Constant ifCondCode = vcGenVars.getVariable(ifCondName);
		List<Path> expected = new ArrayList<>();
		Path mainBranchFirstIter = new Path(and(inv1s0, getVarBool(s0, ifCondCode)), s0);
		expected.add(mainBranchFirstIter);
		expected.add(path2);
		Path mainBranch = new Path(and(loopinvs0, getVarBool(s0, repeatCondCode), getVarBool(s0, ifCondCode)), s0);
		expected.add(mainBranch);
		Path loopPostcondition = new Path(and(new ComplexTerm(loopinv, s0), not(getVarBool(s0, repeatCondCode))), s0);
		expected.add(loopPostcondition);
		List<Term> expectedVC = new ArrayList<>();
		expectedVC.add(impl(and(inv1s0, not(getVarBool(s0, ifCondCode))), loopinvs0));
		expectedVC.add(impl(and(loopinvs0, getVarBool(s0, repeatCondCode), not(getVarBool(s0, ifCondCode))), loopinvs0));
		List<Path> result = repeatStatement.applyTo(loopPrecondition, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedVC, vcGenVars.getVcSet());		
	}
}
