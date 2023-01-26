package su.nsk.iae.post.poST.impl;

import static su.nsk.iae.post.vcgenerator.Constant.True;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.junit.Test;

import su.nsk.iae.post.poST.Expression;
import su.nsk.iae.post.poST.Statement;
import su.nsk.iae.post.poST.SymbolicVariable;
import su.nsk.iae.post.poST.VarInitDeclaration;
import su.nsk.iae.post.vcgenerator.ComplexTerm;
import su.nsk.iae.post.vcgenerator.FunctionSymbol;
import su.nsk.iae.post.vcgenerator.ModificationType;
import su.nsk.iae.post.vcgenerator.Path;
import su.nsk.iae.post.vcgenerator.Term;
import su.nsk.iae.post.vcgenerator.VCGeneratorState;
import su.nsk.iae.post.vcgenerator.Variable;

public class ForStatementTest {
	@Test
	public void testApplyToDefaultStepSomePathsContainReturn() {
		/*i, x, a, b: INT;
		 * loop precondition^ [{inv1(s0), s0, NORMAL}, {inv2(s0), s0, RETURN}]
		 * statement: FOR i := a TO b DO IF cond THEN RETURN; END_IF END_FOR
		 * expected result:
		 * [{inv2(s0), s0, RETURN},
		 * {loopinv(s0) /\ 1 > 0 /\ getVarInt(s0, i) <= getVarInt(s0, b) /\ getVarBool(s0, cond), s0, RETURN},
		 * {loopinv(s0) /\ 1 < 0 /\ getVarInt(s0, i) >= getVarInt(s0, b) /\ getVarBool(s0, cond), s0, RETURN},
		 *  {loopinv(s0), s0, NORMAL}]
		 * vcs = [
		 * inv1(s0) --> loopinv(setVarInt(s0, i, getVarInt(s0, a))),
		 *  loopinv(s0) --> 1 \<noteq> 0,
		 *  loopinv(s0) /\ 1 > 0 /\ getVarInt(s0, i) <= getVarInt(s0, b) /\ not(getVarBool(s0, cond))--> loopinv(setVarInt(s0, i, getVarInt(s0, i) + 1)),
		 *  loopinv(s0) /\ 1 > 0 /\ getVarInt(s0, i) <= getVarInt(s0, b) /\ not(getVarBool(s0, cond))--> loopinv(setVarInt(s0, i, getVarInt(s0, i) + 1))]
		 */
		String iName = "i";
		String aName = "a";
		String bName = "b";
		String condName = "cond";
		Term s0 = new Variable("s0");
		SymbolicVariable i = ExpressionFactory.createSymbolicVariable(iName);
		SymbolicVariable aVar = ExpressionFactory.createSymbolicVariable(aName);
		SymbolicVariable bVar = ExpressionFactory.createSymbolicVariable(bName);
		SymbolicVariable condVar = ExpressionFactory.createSymbolicVariable(condName);
		Expression a = ExpressionFactory.createVariableExpression(aVar);
		Expression b = ExpressionFactory.createVariableExpression(bVar);
		Expression cond = ExpressionFactory.createVariableExpression(condVar);
		Statement mainStatement = StatementFactory.createReturnStatement();
		List<Statement> mainStatements = new ArrayList<>();
		mainStatements.add(mainStatement);
		Statement ifStatement = StatementFactory.createIfStatement(cond, mainStatements, null, null, null);
		List<Statement> loopBody = new ArrayList<>();
		loopBody.add(ifStatement);
		Statement forStatement = StatementFactory.createForStatement(i, a, b, null, loopBody);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration intVarDecl = ProgramFactory.createSimpleVarDeclaration("INT", null, i, aVar, bVar);
		VarInitDeclaration boolVarDecl = ProgramFactory.createSimpleVarDeclaration("BOOL", null, condVar);
		vcGenVars.addVars(intVarDecl, null, ModificationType.VAR);
		vcGenVars.addVars(boolVarDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant iCode = vcGenVars.getVariable(iName);
		su.nsk.iae.post.vcgenerator.Constant aCode = vcGenVars.getVariable(aName);
		su.nsk.iae.post.vcgenerator.Constant bCode = vcGenVars.getVariable(bName);
		su.nsk.iae.post.vcgenerator.Constant condCode = vcGenVars.getVariable(condName);
		FunctionSymbol inv1 = new FunctionSymbol("inv1", true);
		FunctionSymbol inv2 = new FunctionSymbol("inv2", true);
		FunctionSymbol loopinv = new FunctionSymbol("loopinv", true);
		Term inv1s0 = new ComplexTerm(inv1, s0);
		Term inv2s0 = new ComplexTerm(inv2, s0);
		Term loopinvs0 = new ComplexTerm(loopinv, s0);
		su.nsk.iae.post.vcgenerator.Constant _1 = new su.nsk.iae.post.vcgenerator.Constant(1);
		su.nsk.iae.post.vcgenerator.Constant _0 = new su.nsk.iae.post.vcgenerator.Constant(0);
		Path path1 = new Path(inv1s0, s0);
		Path path2 = new Path(inv2s0, s0);
		path2.doReturn();
		List<Path> paths = new ArrayList<>();
		paths.add(path1);
		paths.add(path2);
		List<Path> expected = new ArrayList<>();
		expected.add(path2);
		Path mainBranch1 = new Path(
				and(loopinvs0, greater(_1, _0), leq(getVarInt(s0, iCode), getVarInt(s0, bCode)), getVarBool(s0, condCode)), s0);
		mainBranch1.doReturn();
		expected.add(mainBranch1);
		Path mainBranch2 = new Path(
				and(loopinvs0, less(_1, _0), geq(getVarInt(s0, iCode), getVarInt(s0, bCode)), getVarBool(s0, condCode)), s0);
		mainBranch2.doReturn();
		expected.add(mainBranch2);
		expected.add(new Path(loopinvs0, s0));
		List<Term> expectedVC = new ArrayList<>();
		expectedVC.add(impl(inv1s0, new ComplexTerm(loopinv, setVarInt(s0, iCode, getVarInt(s0, aCode)))));
		expectedVC.add(impl(loopinvs0, noteq(_1, _0)));
		expectedVC.add(impl(and(loopinvs0, greater(_1, _0), leq(getVarInt(s0, iCode), getVarInt(s0, bCode)), not(getVarBool(s0, condCode))),
				new ComplexTerm(loopinv, setVarInt(s0, iCode, plus(getVarInt(s0, iCode), _1)))));
		expectedVC.add(impl(and(loopinvs0, less(_1, _0), geq(getVarInt(s0, iCode), getVarInt(s0, bCode)), not(getVarBool(s0, condCode))),
				new ComplexTerm(loopinv, setVarInt(s0, iCode, plus(getVarInt(s0, iCode), _1)))));
		List<Path> result = forStatement.applyTo(paths, vcGenVars);
		Assert.assertEquals(expected,  result);
		Assert.assertEquals(expectedVC,  vcGenVars.getVcSet());
	}
	
	@Test
	public void testApplyToEmptyLoopBody() {
		/*i, a, b, c: INT;
		 * cond: BOOL;
		 * loop precondition^ [{inv1(s0), s0, NORMAL}, {inv2(s0), s0, RETURN}]
		 * statement: FOR i := a TO b DO END_FOR
		 * expected result:
		 * [{inv2(s0), s0, RETURN},
		 *  {loopinv(s0), s0, NORMAL}]
		 * vcs = [
		 * inv1(s0) --> loopinv(setVarInt(s0, i, getVarInt(s0, a))),
		 *  loopinv(s0) --> getVarInt(s0, c) \<noteq> 0,
		 *  loopinv(s0) /\ getVarInt(s0, c) > 0 /\ getVarInt(s0, i) <= getVarInt(s0, b)
		 *  --> loopinv(setVarInt(s0, i, getVarInt(s0, i) + 1)),
		 *  loopinv(s0) /\ getVarInt(s0, c) < 0 /\ getVarInt(s0, i) >= getVarInt(s0, b)
		 *  --> loopinv(setVarInt(s0, i, getVarInt(s0, i) + 1))
		 */
		String iName = "i";
		String cName = "x";
		String aName = "a";
		String bName = "b";
		String condName = "cond";
		Term s0 = new Variable("s0");
		SymbolicVariable i = ExpressionFactory.createSymbolicVariable(iName);
		SymbolicVariable aVar = ExpressionFactory.createSymbolicVariable(aName);
		SymbolicVariable bVar = ExpressionFactory.createSymbolicVariable(bName);
		SymbolicVariable cVar = ExpressionFactory.createSymbolicVariable(cName);
		SymbolicVariable condVar = ExpressionFactory.createSymbolicVariable(condName);
		Expression a = ExpressionFactory.createVariableExpression(aVar);
		Expression b = ExpressionFactory.createVariableExpression(bVar);
		Expression c = ExpressionFactory.createVariableExpression(cVar);
		Statement forStatement = StatementFactory.createForStatement(i, a, b, c, null);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration("INT", null, i, aVar, bVar, cVar);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant iCode = vcGenVars.getVariable(iName);
		su.nsk.iae.post.vcgenerator.Constant aCode = vcGenVars.getVariable(aName);
		su.nsk.iae.post.vcgenerator.Constant bCode = vcGenVars.getVariable(bName);
		su.nsk.iae.post.vcgenerator.Constant cCode = vcGenVars.getVariable(cName);
		FunctionSymbol inv1 = new FunctionSymbol("inv1", true);
		FunctionSymbol inv2 = new FunctionSymbol("inv2", true);
		FunctionSymbol loopinv = new FunctionSymbol("loopinv", true);
		Term inv1s0 = new ComplexTerm(inv1, s0);
		Term inv2s0 = new ComplexTerm(inv2, s0);
		Term loopinvs0 = new ComplexTerm(loopinv, s0);
		su.nsk.iae.post.vcgenerator.Constant _1 = new su.nsk.iae.post.vcgenerator.Constant(1);
		su.nsk.iae.post.vcgenerator.Constant _0 = new su.nsk.iae.post.vcgenerator.Constant(0);
		Path path1 = new Path(inv1s0, s0);
		Path path2 = new Path(inv2s0, s0);
		path2.doReturn();
		List<Path> paths = new ArrayList<>();
		paths.add(path1);
		paths.add(path2);
		List<Path> expected = new ArrayList<>();
		expected.add(path2);
		expected.add(new Path(loopinvs0, s0));
		List<Term> expectedVC = new ArrayList<>();
		expectedVC.add(impl(inv1s0, new ComplexTerm(loopinv, setVarInt(s0, iCode, getVarInt(s0, aCode)))));
		expectedVC.add(impl(loopinvs0, noteq(getVarInt(s0, cCode), _0)));
		expectedVC.add(impl(and(loopinvs0, greater(getVarInt(s0, cCode), _0), leq(getVarInt(s0, iCode), getVarInt(s0, bCode))),
				new ComplexTerm(loopinv, setVarInt(s0, iCode, plus(getVarInt(s0, iCode), getVarInt(s0, cCode))))));
		expectedVC.add(impl(and(loopinvs0, less(getVarInt(s0, cCode), _0), geq(getVarInt(s0, iCode), getVarInt(s0, bCode))),
				new ComplexTerm(loopinv, setVarInt(s0, iCode, plus(getVarInt(s0, iCode), getVarInt(s0, cCode))))));
		List<Path> result = forStatement.applyTo(paths, vcGenVars);
		Assert.assertEquals(expected,  result);
		Assert.assertEquals(expectedVC,  vcGenVars.getVcSet());
		}

}
