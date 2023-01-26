package su.nsk.iae.post.poST.impl;

import org.eclipse.emf.common.util.*;

import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.Resource.Diagnostic;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;
import org.junit.Assert;
import org.junit.Test;

import com.google.inject.Inject;
import com.google.inject.Injector;

import su.nsk.iae.post.PoSTStandaloneSetup;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;

import java.io.ByteArrayInputStream;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;

import static su.nsk.iae.post.vcgenerator.Constant.*;
import org.eclipse.xtext.testing.util.*;

;public class PrimaryExpressionTest {
	
	@Test
	public void testgenerateProcessStatusExpressionStop() {
		/*expression: PROCESS p IN STATE STOP
		 * expected result: getPstate(s0, p) = stop
		 */
		String processName = "p";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s9");
		su.nsk.iae.post.poST.Process process = new ProcessImpl();
		process.setName(processName);
		PrimaryExpression expr = ExpressionFactory.createProcessStopExpression(process);
		VCGeneratorState vcGenVars =new VCGeneratorState();
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		Term expected = eq(getPstate(currentState, procCode), stop);
		Term result = expr.generateExpression(currentState, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.BOOL, result.getType());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testgenerateProcessStatusExpressionError() {
		/*expression: PROCESS IN STATE ERROR
		 * expected result: getPstate(s0, p) = error
		 */
		String processName = "p";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s9");
		su.nsk.iae.post.poST.Process process = new ProcessImpl();
		process.setName(processName);
		PrimaryExpression expr = ExpressionFactory.createProcessErrorExpression(process);
		VCGeneratorState vcGenVars =new VCGeneratorState();
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		Term expected = eq(getPstate(currentState, procCode), error);
		Term result = expr.generateExpression(currentState, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.BOOL, result.getType());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testgenerateProcessStatusExpressionInactive() {
		/*expression PROCESS IN STATE INACTIVE
		 * expected result: getPstate(s0, p) = stop \/ getPstate(s0, p) = error
		 */
		String processName = "p";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s9");
		su.nsk.iae.post.poST.Process process = new ProcessImpl();
		process.setName(processName);
		PrimaryExpression expr = ExpressionFactory.createProcessInactiveExpression(process);
		VCGeneratorState vcGenVars =new VCGeneratorState();
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		Term expected = or(eq(getPstate(currentState, procCode), stop), eq(getPstate(currentState, procCode), error));
		Term result = expr.generateExpression(currentState, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.BOOL, result.getType());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testgenerateProcessStatusExpressionActive() {
		/*expression: PROCESS p IN STATE ACTIVE
		 * expected result: not(getPstate(s0, p) = stop \/ getPstate(s0, p) = error)
		 */
		String processName = "p";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s9");
		su.nsk.iae.post.poST.Process process = new ProcessImpl();
		process.setName(processName);
		PrimaryExpression expr = ExpressionFactory.createProcessActiveExpression(process);
		VCGeneratorState vcGenVars =new VCGeneratorState();
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		Term expected = not(or(eq(getPstate(currentState, procCode), stop), eq(getPstate(currentState, procCode), error)));
		Term result = expr.generateExpression(currentState, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.BOOL, result.getType());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void testgenerateExpressionNestExpr() {
		/*a: BOOL
		 * expression: (a)
		 * expected result: getVarBool(s0, a)
		 */
		String variableName = "a";
		String variableType = "BOOL";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable variable = ExpressionFactory.createSymbolicVariable(variableName);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration(variableType, null, variable);
		PrimaryExpression nestExpr = ExpressionFactory.createVariableExpression(variable);
		PrimaryExpression expr = ExpressionFactory.createNestExpression(nestExpr);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant varCode = vcGenVars.getVariable(variableName);
		Term expected = getVarBool(currentState, varCode);
		Term result = expr.generateExpression(currentState, vcGenVars);
		Assert.assertEquals(expected, result);
		Assert.assertNull(result.getPrecondition());
		Assert.assertEquals(expected.getType(), result.getType());	
	}
	
	@Test
	public void testGenerateExpressionBoolArray() {
		/*a: ARRAY [start .. end] OF BOOL
		 * expression: a[i]
		 * expected result: getVarArrayBool(s0, a, i)
		 * expected precondition: start <= getVarInt(s0, i) /\ getVarInt(s0, i) <= end
		 */
		String arrayName = "a";
		String type = "BOOL";
		int startIndex = 1, endIndex = 10;
		String indexName = "i";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable array = ExpressionFactory.createSymbolicVariable(arrayName);
		SymbolicVariable index = ExpressionFactory.createSymbolicVariable(indexName);
		Expression indexExpr = ExpressionFactory.createVariableExpression(index);
		Expression ai = ExpressionFactory.createArrayVariableExpression(array, indexExpr);
		su.nsk.iae.post.poST.Constant startConst = ExpressionFactory.createIntConstant(startIndex);
		su.nsk.iae.post.poST.Constant endConst = ExpressionFactory.createIntConstant(endIndex);
		Expression start = ExpressionFactory.createConstantExpression(startConst);
		Expression end = ExpressionFactory.createConstantExpression(endConst);
		VarInitDeclaration arrayDecl = ProgramFactory.createArrayVarDeclaration(start, end, type, null, array);
		VarInitDeclaration iDecl = ProgramFactory.createSimpleVarDeclaration("INT", null, index);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(arrayDecl, null, ModificationType.VAR);
		globVars.addVars(iDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant arrayCode = globVars.getVariable(arrayName);
		su.nsk.iae.post.vcgenerator.Constant indexCode = globVars.getVariable(indexName);
		Term newState = globVars.initializeVar(arrayCode, currentState);
		Term expected = getVarArrayBool(currentState, arrayCode, getVarInt(currentState, indexCode));
		Term expectedPrecondition = and(
				leq(new su.nsk.iae.post.vcgenerator.Constant(startIndex), getVarInt(currentState, indexCode)),
				leq(getVarInt(currentState, indexCode), new su.nsk.iae.post.vcgenerator.Constant(endIndex)));
		Term result = ai.generateExpression(newState, globVars);
		Assert.assertEquals(currentState,  newState);;
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedPrecondition,  result.getPrecondition());
		Assert.assertEquals(DataType.BOOL,  result.getType());
	}
	
	@Test
	public void testGenerateExpressionIntArray() {
		/*a: ARRAY [start .. end] OF INT
		 * expression: a[i]
		 * expected result: getVarArrayInt(s0, a, i)
		 * expected precondition: start <= getVarInt(s0, i) /\ getVarInt(s0, i) <= end
		 */
		String arrayName = "a";
		String type = "INT";
		int startIndex = 1, endIndex = 10;
		String indexName = "i";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable array = ExpressionFactory.createSymbolicVariable(arrayName);
		SymbolicVariable index = ExpressionFactory.createSymbolicVariable(indexName);
		Expression indexExpr = ExpressionFactory.createVariableExpression(index);
		Expression ai = ExpressionFactory.createArrayVariableExpression(array, indexExpr);
		su.nsk.iae.post.poST.Constant startConst = ExpressionFactory.createIntConstant(startIndex);
		su.nsk.iae.post.poST.Constant endConst = ExpressionFactory.createIntConstant(endIndex);
		Expression start = ExpressionFactory.createConstantExpression(startConst);
		Expression end = ExpressionFactory.createConstantExpression(endConst);
		VarInitDeclaration arrayDecl = ProgramFactory.createArrayVarDeclaration(start, end, type, null, array);
		VarInitDeclaration iDecl = ProgramFactory.createSimpleVarDeclaration("INT", null, index);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(arrayDecl, null, ModificationType.VAR);
		globVars.addVars(iDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant arrayCode = globVars.getVariable(arrayName);
		su.nsk.iae.post.vcgenerator.Constant indexCode = globVars.getVariable(indexName);
		Term newState = globVars.initializeVar(arrayCode, currentState);
		Term expected = getVarArrayInt(currentState, arrayCode, getVarInt(currentState, indexCode));
		Term expectedPrecondition = and(
				leq(new su.nsk.iae.post.vcgenerator.Constant(startIndex), getVarInt(currentState, indexCode)),
				leq(getVarInt(currentState, indexCode), new su.nsk.iae.post.vcgenerator.Constant(endIndex)));
		Term result = ai.generateExpression(newState, globVars);
		Assert.assertEquals(currentState,  newState);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedPrecondition,  result.getPrecondition());
		Assert.assertEquals(DataType.INT,  result.getType());
	}
	
	@Test
	public void testGenerateExpressionRealArray() {
		/*a: ARRAY [start .. end] OF REAL
		 * expression: a[i]
		 * expected result: getVarArrayReal(s0, a, i)
		 * expected precondition: start <= getVarInt(s0, i) /\ getVarInt(s0, i) <= end
		 */
		String arrayName = "a";
		String type = "REAL";
		int startIndex = 1, endIndex = 10;
		String indexName = "i";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable array = ExpressionFactory.createSymbolicVariable(arrayName);
		SymbolicVariable index = ExpressionFactory.createSymbolicVariable(indexName);
		Expression indexExpr = ExpressionFactory.createVariableExpression(index);
		Expression ai = ExpressionFactory.createArrayVariableExpression(array, indexExpr);
		su.nsk.iae.post.poST.Constant startConst = ExpressionFactory.createIntConstant(startIndex);
		su.nsk.iae.post.poST.Constant endConst = ExpressionFactory.createIntConstant(endIndex);
		Expression start = ExpressionFactory.createConstantExpression(startConst);
		Expression end = ExpressionFactory.createConstantExpression(endConst);
		VarInitDeclaration arrayDecl = ProgramFactory.createArrayVarDeclaration(start, end, type, null, array);
		VarInitDeclaration iDecl = ProgramFactory.createSimpleVarDeclaration("INT", null, index);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(arrayDecl, null, ModificationType.VAR);
		globVars.addVars(iDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant arrayCode = globVars.getVariable(arrayName);
		su.nsk.iae.post.vcgenerator.Constant indexCode = globVars.getVariable(indexName);
		Term expected = getVarArrayReal(currentState, arrayCode, getVarInt(currentState, indexCode));
		Term newState = globVars.initializeVar(arrayCode, currentState);
		Term expectedPrecondition = and(
				leq(new su.nsk.iae.post.vcgenerator.Constant(startIndex), getVarInt(currentState, indexCode)),
				leq(getVarInt(currentState, indexCode), new su.nsk.iae.post.vcgenerator.Constant(endIndex)));
		Term result = ai.generateExpression(newState, globVars);
		Assert.assertEquals(currentState,  newState);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedPrecondition,  result.getPrecondition());
		Assert.assertEquals(DataType.REAL,  result.getType());
	}
	
	@Test
	public void testGenerateExpressionTimeArray() {
		/*a: ARRAY [start .. end] OF INT
		 * expression: a[i]
		 * expected result: getVarArrayInt(s0, a, i)
		 * expected precondition: start <= getVarInt(s0, i) /\ getVarInt(s0, i) <= end
		 */
		String arrayName = "a";
		String type = "TIME";
		int startIndex = 1, endIndex = 10;
		String indexName = "i";
		Term currentState = new su.nsk.iae.post.vcgenerator.Variable("s0");
		SymbolicVariable array = ExpressionFactory.createSymbolicVariable(arrayName);
		SymbolicVariable index = ExpressionFactory.createSymbolicVariable(indexName);
		Expression indexExpr = ExpressionFactory.createVariableExpression(index);
		Expression ai = ExpressionFactory.createArrayVariableExpression(array, indexExpr);
		su.nsk.iae.post.poST.Constant startConst = ExpressionFactory.createIntConstant(startIndex);
		su.nsk.iae.post.poST.Constant endConst = ExpressionFactory.createIntConstant(endIndex);
		Expression start = ExpressionFactory.createConstantExpression(startConst);
		Expression end = ExpressionFactory.createConstantExpression(endConst);
		VarInitDeclaration arrayDecl = ProgramFactory.createArrayVarDeclaration(start, end, type, null, array);
		VarInitDeclaration iDecl = ProgramFactory.createSimpleVarDeclaration("INT", null, index);
		VCGeneratorState globVars = new VCGeneratorState(1);
		globVars.addVars(arrayDecl, null, ModificationType.VAR);
		globVars.addVars(iDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant arrayCode = globVars.getVariable(arrayName);
		su.nsk.iae.post.vcgenerator.Constant indexCode = globVars.getVariable(indexName);
		Term newState = globVars.initializeVar(arrayCode, currentState);
		Term expected = getVarArrayInt(currentState, arrayCode, getVarInt(currentState, indexCode));
		Term expectedPrecondition = and(
				leq(new su.nsk.iae.post.vcgenerator.Constant(startIndex), getVarInt(currentState, indexCode)),
				leq(getVarInt(currentState, indexCode), new su.nsk.iae.post.vcgenerator.Constant(endIndex)));
		Term result = ai.generateExpression(newState, globVars);
		Assert.assertEquals(currentState,  newState);
		Assert.assertEquals(expected, result);
		Assert.assertEquals(expectedPrecondition,  result.getPrecondition());
		Assert.assertEquals(DataType.INT,  result.getType());
	}
}
