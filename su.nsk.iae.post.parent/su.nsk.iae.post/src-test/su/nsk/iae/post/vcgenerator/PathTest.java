package su.nsk.iae.post.vcgenerator;

import org.junit.Assert;
import org.junit.Test;

import su.nsk.iae.post.poST.impl.ExpressionFactory;
import su.nsk.iae.post.poST.impl.ProgramFactory;
import su.nsk.iae.post.poST.impl.StatementFactory;
import su.nsk.iae.post.poST.*;

import static su.nsk.iae.post.vcgenerator.TermFactory.*;
import static su.nsk.iae.post.vcgenerator.Constant.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

public class PathTest {
	@Test
	public void testDoAssignmentToBoolVariable() {
		/*a: BOOL
		 * statement: a := TRUE
		 * expected result: setVarBool(s0, a, True)
		 */
		String variableName = "a";
		boolean value = true;
		Term currentState = new Variable("s0");
		String type = "BOOL";
		SymbolicVariable variable = ExpressionFactory.createSymbolicVariable(variableName);
		su.nsk.iae.post.poST.Constant valueConstant = ExpressionFactory.createBooleanConstant(value);
		Expression valueExpression = ExpressionFactory.createConstantExpression(valueConstant);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDeclaration = ProgramFactory.createSimpleVarDeclaration(type, null, variable);
		vcGenVars.addVars(varDeclaration, null, ModificationType.VAR);
		Constant variableCode = vcGenVars.getVariable(variableName);
		Term expected = setVarBool(currentState, variableCode, Constant.True);
		path.doAssignment(variable, valueExpression, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testDoAssignmentToIntVariable() {
		/*a: INT
		 * statement: a := 0
		 * expected result: setVarInt(s0, a, 0)
		 */
		String variableName = "a";
		int value = 0;
		Term currentState = new Variable("s0");
		String type = "INT";
		SymbolicVariable variable = ExpressionFactory.createSymbolicVariable(variableName);
		su.nsk.iae.post.poST.Constant valueConstant = ExpressionFactory.createIntConstant(value);
		Expression valueExpression = ExpressionFactory.createConstantExpression(valueConstant);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDeclaration = ProgramFactory.createSimpleVarDeclaration(type, null, variable);
		vcGenVars.addVars(varDeclaration, null, ModificationType.VAR);
		Constant variableCode = vcGenVars.getVariable(variableName);
		Term expected = setVarInt(currentState, variableCode, new Constant(value));
		path.doAssignment(variable, valueExpression, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testDoAssignmentToRealVariable() {
		/*a: REAL
		 * statement: a := 0
		 * expected result: setVarReal(s0, a, 0)
		 */
		String variableName = "a";
		double value = 0;
		Term currentState = new Variable("s0");
		String type = "REAL";
		SymbolicVariable variable = ExpressionFactory.createSymbolicVariable(variableName);
		su.nsk.iae.post.poST.Constant valueConstant = ExpressionFactory.createRealConstant(value);
		Expression valueExpression = ExpressionFactory.createConstantExpression(valueConstant);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDeclaration = ProgramFactory.createSimpleVarDeclaration(type, null, variable);
		vcGenVars.addVars(varDeclaration, null, ModificationType.VAR);
		Constant variableCode = vcGenVars.getVariable(variableName);
		Term expected = setVarReal(currentState, variableCode, new Constant(value));
		path.doAssignment(variable, valueExpression, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testDoAssignmentToTimeVariable() {
		/*a: BOOL
		 * statement: a := T#1ms
		 * expected result: setVarInt(s0, a, 1)
		 */
		String variableName = "a";
		String value = "1ms";
		int valueInMilliseconds = 1;
		Term currentState = new Variable("s0");
		String type = "TIME";
		SymbolicVariable variable = ExpressionFactory.createSymbolicVariable(variableName);
		su.nsk.iae.post.poST.Constant valueConstant = ExpressionFactory.createTimeConstant(value);
		Expression valueExpression = ExpressionFactory.createConstantExpression(valueConstant);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDeclaration = ProgramFactory.createSimpleVarDeclaration(type, null, variable);
		vcGenVars.addVars(varDeclaration, null, ModificationType.VAR);
		Constant variableCode = vcGenVars.getVariable(variableName);
		Term expected = setVarInt(currentState, variableCode, new Constant(valueInMilliseconds));
		path.doAssignment(variable, valueExpression, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testDoAssignmentToboolArray() {
		/*a: ARRAY [start .. end] OF BOOL
		 * statement: a[i] := FALSE
		 * expected result: setVarArrayBool(currentState, a, getVarInt(currentState i), False)
		 */
		String arrayName = "a";
		String iName = "i";
		boolean value = false;
		int startIndex = 1, endIndex = 10;
		Term currentState = new Variable("s0");
		String type = "BOOL";
		SymbolicVariable array = ExpressionFactory.createSymbolicVariable(arrayName);
		SymbolicVariable i = ExpressionFactory.createSymbolicVariable(iName);
		Expression index = ExpressionFactory.createVariableExpression(i);
		su.nsk.iae.post.poST.Constant valueConstant = ExpressionFactory.createBooleanConstant(value);
		Expression valueExpression = ExpressionFactory.createConstantExpression(valueConstant);
		AssignmentStatement statement = StatementFactory.createArrayAssignmentStatement(array, index, valueExpression);
		Path path = new Path(null, currentState);
		su.nsk.iae.post.poST.Constant startConst = ExpressionFactory.createIntConstant(startIndex);
		su.nsk.iae.post.poST.Constant endConst = ExpressionFactory.createIntConstant(endIndex);
		Expression start = ExpressionFactory.createConstantExpression(startConst);
		Expression end = ExpressionFactory.createConstantExpression(endConst);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration iDeclaration = ProgramFactory.createSimpleVarDeclaration("INT", null, i);
		VarInitDeclaration arrayDeclaration = ProgramFactory.createArrayVarDeclaration(start, end, type, null, array);
		vcGenVars.addVars(arrayDeclaration, null, ModificationType.VAR);
		vcGenVars.addVars(iDeclaration, null, ModificationType.VAR);
		Constant arrayCode = vcGenVars.getVariable(arrayName);
		Constant iCode = vcGenVars.getVariable(iName);
		vcGenVars.initializeVar(arrayCode, currentState);
		Term expected = setVarArrayBool(currentState, arrayCode, getVarInt(currentState, iCode), Constant.False);
		Term expectedAssertion = and(
				leq(new Constant(startIndex), getVarInt(currentState, iCode)),
				leq(getVarInt(currentState, iCode), new Constant(endIndex)));
		path.doAssignment(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertEquals(1,  vcGenVars.getVcSet().size());
		Assert.assertEquals(expectedAssertion, vcGenVars.getVcSet().get(0));
		Assert.assertEquals(expectedAssertion, path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testDoAssignmentToIntArray() {
		/*a: ARRAY [start .. end] OF INT
		 * statement: a[i] := 0
		 * expected result: setVarArrayInt(currentState, a, getVarInt(currentState i), 0)
		 */
		String arrayName = "a";
		String iName = "i";
		int value = 0;
		int startIndex = 1, endIndex = 10;
		Term currentState = new Variable("s0");
		String type = "INT";
		SymbolicVariable array = ExpressionFactory.createSymbolicVariable(arrayName);
		SymbolicVariable i = ExpressionFactory.createSymbolicVariable(iName);
		Expression index = ExpressionFactory.createVariableExpression(i);
		su.nsk.iae.post.poST.Constant valueConstant = ExpressionFactory.createIntConstant(value);
		Expression valueExpression = ExpressionFactory.createConstantExpression(valueConstant);
		AssignmentStatement statement = StatementFactory.createArrayAssignmentStatement(array, index, valueExpression);
		Path path = new Path(null, currentState);
		su.nsk.iae.post.poST.Constant startConst = ExpressionFactory.createIntConstant(startIndex);
		su.nsk.iae.post.poST.Constant endConst = ExpressionFactory.createIntConstant(endIndex);
		Expression start = ExpressionFactory.createConstantExpression(startConst);
		Expression end = ExpressionFactory.createConstantExpression(endConst);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration iDeclaration = ProgramFactory.createSimpleVarDeclaration("INT", null, i);
		VarInitDeclaration arrayDeclaration = ProgramFactory.createArrayVarDeclaration(start, end, type, null, array);
		vcGenVars.addVars(arrayDeclaration, null, ModificationType.VAR);
		vcGenVars.addVars(iDeclaration, null, ModificationType.VAR);
		Constant arrayCode = vcGenVars.getVariable(arrayName);
		Constant iCode = vcGenVars.getVariable(iName);
		vcGenVars.initializeVar(arrayCode, currentState);
		Term expected = setVarArrayInt(currentState, arrayCode, getVarInt(currentState, iCode), new Constant(value));
		Term expectedAssertion = and(
				leq(new Constant(startIndex), getVarInt(currentState, iCode)),
				leq(getVarInt(currentState, iCode), new Constant(endIndex)));
		path.doAssignment(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertEquals(1,  vcGenVars.getVcSet().size());
		Assert.assertEquals(expectedAssertion, vcGenVars.getVcSet().get(0));
		Assert.assertEquals(expectedAssertion, path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testDoAssignmentToRealArray() {
		/*a: ARRAY [start .. end] OF REAL
		 * statement: a[i] := 0
		 * expected result: setVarArrayReal(currentState, a, getVarInt(currentState i), 0)
		 */
		String arrayName = "a";
		String iName = "i";
		double value = 0;
		int startIndex = 1, endIndex = 10;
		Term currentState = new Variable("s0");
		String type = "REAL";
		SymbolicVariable array = ExpressionFactory.createSymbolicVariable(arrayName);
		SymbolicVariable i = ExpressionFactory.createSymbolicVariable(iName);
		Expression index = ExpressionFactory.createVariableExpression(i);
		su.nsk.iae.post.poST.Constant valueConstant = ExpressionFactory.createRealConstant(value);
		Expression valueExpression = ExpressionFactory.createConstantExpression(valueConstant);
		AssignmentStatement statement = StatementFactory.createArrayAssignmentStatement(array, index, valueExpression);
		Path path = new Path(null, currentState);
		su.nsk.iae.post.poST.Constant startConst = ExpressionFactory.createIntConstant(startIndex);
		su.nsk.iae.post.poST.Constant endConst = ExpressionFactory.createIntConstant(endIndex);
		Expression start = ExpressionFactory.createConstantExpression(startConst);
		Expression end = ExpressionFactory.createConstantExpression(endConst);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration iDeclaration = ProgramFactory.createSimpleVarDeclaration("INT", null, i);
		VarInitDeclaration arrayDeclaration = ProgramFactory.createArrayVarDeclaration(start, end, type, null, array);
		vcGenVars.addVars(arrayDeclaration, null, ModificationType.VAR);
		vcGenVars.addVars(iDeclaration, null, ModificationType.VAR);
		Constant arrayCode = vcGenVars.getVariable(arrayName);
		Constant iCode = vcGenVars.getVariable(iName);
		vcGenVars.initializeVar(arrayCode, currentState);
		Term expected = setVarArrayReal(currentState, arrayCode, getVarInt(currentState, iCode), new Constant(value));
		Term expectedAssertion = and(
				leq(new Constant(startIndex), getVarInt(currentState, iCode)),
				leq(getVarInt(currentState, iCode), new Constant(endIndex)));
		path.doAssignment(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertEquals(1,  vcGenVars.getVcSet().size());
		Assert.assertEquals(expectedAssertion, vcGenVars.getVcSet().get(0));
		Assert.assertEquals(expectedAssertion, path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testDoAssignmentToTimeArray() {
		/*a: ARRAY [start .. end] OF BOOL
		 * statement: a[i] := T#1s
		 * expected result: setVarArrayInt(currentState, a, getVarInt(currentState i), 1 * 1000)
		 */
		String arrayName = "a";
		String iName = "i";
		String value = "1s";
		int valueInMilliseconds = 1000;
		int startIndex = 1, endIndex = 10;
		Term currentState = new Variable("s0");
		String type = "TIME";
		SymbolicVariable array = ExpressionFactory.createSymbolicVariable(arrayName);
		SymbolicVariable i = ExpressionFactory.createSymbolicVariable(iName);
		Expression index = ExpressionFactory.createVariableExpression(i);
		su.nsk.iae.post.poST.Constant valueConstant = ExpressionFactory.createTimeConstant(value);
		Expression valueExpression = ExpressionFactory.createConstantExpression(valueConstant);
		AssignmentStatement statement = StatementFactory.createArrayAssignmentStatement(array, index, valueExpression);
		Path path = new Path(null, currentState);
		su.nsk.iae.post.poST.Constant startConst = ExpressionFactory.createIntConstant(startIndex);
		su.nsk.iae.post.poST.Constant endConst = ExpressionFactory.createIntConstant(endIndex);
		Expression start = ExpressionFactory.createConstantExpression(startConst);
		Expression end = ExpressionFactory.createConstantExpression(endConst);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration iDeclaration = ProgramFactory.createSimpleVarDeclaration("INT", null, i);
		VarInitDeclaration arrayDeclaration = ProgramFactory.createArrayVarDeclaration(start, end, type, null, array);
		vcGenVars.addVars(arrayDeclaration, null, ModificationType.VAR);
		vcGenVars.addVars(iDeclaration, null, ModificationType.VAR);
		Constant arrayCode = vcGenVars.getVariable(arrayName);
		Constant iCode = vcGenVars.getVariable(iName);
		vcGenVars.initializeVar(arrayCode, currentState);
		Term expected = setVarArrayInt(currentState, arrayCode, getVarInt(currentState, iCode), new Constant(valueInMilliseconds));
		Term expectedAssertion = and(
				leq(new Constant(startIndex), getVarInt(currentState, iCode)),
				leq(getVarInt(currentState, iCode), new Constant(endIndex)));
		path.doAssignment(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertEquals(1,  vcGenVars.getVcSet().size());
		Assert.assertEquals(expectedAssertion, vcGenVars.getVcSet().get(0));
		Assert.assertEquals(expectedAssertion, path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testDoAssignmentAfterExit() {
		String variableName = "a";
		int value = 0;
		Term currentState = new Variable("s0");
		String type = "INT";
		SymbolicVariable variable = ExpressionFactory.createSymbolicVariable(variableName);
		su.nsk.iae.post.poST.Constant valueConstant = ExpressionFactory.createIntConstant(value);
		Expression valueExpression = ExpressionFactory.createConstantExpression(valueConstant);
		AssignmentStatement statement = StatementFactory.createVariableAssignmentStatement(variable, valueExpression);
		Path path = new Path(null, currentState);
		path.doExit();
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDeclaration = ProgramFactory.createSimpleVarDeclaration(type, null, variable);
		vcGenVars.addVars(varDeclaration, null, ModificationType.VAR);
		Term expected = currentState;
		path.doAssignment(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.EXIT,  path.getStatus());
	}
	
	@Test
	public void testSetStateSpecifiedStete() {
		/*current process: process1
		 * statement: SET STATE state1
		 * expected result: setPstate(s0, process1, state1)
		 */
		String stateName = "state1";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(stateName, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		SetStateStatement statement = StatementFactory.createSetStateStatement(state1);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(stateName);
		vcGenVars.setCurrentProcess(processName);
		Term expected = setPstate(currentState, processCode, stateCode);
		path.setState(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testSetStateNext() {
		/*PROCESS process1
		 * STATE state1
		 * STATE state2
		 * current state: state1
		 * statement: SET NEXT
		 * expected result: setPstate(s0, process1, state2)
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		SetStateStatement statement = StatementFactory.createSetNextStateStatement();
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state2Name);
		vcGenVars.setCurrentProcess(processName);
		vcGenVars.setCurrentProcessState(0);
		Term expected = setPstate(currentState, processCode, stateCode);
		path.setState(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testSetStateAfterExit() {
		/*current process: process1
		 * statement: SET STATE state1
		 * expected result: setPstate(s0, process1, state1)
		 */
		String stateName = "state1";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(stateName, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		SetStateStatement statement = StatementFactory.createSetStateStatement(state1);
		Path path = new Path(null, currentState);
		path.doExit();
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(stateName);
		vcGenVars.setCurrentProcess(processName);
		Term expected = currentState;
		path.setState(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.EXIT,  path.getStatus());
	}
	
	@Test
	public void testResetTimerNormal() {
		/*current process: process1
		 * statement: RESET TIMER
		 * expected result: reset(s0, process1)
		 */
		String stateName = "state1";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(stateName, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		ResetTimerStatement statement = StatementFactory.createResetTimerStatement();
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess(processName);
		Term expected = reset(currentState, processCode);
		path.resetTimer(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testResetTimerAfterExit() {
		/*current process: process1
		 * statement: EXIT; RESET TIMER
		 * expected result: s0
		 */
		String stateName = "state1";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(stateName, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		ResetTimerStatement statement = StatementFactory.createResetTimerStatement();
		Path path = new Path(null, currentState);
		path.doExit();
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess(processName);
		Term expected = currentState;
		path.resetTimer(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.EXIT,  path.getStatus());
	}
	
	@Test
	public void testStartProcessSpecifiedProcess() {
		/*PROCESS process1
		 * STATE state1
		 * ...
		 * statement: START PROCESS process1
		 * expected result: setPstate(s0, process1 state1)
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		StartProcessStatement statement = StatementFactory.createStartProcessStatement(process);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		Term expected = setPstate(currentState, processCode, stateCode);
		path.startProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testStartProcessWithVariableInitialization() {
		/*PROCESS process1
		 * VAR
		 * var1: BOOL := TRUE;
		 * STATE state1
		 * ...
		 * statement: START PROCESS process1
		 * expected result: setPstate(s0, process1 state1)
		 */
		String var1Name = "var1";
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		SymbolicVariable var1Var = ExpressionFactory.createSymbolicVariable(var1Name);
		su.nsk.iae.post.poST.Constant valueConst = ExpressionFactory.createBooleanConstant(true);
		Expression value = ExpressionFactory.createConstantExpression(valueConst);
		VarInitDeclaration varInitDecl = ProgramFactory.createSimpleVarDeclaration("BOOL", value, var1Var);
		VarDeclaration varDecl = ProgramFactory.createVarDeclaration(false, Arrays.asList(varInitDecl));
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		vars.add(varDecl);
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		StartProcessStatement statement = StatementFactory.createStartProcessStatement(process);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		Constant var1 = vcGenVars.getVariable(var1Name);
		Term expected = setPstate(setVarBool(currentState, var1, True), processCode, stateCode);
		path.startProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	
	@Test
	public void testStartProcessRestart() {
		/*PROCESS process1
		 * STATE state1
		 * ...
		 * current process: process1
		 * statement: RESTART
		 * expected result: setPstate(s0, process1 state1)
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		StartProcessStatement statement = StatementFactory.createStartProcessStatement(null);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		vcGenVars.setCurrentProcess(processName);
		Term expected = setPstate(currentState, processCode, stateCode);
		path.startProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testStartProcessAfterExit() {
		/*PROCESS process1
		 * STATE state1
		 * ...
		 * current process: process1
		 * statement: EXIT; RESTART
		 * expected result: s0
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		StartProcessStatement statement = StatementFactory.createStartProcessStatement(null);
		Path path = new Path(null, currentState);
		path.doExit();
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		vcGenVars.setCurrentProcess(processName);
		Term expected = currentState;
		path.startProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.EXIT,  path.getStatus());
	}
	
	@Test
	public void testStopProcessSpecifiedProcess() {
		/*PROCESS process1
		 * STATE state1
		 * ...
		 * statement: STOP PROCESS process1
		 * expected result: setPstate(s0, process1 stop)
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		StopProcessStatement statement = StatementFactory.createStopProcessStatement(process);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		Term expected = setPstate(currentState, processCode, Constant.stop);
		path.stopProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testStopProcessCurrent() {
		/*PROCESS process1
		 * STATE state1
		 * ...
		 * current process: process1
		 * statement: STOP
		 * expected result: setPstate(s0, process1 stop)
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		StopProcessStatement statement = StatementFactory.createStopProcessStatement(null);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		vcGenVars.setCurrentProcess(processName);
		Term expected = setPstate(currentState, processCode, Constant.stop);
		path.stopProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testStopProcessAfterExit() {
		/*PROCESS process1
		 * STATE state1
		 * ...
		 * current process: process1
		 * statement: EXIT; STOP
		 * expected result: s0
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		StopProcessStatement statement = StatementFactory.createStopProcessStatement(null);
		Path path = new Path(null, currentState);
		path.doExit();
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		vcGenVars.setCurrentProcess(processName);
		Term expected = currentState;
		path.stopProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.EXIT,  path.getStatus());
	}
	
	@Test
	public void testErrorProcessSpecifiedProcess() {
		/*PROCESS process1
		 * STATE state1
		 * ...
		 * statement: ERROR PROCESS process1
		 * expected result: setPstate(s0, process1 error)
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		ErrorProcessStatement statement = StatementFactory.createErrorProcessStatement(process);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		Term expected = setPstate(currentState, processCode, Constant.error);
		path.errorProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testErrorProcessCurrent() {
		/*PROCESS process1
		 * STATE state1
		 * ...
		 * current process: process1
		 * statement: ERROR
		 * expected result: setPstate(s0, process1, error)
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		ErrorProcessStatement statement = StatementFactory.createErrorProcessStatement(null);
		Path path = new Path(null, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		vcGenVars.setCurrentProcess(processName);
		Term expected = setPstate(currentState, processCode, Constant.error);
		path.errorProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.NORMAL,  path.getStatus());
	}
	
	@Test
	public void testErrorProcessAfterExit() {
		/*PROCESS process1
		 * STATE state1
		 * ...
		 * current process: process1
		 * statement: EXIT; ERROR
		 * expected result: s0
		 */
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term currentState = new Variable("s0");
		State state1 = ProgramFactory.createState(state1Name, null, null);
		State state2 = ProgramFactory.createState(state2Name, null, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		ErrorProcessStatement statement = StatementFactory.createErrorProcessStatement(null);
		Path path = new Path(null, currentState);
		path.doExit();
		VCGeneratorState vcGenVars = new VCGeneratorState();
		Constant processCode = vcGenVars.addProcess(process);
		Constant stateCode = vcGenVars.getState(state1Name);
		vcGenVars.setCurrentProcess(processName);
		Term expected = currentState;
		path.errorProcess(statement, vcGenVars);
		Assert.assertEquals(expected, path.getCurrentState());
		Assert.assertNull(path.getPrecondition());
		Assert.assertEquals(ExecutionStatus.EXIT,  path.getStatus());
	}
	
	@Test
	public void testAddConditionNullAddedCondition() {
		Term precondition = new Variable("a");
		Term addedCondition = null;
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		path = path.addCondition(addedCondition);
		Assert.assertEquals(precondition, path.getPrecondition());
		Assert.assertEquals(currentState, path.getCurrentState());
		Assert.assertEquals(ExecutionStatus.NORMAL, path.getStatus());
	}
	
	@Test
	public void testAddConditionNullPrecondition() {
		Term precondition = null;
		Term addedCondition = new Variable("a");
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		Path branch = path.addCondition(addedCondition);
		Assert.assertNotSame(path,  branch);;
		Assert.assertEquals(addedCondition, branch.getPrecondition());
		Assert.assertEquals(currentState, branch.getCurrentState());
		Assert.assertEquals(ExecutionStatus.NORMAL, branch.getStatus());
	}
	
	@Test
	public void testAddConditionPreconditionAndAddedConditionNotNull() {
		Term precondition = new Variable("a");
		Term addedCondition = new Variable("b");
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		Term expected = and(precondition, addedCondition);
		Path branch = path.addCondition(addedCondition);
		Assert.assertNotSame(path,  branch);;
		Assert.assertEquals(expected, branch.getPrecondition());
		Assert.assertEquals(currentState, branch.getCurrentState());
		Assert.assertEquals(ExecutionStatus.NORMAL, branch.getStatus());
	}
	
	@Test
	public void testGenerateVerificationConditionNotNullPrecondition() {
		Term precondition = new Variable("a");
		Term postcondition = new Variable("b");
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		Term expected = impl(precondition, postcondition);
		Term result = path.generateVerificationCondition(postcondition);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateVerificationConditionNullPrecondition() {
		Term precondition = null;
		Term postcondition = new Variable("b");
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		Term expected = postcondition;
		Term result = path.generateVerificationCondition(postcondition);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateVerificationConditionLoopinv() {
		Term precondition = new Variable("a");
		FunctionSymbol loopinv = new FunctionSymbol("inv", true);
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		Term expected = impl(precondition, new ComplexTerm(loopinv, currentState));
		Term result = path.generateVerificationCondition(loopinv);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testAssertionNullAssertion() {
		Term assertion = null;
		Term precondition = new Variable("b");
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		path.assertion(assertion, vcGenVars);
		Assert.assertEquals(precondition, path.getPrecondition());
		Assert.assertTrue(vcGenVars.getVcSet().isEmpty());
	}
	
	@Test
	public void testAssertionAfterExit() {
		Term assertion = new Variable("a");
		Term precondition = new Variable("b");
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		path.doExit();
		path.assertion(assertion, vcGenVars);
		Assert.assertEquals(precondition, path.getPrecondition());
		Assert.assertTrue(vcGenVars.getVcSet().isEmpty());
	}
	
	@Test
	public void testAssertionNullPrecondition() {
		Term assertion = new Variable("a");
		Term precondition = null;
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		path.assertion(assertion, vcGenVars);
		Assert.assertEquals(assertion, path.getPrecondition());
		Assert.assertEquals(1, vcGenVars.getVcSet().size());
		Assert.assertEquals(assertion, vcGenVars.getVcSet().get(0));
	}
	
	@Test
	public void testAssertionNotNullPrecondition() {
		Term assertion = new Variable("a");
		Term precondition = new Variable("b");
		Term currentState = new Variable("s0");
		Path path = new Path(precondition, currentState);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		path.assertion(assertion, vcGenVars);
		Term expectedPrecondition = and(precondition, assertion);
		Term expectedVC = impl(precondition, assertion);
		Assert.assertEquals(expectedPrecondition, path.getPrecondition());
		Assert.assertEquals(1, vcGenVars.getVcSet().size());
		Assert.assertEquals(expectedVC, vcGenVars.getVcSet().get(0));
	}
}
