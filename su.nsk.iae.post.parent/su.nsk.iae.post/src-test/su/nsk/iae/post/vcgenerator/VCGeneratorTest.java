package su.nsk.iae.post.vcgenerator;

import org.junit.Test;

import com.google.inject.Injector;
import com.google.inject.Provider;

import su.nsk.iae.post.poST.impl.ExpressionFactory;
import su.nsk.iae.post.poST.impl.ProgramFactory;
import su.nsk.iae.post.poST.impl.StatementFactory;
import su.nsk.iae.post.PoSTStandaloneSetup;
import su.nsk.iae.post.poST.*;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;
import static su.nsk.iae.post.vcgenerator.Constant.*;

import java.util.ArrayList;
import java.util.List;

import org.junit.Assert;
import org.eclipse.xtext.testing.util.ParseHelper;

public class VCGeneratorTest {
	Injector injector = new PoSTStandaloneSetup().createInjectorAndDoEMFRegistration();
	ParseHelper<Model> parser = (ParseHelper) ((Provider) injector.getProvider(ParseHelper.class)).get();
	
	@Test
	public void testGenerateTimeoutTimeLiteral() {
		/*current process: process1
		 * statement: TIMEOUT T#1m THEN SET STATE state1; END_TIMEOUT
		 * expected result: [{1m <= ltime(s0 process1), setPstate(s0, process1, state1)}, {not(1m <= ltime(s0, process1)), s0]
		 */
		String timeValue = "1m";
		int timeInMilliseconds = 1000 * 60;
		int period = 100;
		Term s0 = new Variable("s0");
		su.nsk.iae.post.poST.Constant timeoutConst = ExpressionFactory.createTimeConstant(timeValue);
		String stateName = "state1";
		String processName = "process1";
		State state = ProgramFactory.createState(stateName, null, null);
		Statement timeoutBodyStatement = StatementFactory.createSetStateStatement(state);
		List<Statement> timeoutBody = new ArrayList<>();
		timeoutBody.add(timeoutBodyStatement);
		TimeoutStatement timeout = StatementFactory.createConstTimeout(timeoutConst, timeoutBody);
		Path path = new Path(null, s0);
		VCGeneratorState vcGenVars = new VCGeneratorState(period);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess(processName);
		su.nsk.iae.post.vcgenerator.Constant stateCode = vcGenVars.getState(stateName);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		List<Path> expected = new ArrayList<>();
		su.nsk.iae.post.vcgenerator.Constant time = new su.nsk.iae.post.vcgenerator.Constant(timeInMilliseconds / period);
		expected.add(new Path(leq(time, ltime(s0, procCode)), setPstate(s0, procCode, stateCode)));
		expected.add(new Path(not(leq(time, ltime(s0, procCode))), s0));
		List<Path> result = vcGen.generateTimeout(path, timeout);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateTimeoutConst() {
		/*VAR CONSTANT
		 * t : TIME := T#1h;
		 * END_VAR
		 * current process: process1
		 * statement: TIMEOUT t THEN SET STATE state1; END_TIMEOUT
		 * expected result: [{1h <= ltime(s0 process1), setPstate(s0, process1, state1)}, {not(1h <= ltime(s0, process1)), s0]
		 */
		String timeValue = "1h";
		int timeInMilliseconds = 1000 * 60 * 60;
		int period = 100;
		Term s0 = new Variable("s0");
		su.nsk.iae.post.poST.Constant timeoutConst = ExpressionFactory.createTimeConstant(timeValue);
		String tName = "T";
		SymbolicVariable t = ExpressionFactory.createSymbolicVariable(tName);
		Expression timeValueExpr = ExpressionFactory.createConstantExpression(timeoutConst);
		String stateName = "state1";
		String processName = "process1";
		State state = ProgramFactory.createState(stateName, null, null);
		Statement timeoutBodyStatement = StatementFactory.createSetStateStatement(state);
		List<Statement> timeoutBody = new ArrayList<>();
		timeoutBody.add(timeoutBodyStatement);
		TimeoutStatement timeout = StatementFactory.createVariableTimeout(t, timeoutBody);
		Path path = new Path(null, s0);
		VCGeneratorState vcGenVars = new VCGeneratorState(period);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration("TIME", timeValueExpr, t);
		vcGenVars.addVars(varDecl, null, ModificationType.CONSTANT);
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess(processName);
		su.nsk.iae.post.vcgenerator.Constant stateCode = vcGenVars.getState(stateName);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		List<Path> expected = new ArrayList<>();
		su.nsk.iae.post.vcgenerator.Constant time = new su.nsk.iae.post.vcgenerator.Constant(timeInMilliseconds / period);
		expected.add(new Path(leq(time, ltime(s0, procCode)), setPstate(s0, procCode, stateCode)));
		expected.add(new Path(not(leq(time, ltime(s0, procCode))), s0));
		List<Path> result = vcGen.generateTimeout(path, timeout);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateTimeoutVariable() {
		/*VAR
		 * t: TIME;
		 * END_VAR
		 * current process: process1
		 * statement: TIMEOUT t THEN SET STATE state1; END_TIMEOUT
		 * expected result: [{(getVarInt(s0, t) - 1) / period + 1 <= ltime(s0, process1), setPstate(s0, process1, state1)},
		 * {not((getVarInt(s0, t) - 1) / period + 1 <= ltime(s0, process1)), s0}]
		 */
		int period = 100;
		su.nsk.iae.post.vcgenerator.Constant periodConst = new su.nsk.iae.post.vcgenerator.Constant(period);
		Term s0 = new Variable("s0");
		String tName = "T";
		SymbolicVariable t = ExpressionFactory.createSymbolicVariable(tName);
		String stateName = "state1";
		String processName = "process1";
		State state = ProgramFactory.createState(stateName, null, null);
		Statement timeoutBodyStatement = StatementFactory.createSetStateStatement(state);
		List<Statement> timeoutBody = new ArrayList<>();
		timeoutBody.add(timeoutBodyStatement);
		TimeoutStatement timeout = StatementFactory.createVariableTimeout(t, timeoutBody);
		Path path = new Path(null, s0);
		VCGeneratorState vcGenVars = new VCGeneratorState(period);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration("TIME", null, t);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess(processName);
		su.nsk.iae.post.vcgenerator.Constant stateCode = vcGenVars.getState(stateName);
		su.nsk.iae.post.vcgenerator.Constant tCode = vcGenVars.getVariable(tName);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		su.nsk.iae.post.vcgenerator.Constant _1 = new su.nsk.iae.post.vcgenerator.Constant(1);
		Term time = plus(div(minus(getVarInt(s0, tCode), _1), periodConst), _1);
		List<Path> expected = new ArrayList<>();
		expected.add(new Path(leq(time, ltime(s0, procCode)), setPstate(s0, procCode, stateCode)));
		expected.add(new Path(not(leq(time, ltime(s0, procCode))), s0));
		List<Path> result = vcGen.generateTimeout(path, timeout);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateTimeoutAfterReturn() {
		/*statement: EXIT; TIMEOUT 1m THEN SET STATE state1; END_STATE
		 * expected result: [{null, s0}]
		 */
		String timeValue = "1m";
		int period = 100;
		Term s0 = new Variable("s0");
		su.nsk.iae.post.poST.Constant timeoutConst = ExpressionFactory.createTimeConstant(timeValue);
		String stateName = "state1";
		String processName = "process1";
		State state = ProgramFactory.createState(stateName, null, null);
		Statement timeoutBodyStatement = StatementFactory.createSetStateStatement(state);
		List<Statement> timeoutBody = new ArrayList<>();
		timeoutBody.add(timeoutBodyStatement);
		TimeoutStatement timeout = StatementFactory.createConstTimeout(timeoutConst, timeoutBody);
		Path path = new Path(null, s0);
		path.doReturn();
		VCGeneratorState vcGenVars = new VCGeneratorState(period);
		List<State> states = new ArrayList<>();
		states.add(state);
		vcGenVars.setCurrentProcess(processName);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		List<Path> expected = new ArrayList<>();
		expected.add(path);
		List<Path> result = vcGen.generateTimeout(path, timeout);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateTimeoutEmptyBody() {
		/*current process: process1
		 * statement: TIMEOUT T#1m THEN END_TIMEOUT
		 * expected result: [{1m <= ltime(s0 process1), s0}, {not(1m <= ltime(s0, process1)), s0]
		 */		
		String timeValue = "1d";
		int timeInMilliseconds = 1000 * 60 * 60 * 24;
		int period = 100;
		Term s0 = new Variable("s0");
		su.nsk.iae.post.poST.Constant timeoutConst = ExpressionFactory.createTimeConstant(timeValue);
		String stateName = "state1";
		String processName = "process1";
		State state = ProgramFactory.createState(stateName, null, null);
		Statement timeoutBodyStatement = StatementFactory.createSetStateStatement(state);
		List<Statement> timeoutBody = new ArrayList<>();
		timeoutBody.add(timeoutBodyStatement);
		TimeoutStatement timeout = StatementFactory.createConstTimeout(timeoutConst, null);
		Path path = new Path(null, s0);
		VCGeneratorState vcGenVars = new VCGeneratorState(period);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess(processName);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		List<Path> expected = new ArrayList<>();
		su.nsk.iae.post.vcgenerator.Constant time = new su.nsk.iae.post.vcgenerator.Constant(timeInMilliseconds / period);
		expected.add(new Path(leq(time, ltime(s0, procCode)), s0));
		expected.add(new Path(not(leq(time, ltime(s0, procCode))), s0));
		List<Path> result = vcGen.generateTimeout(path, timeout);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateStateOnlyTimeout() {
		/*current process: process1
		 * STATE state1
		 * TIMEOUT T#1s1ms THEN SET STATE state1; ENDTIMEOUT
		 * END_STATE
		 * expected result: [{getPstate(s0, process1) = state1 /\ 1s1ms <= ltime(s0 process1), setPstate(s0, process1, state1)},
		 *  {getPstate(s0, process1) = state1 /\ not(1m <= ltime(s0, process1)), s0]
		 */
		String timeValue = "1s1ms";
		int timeInMilliseconds = 1001;
		int period = 100;
		Term s0 = new Variable("s0");
		su.nsk.iae.post.poST.Constant timeoutConst = ExpressionFactory.createTimeConstant(timeValue);
		String stateName = "state1";
		String processName = "process1";
		State state = ProgramFactory.createState(stateName, null, null);
		Statement timeoutBodyStatement = StatementFactory.createSetStateStatement(state);
		List<Statement> timeoutBody = new ArrayList<>();
		timeoutBody.add(timeoutBodyStatement);
		TimeoutStatement timeout = StatementFactory.createConstTimeout(timeoutConst, timeoutBody);
		state.setTimeout(timeout);
		Path path = new Path(null, s0);
		VCGeneratorState vcGenVars = new VCGeneratorState(period);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess(processName);
		su.nsk.iae.post.vcgenerator.Constant stateCode = vcGenVars.getState(stateName);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		vcGenVars.currentProcessState= states.indexOf(state);
		List<Path> expected = new ArrayList<>();
		int timeInCycles = timeInMilliseconds % period == 0 ? timeInMilliseconds / period : timeInMilliseconds / period + 1;
		su.nsk.iae.post.vcgenerator.Constant time = new su.nsk.iae.post.vcgenerator.Constant(timeInCycles);
		expected.add(new Path(and(eq(getPstate(s0, procCode), stateCode), leq(time, ltime(s0, procCode))), setPstate(s0, procCode, stateCode)));
		expected.add(new Path(and(eq(getPstate(s0, procCode), stateCode), not(leq(time, ltime(s0, procCode)))), s0));
		List<Path> result = vcGen.generateState(path, state);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateStateWithoutTimeout() {
		/*current process: process1
		 * STATE state2
		 *  SET STATE state1;
		 * END_STATE
		 * expected result: [{getPstate(s0, process1) = state2, setPstate(s0, process1, state1)}]
		 */
		String timeValue = "1s1ms";
		int timeInMilliseconds = 1001;
		int period = 100;
		Term s0 = new Variable("s0");
		su.nsk.iae.post.poST.Constant timeoutConst = ExpressionFactory.createTimeConstant(timeValue);
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		State state1 = ProgramFactory.createState(state1Name, null, null);
		Statement stateBodyStatement = StatementFactory.createSetStateStatement(state1);
		List<Statement> stateBody = new ArrayList<>();
		stateBody.add(stateBodyStatement);
		State state2 = ProgramFactory.createState(state2Name, stateBody, null);
		Path path = new Path(null, s0);
		VCGeneratorState vcGenVars = new VCGeneratorState(period);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess(processName);
		su.nsk.iae.post.vcgenerator.Constant state1Code = vcGenVars.getState(state1Name);
		su.nsk.iae.post.vcgenerator.Constant state2Code = vcGenVars.getState(state2Name);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		vcGenVars.currentProcessState= states.indexOf(state2);
		List<Path> expected = new ArrayList<>();
		expected.add(new Path(eq(getPstate(s0, procCode), state2Code), setPstate(s0, procCode, state1Code)));
		List<Path> result = vcGen.generateState(path, state2);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateStateStatementAndTimeout() {
		/*current process: process1
		 * STATE state2
		 *  SET STATE state1;
		 *  TIMEOUT T#1m1ms THEN END_TIMEOUT
		 * END_STATE
		 * expected result: [{getPstate(s0, process1) = state2 /\ ltime(setPstate(s0, process1, state1) <= 1m1ms, process1),
		 *  setPstate(s0, process1, state1)},
		 *  {getPstate(s0, process1) = state2 /\ not(ltime(setPstate(s0, process1, state1), process1) <= 1m1ms),
		 *  setPstate(s0, process1, state1)}]
		 */
		String timeValue = "1m1ms";
		int timeInMilliseconds = 1000 * 60 + 1;
		int period = 100;
		Term s0 = new Variable("s0");
		su.nsk.iae.post.poST.Constant timeoutConst = ExpressionFactory.createTimeConstant(timeValue);
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		State state1 = ProgramFactory.createState(state1Name, null, null);
		Statement stateBodyStatement = StatementFactory.createSetStateStatement(state1);
		List<Statement> stateBody = new ArrayList<>();
		stateBody.add(stateBodyStatement);
		TimeoutStatement timeout = StatementFactory.createConstTimeout(timeoutConst, null);
		State state2 = ProgramFactory.createState(state2Name, stateBody, timeout);
		Path path = new Path(null, s0);
		VCGeneratorState vcGenVars = new VCGeneratorState(period);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		vcGenVars.setCurrentProcess(processName);
		su.nsk.iae.post.vcgenerator.Constant state1Code = vcGenVars.getState(state1Name);
		su.nsk.iae.post.vcgenerator.Constant state2Code = vcGenVars.getState(state2Name);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		vcGenVars.currentProcessState= states.indexOf(state2);
		Term stateAfterStateBody = setPstate(s0, procCode, state1Code);
		int timeInCycles = timeInMilliseconds % period == 0 ? timeInMilliseconds / period : timeInMilliseconds / period + 1;
		su.nsk.iae.post.vcgenerator.Constant time = new su.nsk.iae.post.vcgenerator.Constant(timeInCycles);
		List<Path> expected = new ArrayList<>();
		expected.add(new Path(and(eq(getPstate(s0, procCode), state2Code), leq(time, ltime(stateAfterStateBody, procCode))), stateAfterStateBody));
		expected.add(new Path(and(eq(getPstate(s0, procCode), state2Code), not(leq(time, ltime(stateAfterStateBody, procCode)))), stateAfterStateBody));
		List<Path> result = vcGen.generateState(path, state2);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateStateAfterReturn() {
		/*current process: process1
		 * STATE state1
		 * TIMEOUT T#1s1ms THEN SET STATE state1; ENDTIMEOUT
		 * END_STATE
		 * expected result: [{getPstate(s0, process1) = state1 /\ 1s1ms <= ltime(s0 process1), setPstate(s0, process1, state1)},
		 *  {getPstate(s0, process1) = state1 /\ not(1m <= ltime(s0, process1)), s0]
		 */
		String timeValue = "1s1ms";
		int period = 100;
		Term s0 = new Variable("s0");
		su.nsk.iae.post.poST.Constant timeoutConst = ExpressionFactory.createTimeConstant(timeValue);
		String stateName = "state1";
		String processName = "process1";
		State state = ProgramFactory.createState(stateName, null, null);
		Statement timeoutBodyStatement = StatementFactory.createSetStateStatement(state);
		List<Statement> timeoutBody = new ArrayList<>();
		timeoutBody.add(timeoutBodyStatement);
		TimeoutStatement timeout = StatementFactory.createConstTimeout(timeoutConst, timeoutBody);
		state.setTimeout(timeout);
		Path path = new Path(null, s0);
		path.doReturn();
		VCGeneratorState vcGenVars = new VCGeneratorState(period);
		List<State> states = new ArrayList<>();
		states.add(state);
		vcGenVars.setCurrentProcess(processName);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		vcGenVars.currentProcessState= states.indexOf(state);
		List<Path> expected = new ArrayList<>();
		expected.add(path);
		List<Path> result = vcGen.generateState(path, state);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateProcessNormal() {
		/*
		 * a: BOOL
		 * PROCESS process1
		 * STATE state1
		 * a := TRUE;
		 * END_STATE
		 * STATE state2
		 * a := FALSE;
		 * END_STATE
		 * END_PROCESS
		 * expected result:
		 * [{getPstate(s0, process1) = state1, setVarBool(s0, a, True)},
		 *  {getPstate(s0, process1) = state2, setVarBool(s0, a, False)},
		 *  {getPstate(s0, process1) = stop, s0},
		 *  {getPstate(s0, process1) = error, s0}]
		 */
		String aName = "a";
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term s0 = new Variable("s0");
		SymbolicVariable a = ExpressionFactory.createSymbolicVariable(aName);
		su.nsk.iae.post.poST.Constant constTrue = ExpressionFactory.createBooleanConstant(true);
		su.nsk.iae.post.poST.Constant constFalse = ExpressionFactory.createBooleanConstant(false);
		Expression trueExpr = ExpressionFactory.createConstantExpression(constTrue);
		Expression falseExpr = ExpressionFactory.createConstantExpression(constFalse);
		Statement statement1 = StatementFactory.createVariableAssignmentStatement(a, trueExpr);
		Statement statement2 = StatementFactory.createVariableAssignmentStatement(a, falseExpr);
		List<Statement> stateBody1 = new ArrayList<>();
		stateBody1.add(statement1);
		List<Statement> stateBody2 = new ArrayList<>();
		stateBody2.add(statement2);
		State state1 = ProgramFactory.createState(state1Name, stateBody1, null);
		State state2 = ProgramFactory.createState(state2Name, stateBody2, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		Path path = new Path(null, s0);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration("BOOL", null, a);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		su.nsk.iae.post.vcgenerator.Constant procCode = vcGenVars.addProcess(process);
		su.nsk.iae.post.vcgenerator.Constant aCode = vcGenVars.getVariable(aName);
		vcGenVars.setCurrentProcess(processName);
		su.nsk.iae.post.vcgenerator.Constant state1Code = vcGenVars.getState(state1Name);
		su.nsk.iae.post.vcgenerator.Constant state2Code = vcGenVars.getState(state2Name);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		List<Path> expected = new ArrayList<>();
		expected.add(new Path(eq(getPstate(s0, procCode), state1Code), setVarBool(s0, aCode, True)));
		expected.add(new Path(eq(getPstate(s0, procCode), state2Code), setVarBool(s0, aCode, False)));
		expected.add(new Path(eq(getPstate(s0, procCode), stop), s0));
		expected.add(new Path(eq(getPstate(s0, procCode), error), s0));
		List<Path> result = vcGen.generateProcess(path, process);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateProcessAfterReturn() {
		/*
		 * a: BOOL
		 * PROCESS process1
		 * STATE state1
		 * a := TRUE;
		 * END_STATE
		 * STATE state2
		 * a := FALSE;
		 * END_STATE
		 * END_PROCESS
		 * expected result:
		 * [{getPstate(s0, process1) = state1, setVarBool(s0, a, True)},
		 *  {getPstate(s0, process1) = state2, setVarBool(s0, a, False)},
		 *  {getPstate(s0, process1) = stop, s0},
		 *  {getPstate(s0, process1) = error, s0}]
		 */
		String aName = "a";
		String state1Name = "state1";
		String state2Name = "state2";
		String processName = "process1";
		Term s0 = new Variable("s0");
		SymbolicVariable a = ExpressionFactory.createSymbolicVariable(aName);
		su.nsk.iae.post.poST.Constant constTrue = ExpressionFactory.createBooleanConstant(true);
		su.nsk.iae.post.poST.Constant constFalse = ExpressionFactory.createBooleanConstant(false);
		Expression trueExpr = ExpressionFactory.createConstantExpression(constTrue);
		Expression falseExpr = ExpressionFactory.createConstantExpression(constFalse);
		Statement statement1 = StatementFactory.createVariableAssignmentStatement(a, trueExpr);
		Statement statement2 = StatementFactory.createVariableAssignmentStatement(a, falseExpr);
		List<Statement> stateBody1 = new ArrayList<>();
		stateBody1.add(statement1);
		List<Statement> stateBody2 = new ArrayList<>();
		stateBody2.add(statement2);
		State state1 = ProgramFactory.createState(state1Name, stateBody1, null);
		State state2 = ProgramFactory.createState(state2Name, stateBody2, null);
		List<InputVarDeclaration> inVars = new ArrayList<>();
		List<OutputVarDeclaration> outVars = new ArrayList<>();
		List<InputOutputVarDeclaration> inOutVars = new ArrayList<>();
		List<VarDeclaration> vars = new ArrayList<>();
		List<State> states = new ArrayList<>();
		states.add(state1);
		states.add(state2);
		su.nsk.iae.post.poST.Process process = ProgramFactory.createProcess(processName, inVars, outVars, inOutVars, vars, states);
		Path path = new Path(null, s0);
		path.doReturn();
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VarInitDeclaration varDecl = ProgramFactory.createSimpleVarDeclaration("BOOL", null, a);
		vcGenVars.addVars(varDecl, null, ModificationType.VAR);
		vcGenVars.setCurrentProcess(processName);
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		List<Path> expected = new ArrayList<>();
		expected.add(path);
		List<Path> result = vcGen.generateProcess(path, process);
		Assert.assertEquals(expected, result);
	}
	
	@Test
	public void testGenerateProgramWithSeveralProcesses() throws Exception {
		String programText = 
				"PROGRAM Prg\r\n"
				+ "VAR_OUTPUT\r\n"
				+ "a, b: BOOL;\r\n"
				+ "END_VAR\r\n"
				+ "PROCESS process1\r\n"
				+ "STATE state1\r\n"
				+ "a:=TRUE;\r\n"
				+ "END_STATE\r\n"
				+ "END_PROCESS\r\n"
				+ "PROCESS process2\r\n"
				+ "STATE state2\r\n"
				+ "b:= TRUE;\r\n"
				+ "END_STATE\r\n"
				+ "END_PROCESS\r\n"
				+ "END_PROGRAM";
		Term s0 = new Variable("s0");
		FunctionSymbol inv = new FunctionSymbol("inv", true);
		FunctionSymbol env = new FunctionSymbol("env", true);
		Term invs0 = new ComplexTerm(inv, s0);
		Term s1 = setVarAny(s0);
		Term envs1 = new ComplexTerm(env, s1);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		Model model = parser.parse(programText);
		Program program = model.getPrograms().get(0);
		vcGen.generateProgram(program);
		su.nsk.iae.post.vcgenerator.Constant a = vcGenVars.getVariable("a");
		su.nsk.iae.post.vcgenerator.Constant b = vcGenVars.getVariable("b");
		su.nsk.iae.post.vcgenerator.Constant process1 = vcGenVars.getProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant process2 = vcGenVars.getProcess("process2");
		Assert.assertNotNull(process1);
		Assert.assertNotNull(process2);
		vcGenVars.setCurrentProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant state1 = vcGenVars.getState("state1");
		vcGenVars.setCurrentProcess("process2");;
		su.nsk.iae.post.vcgenerator.Constant state2 = vcGenVars.getState("state2");
		Term stateAfterProcess1 = setVarBool(s1, a, True);
		List<Term> expected = new ArrayList<>();
		expected.add(impl(eq(s0, toEnv(setPstate(emptyState, process1, state1))), invs0));
		expected.add((impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), eq(getPstate(stateAfterProcess1, process2), state2)), 
				new ComplexTerm(inv, toEnv(setVarBool(stateAfterProcess1, b, True))))));
		expected.add((impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), eq(getPstate(stateAfterProcess1, process2), stop)), 
				new ComplexTerm(inv, toEnv(stateAfterProcess1)))));
		expected.add((impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), eq(getPstate(stateAfterProcess1, process2), error)), 
				new ComplexTerm(inv, toEnv(stateAfterProcess1)))));
		expected.add((impl(and(invs0, envs1, eq(getPstate(s1, process1), stop), eq(getPstate(s1, process2), state2)), 
				new ComplexTerm(inv, toEnv(setVarBool(s1, b, True))))));
		expected.add((impl(and(invs0, envs1, eq(getPstate(s1, process1), stop), eq(getPstate(s1, process2), stop)), 
				new ComplexTerm(inv, toEnv(s1)))));
		expected.add((impl(and(invs0, envs1, eq(getPstate(s1, process1), stop), eq(getPstate(s1, process2), error)), 
				new ComplexTerm(inv, toEnv(s1)))));
		expected.add((impl(and(invs0, envs1, eq(getPstate(s1, process1), error), eq(getPstate(s1, process2), state2)), 
				new ComplexTerm(inv, toEnv(setVarBool(s1, b, True))))));
		expected.add((impl(and(invs0, envs1, eq(getPstate(s1, process1), error), eq(getPstate(s1, process2), stop)), 
				new ComplexTerm(inv, toEnv(s1)))));
		expected.add((impl(and(invs0, envs1, eq(getPstate(s1, process1), error), eq(getPstate(s1, process2), error)), 
				new ComplexTerm(inv, toEnv(s1)))));
		Assert.assertEquals(expected, vcGenVars.vcSet);
	}
	
	@Test
	public void testGenerateProgramWithInitializedVariables() throws Exception {
		String programText = 
				"PROGRAM Prg\r\n"
				+ "VAR_INPUT\r\n"
				+ "in: BOOL;\r\n"
				+ "END_VAR\r\n"
				+ "VAR_OUTPUT\r\n"
				+ "out: BOOL;\r\n"
				+ "END_VAR\r\n"
				+ "VAR_IN_OUT\r\n"
				+ "inOut: BOOL;\r\n"
				+ "END_VAR\r\n"
				+ "VAR\r\n"
				+ "var1: INT := 1;\r\n"
				+ "var2: INT := 2;\r\n"
				+ "var3: INT := var1/var2;\r\n"
				+ "END_VAR\r\n"
				+ "PROCESS process1\r\n"
				+ "VAR_INPUT\r\n"
				+ "pIn: BOOL;\r\n"
				+ "END_VAR\r\n"
				+ "VAR_OUTPUT\r\n"
				+ "pOut: BOOL;\r\n"
				+ "END_VAR\r\n"
				+ "VAR_IN_OUT\r\n"
				+ "pInOut: BOOL;\r\n"
				+ "END_VAR\r\n"
				+ "VAR\r\n"
				+ "pVar: BOOL;\r\n"
				+ "END_VAR\r\n"
				+ "STATE state1\r\n"
				+ "pOut := TRUE\r\n"
				+ "END_STATE\r\n"
				+ "END_PROCESS\r\n"
				+ "END_PROGRAM";
		su.nsk.iae.post.vcgenerator.Constant var1Value = new su.nsk.iae.post.vcgenerator.Constant(1);
		su.nsk.iae.post.vcgenerator.Constant var2Value = new su.nsk.iae.post.vcgenerator.Constant(2);
		su.nsk.iae.post.vcgenerator.Constant _0 = new su.nsk.iae.post.vcgenerator.Constant(0);
		Term s0 = new Variable("s0");
		Variable inValue = new Variable("in_value");
		Variable inOutValue = new Variable("inOut_value");
		Variable pInValue = new Variable("pIn_value");
		Variable pInOutValue = new Variable("pInOut_value");
		FunctionSymbol inv = new FunctionSymbol("inv", true);
		FunctionSymbol env = new FunctionSymbol("env", true);
		Term invs0 = new ComplexTerm(inv, s0);
		Term s1 = setVarAny(s0, inValue, inOutValue, pInValue, pInOutValue);
		Term envs1 = new ComplexTerm(env, s1);
		VCGeneratorState vcGenVars = new VCGeneratorState();
		VCGenerator vcGen = new VCGenerator();
		vcGen.globVars = vcGenVars;
		Model model = parser.parse(programText);
		Program program = model.getPrograms().get(0);
		vcGen.generateProgram(program);
		su.nsk.iae.post.vcgenerator.Constant var1 = vcGenVars.getVariable("var1");
		su.nsk.iae.post.vcgenerator.Constant var2 = vcGenVars.getVariable("var2");
		su.nsk.iae.post.vcgenerator.Constant var3 = vcGenVars.getVariable("var3");
		su.nsk.iae.post.vcgenerator.Constant process1 = vcGenVars.getProcess("process1");
		vcGenVars.setCurrentProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant pOut = vcGenVars.getVariable("pOut");
		su.nsk.iae.post.vcgenerator.Constant state1 = vcGenVars.getState("state1");
		Term stateAfterVar12Initialization = setVarInt(setVarInt(emptyState, var1, var1Value), var2, var2Value);
		Term stateAfterVar123Initialization = setVarInt(
				stateAfterVar12Initialization,
				var3,
				div(getVarInt(stateAfterVar12Initialization, var1), getVarInt(stateAfterVar12Initialization, var2)));
		List<Term> expected = new ArrayList<>();
		expected.add(noteq(getVarInt(stateAfterVar12Initialization, var2), _0));
		expected.add(impl(eq(s0, toEnv(setPstate(stateAfterVar123Initialization, process1, state1))), invs0));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), state1)),
				new ComplexTerm(inv, toEnv(setVarBool(s1, pOut, True)))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), stop)),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), error)),
				new ComplexTerm(inv, toEnv(s1))));
		Assert.assertEquals(expected, vcGenVars.vcSet);
	}
	
	@Test
	public void testGenerateVCsForConfiguredProgramConfigurationForAnotherProgram() throws Exception {
		String programText =
				"PROGRAM Prg1\r\n"
				+ "PROCESS process1\r\n"
				+ "STATE state1\r\n"
				+ "TIMEOUT T#1h100ms THEN\r\n"
				+ "END_TIMEOUT\r\n"
				+ "END_STATE\r\n"
				+ "END_PROCESS\r\n"
				+ "END_PROGRAM\r\n"
				+ "PROGRAM Prg2\r\n"
				+ "END_PROGRAM\r\n"
				+ "CONFIGURATION Conf\r\n"
				+ "RESOURCE Res1 ON TestCPU\r\n"
				+ "TASK T1 (INTERVAL := T#10ms, PRIORITY := 1);\r\n"
				+ "PROGRAM program2 WITH T1: Prg2;\r\n"
				+ "END_RESOURCE\r\n"
				+ "END_CONFIGURATION"
				+ "\r\n";;
		int timeInMilliseconds = 1000 *60 * 60 + 100;
		int defaultPeriod = 100;
		int period = 10;
		int timeInCycles = timeInMilliseconds / defaultPeriod;
		su.nsk.iae.post.vcgenerator.Constant timeout = new su.nsk.iae.post.vcgenerator.Constant(timeInCycles);
		Term s0 = new Variable("s0");
		FunctionSymbol inv = new FunctionSymbol("inv", true);
		FunctionSymbol env = new FunctionSymbol("env", true);
		Term invs0 = new ComplexTerm(inv, s0);
		Term s1 = setVarAny(s0);
		Term envs1 = new ComplexTerm(env, s1);
		VCGenerator vcGen = new VCGenerator(defaultPeriod);
		Model model = parser.parse(programText);
		VCGeneratorState vcGenVars = vcGen.generateVCsForConfiguredProgram(model);
		su.nsk.iae.post.vcgenerator.Constant process1 = vcGenVars.getProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant state1 = vcGenVars.getState("state1");
		List<Term> expected = new ArrayList<>();
		expected.add(impl(eq(s0, toEnv(setPstate(emptyState, process1, state1))), invs0));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), leq(timeout, ltime(s1, process1))),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), not(leq(timeout, ltime(s1, process1)))),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), stop)),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), error)),
				new ComplexTerm(inv, toEnv(s1))));
		Assert.assertEquals(expected,  vcGenVars.getVcSet());
	}
	
	@Test
	public void testGenerateVCsForConfiguredProgramWithoutConfiguration() throws Exception {
		String programText =
				"PROGRAM Prg1\r\n"
				+ "PROCESS process1\r\n"
				+ "STATE state1\r\n"
				+ "TIMEOUT T#1h100ms THEN\r\n"
				+ "END_TIMEOUT\r\n"
				+ "END_STATE\r\n"
				+ "END_PROCESS\r\n"
				+ "END_PROGRAM\r\n";
		int timeInMilliseconds = 1000 *60 * 60 + 100;
		int defaultPeriod = 100;
		int timeInCycles = timeInMilliseconds / defaultPeriod;
		su.nsk.iae.post.vcgenerator.Constant timeout = new su.nsk.iae.post.vcgenerator.Constant(timeInCycles);
		Term s0 = new Variable("s0");
		FunctionSymbol inv = new FunctionSymbol("inv", true);
		FunctionSymbol env = new FunctionSymbol("env", true);
		Term invs0 = new ComplexTerm(inv, s0);
		Term s1 = setVarAny(s0);
		Term envs1 = new ComplexTerm(env, s1);
		VCGenerator vcGen = new VCGenerator(defaultPeriod);
		Model model = parser.parse(programText);
		VCGeneratorState vcGenVars = vcGen.generateVCsForConfiguredProgram(model);
		su.nsk.iae.post.vcgenerator.Constant process1 = vcGenVars.getProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant state1 = vcGenVars.getState("state1");
		List<Term> expected = new ArrayList<>();
		expected.add(impl(eq(s0, toEnv(setPstate(emptyState, process1, state1))), invs0));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), leq(timeout, ltime(s1, process1))),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), not(leq(timeout, ltime(s1, process1)))),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), stop)),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), error)),
				new ComplexTerm(inv, toEnv(s1))));
		Assert.assertEquals(expected,  vcGenVars.getVcSet());
	}
	
	@Test
	public void testGenerateVCsForConfiguredProgramConfigurationWihoutTask() throws Exception {
		String programText =
				"PROGRAM Prg1\r\n"
				+ "PROCESS process1\r\n"
				+ "STATE state1\r\n"
				+ "TIMEOUT T#1h100ms THEN\r\n"
				+ "END_TIMEOUT\r\n"
				+ "END_STATE\r\n"
				+ "END_PROCESS\r\n"
				+ "END_PROGRAM\r\n"
				+ "PROGRAM Prg2\r\n"
				+ "END_PROGRAM\r\n"
				+ "CONFIGURATION Conf\r\n"
				+ "RESOURCE Res1 ON TestCPU\r\n"
				+ "PROGRAM program1 : Prg1;\r\n"
				+ "END_RESOURCE\r\n"
				+ "END_CONFIGURATION"
				+ "\r\n";;
		int timeInMilliseconds = 1000 *60 * 60 + 100;
		int defaultPeriod = 100;
		int period = 10;
		int timeInCycles = timeInMilliseconds / defaultPeriod;
		su.nsk.iae.post.vcgenerator.Constant timeout = new su.nsk.iae.post.vcgenerator.Constant(timeInCycles);
		Term s0 = new Variable("s0");
		FunctionSymbol inv = new FunctionSymbol("inv", true);
		FunctionSymbol env = new FunctionSymbol("env", true);
		Term invs0 = new ComplexTerm(inv, s0);
		Term s1 = setVarAny(s0);
		Term envs1 = new ComplexTerm(env, s1);
		VCGenerator vcGen = new VCGenerator(defaultPeriod);
		Model model = parser.parse(programText);
		VCGeneratorState vcGenVars = vcGen.generateVCsForConfiguredProgram(model);
		su.nsk.iae.post.vcgenerator.Constant process1 = vcGenVars.getProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant state1 = vcGenVars.getState("state1");
		List<Term> expected = new ArrayList<>();
		expected.add(impl(eq(s0, toEnv(setPstate(emptyState, process1, state1))), invs0));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), leq(timeout, ltime(s1, process1))),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), not(leq(timeout, ltime(s1, process1)))),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), stop)),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), error)),
				new ComplexTerm(inv, toEnv(s1))));
		Assert.assertEquals(expected,  vcGenVars.getVcSet());
	}
	
	@Test
	public void testGenerateVCsForConfiguredProgramConfigurationWithTask() throws Exception {
		String programText =
				"PROGRAM Prg1\r\n"
				+ "PROCESS process1\r\n"
				+ "STATE state1\r\n"
				+ "TIMEOUT T#1h100ms THEN\r\n"
				+ "END_TIMEOUT\r\n"
				+ "END_STATE\r\n"
				+ "END_PROCESS\r\n"
				+ "END_PROGRAM\r\n"
				+ "PROGRAM Prg2\r\n"
				+ "END_PROGRAM\r\n"
				+ "CONFIGURATION Conf\r\n"
				+ "RESOURCE Res1 ON TestCPU\r\n"
				+ "TASK T1 (INTERVAL := T#10ms, PRIORITY := 1);\r\n"
				+ "PROGRAM program1 WITH T1: Prg1;\r\n"
				+ "END_RESOURCE\r\n"
				+ "END_CONFIGURATION"
				+ "\r\n";;
		int timeInMilliseconds = 1000 *60 * 60 + 100;
		int defaultPeriod = 100;
		int period = 10;
		int timeInCycles = timeInMilliseconds / period;
		su.nsk.iae.post.vcgenerator.Constant timeout = new su.nsk.iae.post.vcgenerator.Constant(timeInCycles);
		Term s0 = new Variable("s0");
		FunctionSymbol inv = new FunctionSymbol("inv", true);
		FunctionSymbol env = new FunctionSymbol("env", true);
		Term invs0 = new ComplexTerm(inv, s0);
		Term s1 = setVarAny(s0);
		Term envs1 = new ComplexTerm(env, s1);
		VCGenerator vcGen = new VCGenerator(defaultPeriod);
		Model model = parser.parse(programText);
		VCGeneratorState vcGenVars = vcGen.generateVCsForConfiguredProgram(model);
		su.nsk.iae.post.vcgenerator.Constant process1 = vcGenVars.getProcess("process1");
		su.nsk.iae.post.vcgenerator.Constant state1 = vcGenVars.getState("state1");
		List<Term> expected = new ArrayList<>();
		expected.add(impl(eq(s0, toEnv(setPstate(emptyState, process1, state1))), invs0));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), leq(timeout, ltime(s1, process1))),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), state1), not(leq(timeout, ltime(s1, process1)))),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), stop)),
				new ComplexTerm(inv, toEnv(s1))));
		expected.add(impl(and(invs0, envs1, eq(getPstate(s1, process1), error)),
				new ComplexTerm(inv, toEnv(s1))));
		Assert.assertEquals(expected,  vcGenVars.getVcSet());
	}
}
