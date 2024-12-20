package su.nsk.iae.post.vcgenerator;

import java.util.*;

import java.util.stream.Stream;

import org.eclipse.emf.ecore.EObject;

import su.nsk.iae.post.poST.*;
import static su.nsk.iae.post.vcgenerator.TermFactory.*;

public class VCGenerator {
	VCGeneratorState globVars;
	int period;

	public VCGenerator(int defaultPeriod) {
		period = defaultPeriod;
	}

	public VCGenerator() {
		this(0);
	}

	List<Path> generateTimeout(Path path, TimeoutStatement statement) {
		if (path.getStatus() != ExecutionStatus.NORMAL) {
			List<Path> result = new ArrayList<>();
			result.add(path);
			return result;
		}
		Term time;
		if(statement.getConst() != null) {
			int timeInMilliseconds = (Integer) statement.getConst().generateConstant().getValue();
			time = globVars.millisecondsToCycles(timeInMilliseconds);
		}
		else { // Variable
			SymbolicVariable timeoutVar = statement.getVariable();
			Constant varCode = globVars.getVariable(timeoutVar.getName());
			time = null;
			if (globVars.isConstant(varCode)) {
				time = globVars.getTimeoutConstantValue(varCode);
			}
			if (time == null) {
				Term symComputedVar = timeoutVar.generateVariable(path.getCurrentState(), globVars);
				time = new ComplexTerm(
						FunctionSymbol.PLUS,
						new ComplexTerm(
								FunctionSymbol.DIV,
								new ComplexTerm(FunctionSymbol.MINUS, symComputedVar, new Constant(1)),
								new Constant(globVars.period)),
						new Constant(1));
			}
		}
		Term timeExpiredCondition = new ComplexTerm(
				FunctionSymbol.LEQ,
				time,
				new ComplexTerm(FunctionSymbol.ltime, path.getCurrentState(), globVars.currentProcess));
		Path expired = path.addCondition(timeExpiredCondition);
		Path notExpired = path.addCondition(new ComplexTerm(FunctionSymbol.NOT, timeExpiredCondition));
		List<Path> result = statement.getStatement().applyTo(expired, globVars);
		result.add(notExpired);
		return result;
	}

	List<Path> generateState(Path path, State state) {
		if (path.getStatus() != ExecutionStatus.NORMAL) {
			List<Path> result = new ArrayList<>();
			result.add(path);
			return result;
		}
		Term processInState = new ComplexTerm(
				FunctionSymbol.EQ,
				new ComplexTerm(
						FunctionSymbol.getPstate,
						path.getCurrentState(),
						globVars.currentProcess),
				globVars.getCurrentState());
		path = path.addCondition(processInState);
		List<Path> pathsBeforeTimeout = state.getStatement().applyTo(path, globVars);
		if (state.getTimeout() == null)
			return pathsBeforeTimeout;
		else {
			List<Path> result = new ArrayList<>();
			for (Path p: pathsBeforeTimeout)
				result.addAll(generateTimeout(p, state.getTimeout()));
			return result;
		}
	}

	List<Path> generateProcess(Path path, su.nsk.iae.post.poST.Process process) {
		List<Path> result = new ArrayList<>();
		if (path.getStatus() != ExecutionStatus.NORMAL) {
			result.add(path);
			return result;
		}
		globVars.setCurrentProcess(process.getName());
		for (State state: process.getStates())  {
			result.addAll(generateState(path, state));
			globVars.setCurrentProcessState(globVars.getCurrentProcessState() + 1);
		}			
		Term processInStopState = new ComplexTerm(
				FunctionSymbol.EQ,
				new ComplexTerm(
						FunctionSymbol.getPstate,
						path.getCurrentState(),
						globVars.currentProcess),
				Constant.stop);
		result.add(path.addCondition(processInStopState));
		Term processInErrorState = new ComplexTerm(
				FunctionSymbol.EQ,
				new ComplexTerm(
						FunctionSymbol.getPstate,
						path.getCurrentState(),
						globVars.currentProcess),
				Constant.error);
		result.add(path.addCondition(processInErrorState));
		return result;
	}

	void generateProgram(Program program) {
		//Encoding of input variables
		for (InputVarDeclaration inVars: program.getProgInVars())
			for (VarInitDeclaration varDecl: inVars.getVars())
				globVars.addVars(varDecl, null, ModificationType.ENV_VAR);
		//Encoding of output variables
		for (OutputVarDeclaration outVars: program.getProgOutVars())
			for (VarInitDeclaration varDecl: outVars.getVars())
				globVars.addVars(varDecl, null, ModificationType.VAR);
		//Encoding of input output variables
		for (InputOutputVarDeclaration inOutVars: program.getProgInOutVars())
			for (VarInitDeclaration varDecl: inOutVars.getVars())
				globVars.addVars(varDecl, null, ModificationType.ENV_VAR);
		//Encoding of variables
		for (VarDeclaration vars: program.getProgVars())
			for (VarInitDeclaration varDecl: vars.getVars())
				if (vars.isConst())
					globVars.addVars(varDecl, null, ModificationType.CONSTANT);
				else
					globVars.addVars(varDecl, null, ModificationType.VAR);
		//Encoding of processes
		for (su.nsk.iae.post.poST.Process process: program.getProcesses())
			globVars.addProcess(process);
		FunctionSymbol env = new FunctionSymbol("env", true);
		FunctionSymbol inv = new FunctionSymbol("inv0", true);
		Variable s0 = new Variable("s0");
		globVars.addVcVariableParam(s0);
		globVars.addVcFunctionParam(inv);
		globVars.addVcFunctionParam(env);
		Term invs0 = new ComplexTerm(inv, s0);
		List<Term> setVarAnyArgs = new ArrayList<>();
		Term s1 = s0;
		for (Constant envVar: globVars.envVars) {
			String varValueName = envVar.getName() + "value";
			Variable varValue = new Variable(varValueName);
			globVars.addVcVariableParam(varValue);
			s1 = TermFactory.setVar(globVars.getVarType(envVar), s1, envVar, varValue);
		}
		Term envs1 = new ComplexTerm(env, s1);
		boolean initialProcess = true;
		Term state = Constant.emptyState;
		for (Constant  initializedVar: globVars.getInitializedVars(null))
			state = globVars.initializeVar(initializedVar, state);
		for (su.nsk.iae.post.poST.Process process: program.getProcesses()) {
			globVars.setCurrentProcess(process.getName());
			Constant processCode = globVars.getProcess(process.getName());
			state = globVars.initializeProcessVars(process.getName(), state);
			if (initialProcess) {
				Constant initialState = globVars.getInitialState(process.getName());
				Term setInitialPstate = new ComplexTerm(FunctionSymbol.setPstate, state, processCode, initialState);
				setInitialPstate.addCondition(state.getPrecondition());
				state = setInitialPstate;
			}
			initialProcess = false;	
		}
		if (state.getPrecondition() != null) {
			globVars.addVerificationCondition(state.getPrecondition());
		}
		Term vcForInitPath =new ComplexTerm(
				FunctionSymbol.IMPL,
				new ComplexTerm(FunctionSymbol.EQ, s0, new ComplexTerm(FunctionSymbol.toEnv, state)),
				new ComplexTerm(inv, s0));	
		globVars.addVerificationCondition(vcForInitPath);
		List<Path> controlLoopBody = new ArrayList<>(1);
		Path controlLoopBodyPath = new Path(null, s1);
		controlLoopBody.add(controlLoopBodyPath);
		for (su.nsk.iae.post.poST.Process process: program.getProcesses()) {
			List<Path> afterProcess = new ArrayList<>();
			for (Path path: controlLoopBody)
				afterProcess.addAll(generateProcess(path, process));
			controlLoopBody = afterProcess;
		}
		for (Path path: controlLoopBody) {
			path.toEnv();
			path = new Path(and(invs0, envs1, path.getPrecondition()), path.getCurrentState());
			globVars.addVerificationCondition(path.generateVerificationCondition(inv));
		}
	}

	public VCGeneratorState generateVCsForConfiguredProgram(Model model) {
		String programName = model.getPrograms().get(0).getName();
		Configuration conf = model.getConf();
		if (conf != null) {
			Stream<EObject> pconfs= Utils.asStream(conf.eAllContents()).filter((e) -> {return e instanceof ProgramConfiguration;});
			Optional<EObject> pconf = pconfs.filter((e) -> ((ProgramConfiguration) e).getProgram().getName().equals(programName)).findFirst();
			if (pconf.isPresent()) {
				Task task = ((ProgramConfiguration) pconf.get()).getTask();
				if (task != null) {
					su.nsk.iae.post.poST.Constant interval = task.getInit().getInterval();
					if (interval != null)
						period = (Integer) interval.generateConstant().getValue();
				}			
			}
		}
		globVars = new VCGeneratorState(period);
		generateProgram(model.getPrograms().get(0));
		return globVars;
	}
}
