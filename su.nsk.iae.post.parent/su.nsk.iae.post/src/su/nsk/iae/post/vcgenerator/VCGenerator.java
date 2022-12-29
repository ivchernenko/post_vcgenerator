package su.nsk.iae.post.vcgenerator;

import java.util.*;

import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.Constant;

public class VCGenerator {
	VCGeneratorState globVars = new VCGeneratorState();

	List<Path> generateTimeout(Path path, TimeoutStatement statement) {
		if (path.getStatus() != ExecutionStatus.NORMAL) {
			List<Path> result = new ArrayList<>();
			result.add(path);
			return result;
		}
		Term time;
		if(statement.getConst() != null) {
			int timeInMilliseconds = (Integer) statement.getConst().generateConstant().getValue();
			int timeInCycles;
			if (timeInMilliseconds % globVars.period == 0)
				timeInCycles = timeInMilliseconds / globVars.period;
			else
				timeInCycles = timeInMilliseconds / globVars.period + 1;
			time = new Constant(timeInCycles);
		}
		else { // Variable
			Term symComputedVar = statement.getVariable().generateVariable(path.getCurrentState(), globVars);
			time = new ComplexTerm(
					FunctionSymbol.PLUS,
					new ComplexTerm(
							FunctionSymbol.DIV,
							new ComplexTerm(FunctionSymbol.MINUS, symComputedVar, new Constant(1)),
							new Constant(globVars.period)),
					new Constant(1));
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
			++globVars.currentProcessState;
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
		for (su.nsk.iae.post.poST.Process process: program.getProcesses()) {
			String processName = process.getName();
			globVars.addProcess(process);
			//Encoding of input variables
			for (InputVarDeclaration inVars: process.getProcInVars())
				for (VarInitDeclaration varDecl: inVars.getVars())
					globVars.addVars(varDecl, processName, ModificationType.ENV_VAR);
			//Encoding of output variables
			for (OutputVarDeclaration outVars: process.getProcOutVars())
				for (VarInitDeclaration varDecl: outVars.getVars())
					globVars.addVars(varDecl, processName, ModificationType.VAR);
			//Encoding of input output variables
			for (InputOutputVarDeclaration inOutVars: process.getProcInOutVars())
				for (VarInitDeclaration varDecl: inOutVars.getVars())
					globVars.addVars(varDecl, processName, ModificationType.ENV_VAR);
			//Encoding of variables
			for (VarDeclaration vars: process.getProcVars())
				for (VarInitDeclaration varDecl: vars.getVars())
					if (vars.isConst())
						globVars.addVars(varDecl, processName, ModificationType.CONSTANT);
					else
						globVars.addVars(varDecl, processName ModificationType.VAR);
			//Encoding of states
			for (State state: process.getStates())
				globVars.addState(state.getName(), process.getName());
		}
		FunctionSymbol init = new FunctionSymbol("init", false);
		FunctionSymbol env = new FunctionSymbol("env", false);
		FunctionSymbol inv = new FunctionSymbol("inv", false);
		Variable s0 = new Variable("s0");
		Term invs0 = new ComplexTerm(inv s0);
		List<Term> setVarAnyArgs = new ArrayList<>();
		setVarAnyArgs.add(s0);
		for (Constant envVar: globVars.envVars) {
			Variable var_value = new Variable(envVar.getName()+"_value");
			setVarAnyArgs.add(var_value);
		}
		Term s1 = new ComplexTerm(FunctionSymbol.setVarAny, (Term[]) setVarAnyArgs.toArray());
		Term envs1 = new ComplexTerm(env, s1);
		List<Term> controlLoopBodyPrecondition = new ArrayList<>(2);
		controlLoopBodyPrecondition.add(invs0);
		controlLoopBodyPrecondition.add(envs1);
		boolean initialProcess = true;
		Term state = Constant.emptyState;
		for (su.nsk.iae.post.poST.Process process: program.getProcesses()) {
			Constant processCode = globVars.getProcess(process.getName());
			if (initialProcess) {
				Constant initialState = globVars.getInitialState(process.getName());
				state = new ComplexTerm(FunctionSymbol.setPstate, state, processCode, initialState);
			}
			initialProcess = false;	
		}
		Term vcForInitPath =new ComplexTerm(
				FunctionSymbol.IMPL,
				new ComplexTerm(FunctionSymbol.EQ, s0, state),
				new ComplexTerm(inv, s0));		
		List<Path> controlLoopBody = new ArrayList<>(1);
		controlLoopBody.add(new Path(controlLoopBodyPrecondition, s0));
		for (su.nsk.iae.post.poST.Process process: program.getProcesses()) {
			List<Path> afterProcess = new ArrayList<>();
			for (Path path: controlLoopBody)
				afterProcess.addAll(generateProcess(path, process));
			controlLoopBody = afterProcess;
		}
		for (Path path: controlLoopBody)
			globVars.addVerificationCondition(path.generateVerificationCondition(inv));

	}
}
