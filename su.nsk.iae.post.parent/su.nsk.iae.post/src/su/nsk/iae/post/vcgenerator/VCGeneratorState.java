package su.nsk.iae.post.vcgenerator;

import java.util.*;

import su.nsk.iae.post.poST.ArrayInterval;
import su.nsk.iae.post.poST.ArraySpecificationInit;
import su.nsk.iae.post.poST.Expression;
import su.nsk.iae.post.poST.InputOutputVarDeclaration;
import su.nsk.iae.post.poST.InputVarDeclaration;
import su.nsk.iae.post.poST.OutputVarDeclaration;
import su.nsk.iae.post.poST.SimpleSpecificationInit;
import su.nsk.iae.post.poST.State;
import su.nsk.iae.post.poST.SymbolicVariable;
import su.nsk.iae.post.poST.VarDeclaration;
import su.nsk.iae.post.poST.VarInitDeclaration;

public class VCGeneratorState {
	Map<Constant, String> varTypes = new HashMap<>();
	Map <String, Constant> variables = new HashMap<>();
	List<Constant> constants = new ArrayList<>();
	Map<Constant, Term> constantValues = new HashMap<>();
	Map<Constant, Constant> timeoutConstantValues = new HashMap<>();
	Map<String, Map<String, Constant>> localVars = new HashMap<>();
	List<Constant> envVars = new ArrayList<>();
	Map<String, List<Constant>> initializedVars = new HashMap<>();
	Map<Constant, SimpleSpecificationInit> varSpecifications = new HashMap<>();
	Map<Constant, ArraySpecificationInit> arraySpecifications = new HashMap<>();
	Map<Constant, IndexRange> indexRanges = new HashMap<>();
	Map<Constant, List<Term>> arrayConstantValues = new HashMap<>();
	int currentProcessState;
	Map<String, StateList> processStates = new HashMap<>();
	Constant currentProcess;
	Map<String, Constant> processes = new HashMap<>();
	Map<String, Constant> initialStates = new HashMap<>();
	int period;
	List<Term> vcSet = new ArrayList<>();
	int loopNumber = 0;
	int pstateNumber = 1;
	int varNumber = 0;
	int processNumber = 0;

	public VCGeneratorState(int period) {
		this.period = period;
		initializedVars.put(null, new ArrayList<>());
	}
	
	public VCGeneratorState() {
		this(0);
	}

	public String getVarType(Constant varCode) {
		return varTypes.get(varCode);
	}

	public Constant getVariable(String name) {
		if (currentProcess == null)
			return variables.get(name);
		Map<String, Constant> localScope = localVars.get(currentProcess.getName());
		if (localScope != null && localScope.get(name) != null)
			return localScope.get(name);
		return variables.get(name);
	}

	public boolean isConstant(Constant varCode) {
		return constants.contains(varCode);
	}

	public Term getConstantValue(Constant c) {
		return constantValues.get(c);
	}
	
	public Constant getTimeoutConstantValue(Constant c) {
		if (timeoutConstantValues.containsKey(c))
			return timeoutConstantValues.get(c);
		else {
			Integer timeInMilliseconds = (Integer) constantValues.get(c).getValue();
			Constant timeoutConst = null;
			if (timeInMilliseconds != null) {
				timeoutConst = millisecondsToCycles(timeInMilliseconds);
				timeoutConst.setName(c.getName() + "_TIMEOUT");
			}
			timeoutConstantValues.put(c, timeoutConst);
			return timeoutConst;
		}
	}
	
	public Term getArrayConstantValue(Constant array, Term index) {
		if (index.getValue() == null)
			return null;
		int arrayIndex = (Integer) index.getValue();
		Integer start = (Integer) indexRanges.get(array).getStart().getValue();
		if (start == null)
			return null;
		int startIndex = start;
		return arrayConstantValues.get(array).get(arrayIndex - startIndex);
	}

	public Constant getState(String name) {
		return processStates.get(currentProcess.getName()).getState(name);
	}

	public Constant getCurrentState() {
		return processStates.get(currentProcess.getName()).getState(currentProcessState);
	}

	public Constant getNextState() {
		return processStates.get(currentProcess.getName()).getState(currentProcessState + 1);
	}

	public Constant getProcess(String name) {
		return processes.get(name);
	}

	public Constant getInitialState() {
		return getInitialState(currentProcess.getName());
	}

	public Constant getInitialState(String processName) {
		return processStates.get(processName).getState(0);
	}

	public void addVerificationCondition(Term vc) {
		getVcSet().add(vc);
	}

	public FunctionSymbol nextLoopInv() {
		++loopNumber;
		return new FunctionSymbol("loopinv"+loopNumber, true);
	}

	public void addState(String stateName, String prefix) {
		++pstateNumber;
		processStates.get(prefix).addState(stateName, prefix, pstateNumber);
	}

	public void setCurrentProcess(String processName) {
		currentProcess = processes.get(processName);
		currentProcessState = 0;
	}

	public void addVars(VarInitDeclaration varDecl, String prefix, ModificationType modType) {
		List<Constant> 	initializedVars = this.initializedVars.get(prefix);
		String varType;
		Expression value = null;
		ArraySpecificationInit arraySpec = null;
		if (varDecl.getSpec() != null) {
			varType = varDecl.getSpec().getType();
			value = varDecl.getSpec().getValue();				
		}			
		else {			
			arraySpec = varDecl.getArrSpec();
			varType = arraySpec.getInit().getType();
		}			
		for (SymbolicVariable symVar: varDecl.getVarList().getVars()) {
			++varNumber;
			String fullVarName;
			if (prefix == null)
				fullVarName = symVar.getName();
			else
				fullVarName = prefix + "_" + symVar.getName();
			Constant varCode = new Constant(fullVarName, varNumber);
			if (value != null && modType != ModificationType.CONSTANT || arraySpec != null) {
				initializedVars.add(varCode);
				if (value != null)
					varSpecifications.put(varCode, varDecl.getSpec());
				else
					arraySpecifications.put(varCode, arraySpec);
			}				
			if (prefix == null) {
				variables.put(symVar.getName(), varCode);
			}
			else {
				Map<String, Constant> varsInScope = localVars.get(prefix);
				if (varsInScope == null) {
					varsInScope = new HashMap<>();
					localVars.put(prefix, varsInScope);
				}
				varsInScope.put(symVar.getName(), varCode);
			}
			varTypes.put(varCode, varType);
			if (modType == ModificationType.CONSTANT) {
				constants.add(varCode);
				if (value != null) {
					Term constantValue = value.generateExpression(Constant.emptyState, this);
					if (constantValue.equals(Constant.True))
						constantValue = new Constant(DataType.BOOL, varCode.getName(), true);
					if (constantValue.equals(Constant.False))
						constantValue = new Constant(DataType.BOOL, varCode.getName(), false);
					constantValues.put(varCode, constantValue);
				}				
			}				
			else if (modType == ModificationType.ENV_VAR)
				envVars.add(varCode);
		}
	}
	
	public List<Constant> getInitializedVars(String prefix) {
		return initializedVars.get(prefix);
	}

	public Constant addProcess(su.nsk.iae.post.poST.Process process) {
		++processNumber;
		String processName = process.getName();
		Constant processCode = new Constant(processName, processNumber);
		processes.put(processName, processCode);
		processStates.put(processName, new StateList());
		initializedVars.put(processName, new ArrayList<>());
		currentProcess = processCode;
		//Encoding of input variables
		for (InputVarDeclaration inVars: process.getProcInVars())
			for (VarInitDeclaration varDecl: inVars.getVars())
				addVars(varDecl, processName, ModificationType.ENV_VAR);
		//Encoding of output variables
		for (OutputVarDeclaration outVars: process.getProcOutVars())
			for (VarInitDeclaration varDecl: outVars.getVars())
				addVars(varDecl, processName, ModificationType.VAR);
		//Encoding of input output variables
		for (InputOutputVarDeclaration inOutVars: process.getProcInOutVars())
			for (VarInitDeclaration varDecl: inOutVars.getVars())
				addVars(varDecl, processName, ModificationType.ENV_VAR);
		//Encoding of variables
		for (VarDeclaration vars: process.getProcVars())
			for (VarInitDeclaration varDecl: vars.getVars())
				if (vars.isConst())
					addVars(varDecl, processName, ModificationType.CONSTANT);
				else
					addVars(varDecl, processName, ModificationType.VAR);
		//Encoding of states
		for (State state: process.getStates())
			addState(state.getName(), process.getName());
		return processCode;
	}
	
	public Term initializeVar(Constant variable, Term state) {
		if (isArray(variable))
			return initializeArray(variable, state);
		else
			return initializeSimpleVar(variable, state);
	}
	
	public IndexRange getIndexRange(Constant varCode) {
		return indexRanges.get(varCode);
	}

	private Term initializeSimpleVar(Constant variable, Term state) {
		SimpleSpecificationInit varSpec = varSpecifications.get(variable);
		Term value = varSpec.getValue().generateExpression(state, this);
		Term newState = TermFactory.setVar(varSpec.getType(), state, variable, value);
		newState.addCondition(state.getPrecondition());
		newState.addCondition(value.getPrecondition());
		return newState;
	}

	private Term initializeArray(Constant variable, Term state) {
		ArraySpecificationInit arraySpec = arraySpecifications.get(variable);
		ArrayInterval interval = arraySpec.getInit().getInterval();
		Term start = interval.getStart().generateExpression(state, this);
		Term end = interval.getEnd().generateExpression(state, this);
		IndexRange range = new IndexRange(start, end);	
		indexRanges.put(variable, range);
		List<Expression> values = arraySpec.getValues().getElements();
		state.addCondition(start.getPrecondition());
		state.addCondition(end.getPrecondition());
		if (values != null) {
			int i = 0;
			List<Term> arrayValues =new ArrayList<>();
			for (Expression expr: values) {
				Term arrayIndex = range.get(i);
				Term value = expr.generateExpression(state, this);
				arrayValues.add(value);
				Term newState = TermFactory.setVarArray(arraySpec.getInit().getType(), state, variable, arrayIndex, value);
				newState.addCondition(state.getPrecondition());
				newState.addCondition(value.getPrecondition());
				state = newState;
			}
			arrayConstantValues.put(variable, arrayValues);
		}
		return state;
	}

	private boolean isArray(Constant variable) {
		return arraySpecifications.containsKey(variable);
	}

	public List<Term> getVcSet() {
		return vcSet;
	}

	Constant millisecondsToCycles(int timeInMilliseconds) {
		int timeInCycles;
		if (timeInMilliseconds % period == 0)
			timeInCycles = timeInMilliseconds / period;
		else
			timeInCycles = timeInMilliseconds / period + 1;
		return new Constant(timeInCycles);
	}
}

class StateList {
	List<String> stateNames;
	Map<String, Constant> pstates;

	StateList() {
		stateNames = new ArrayList<>();
		pstates = new HashMap<>();
	}

	Constant getState(String name) {
		return pstates.get(name);
	}

	Constant getState(int index) {
		return getState(stateNames.get(index));
	}

	void addState(String stateName, String prefix, int stateCode) {
		stateNames.add(stateName);
		pstates.put(stateName, new Constant(prefix + "_" + stateName, stateCode));
	}
}
