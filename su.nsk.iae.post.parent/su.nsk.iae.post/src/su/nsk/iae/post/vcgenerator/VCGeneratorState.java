package su.nsk.iae.post.vcgenerator;

import java.util.*;

import su.nsk.iae.post.poST.SimpleSpecificationInit;
import su.nsk.iae.post.poST.State;
import su.nsk.iae.post.poST.SymbolicVariable;
import su.nsk.iae.post.poST.VarInitDeclaration;

public class VCGeneratorState {
	Map<String, String> varTypes;
	Map <String, Constant> variables;
	List<Constant> constants;
	Map<String, Map<String, Constant>> localVars;
	Map<String, Map<String, String>> localVarTypes;
	List<Constant> envVars;
	int currentProcessState;
	Map<String, StateList> processStates;
	Constant currentProcess;
	Map<String, Constant> processes;
	Map<String, Constant> initialStates;
	int period;
	List<Term> vcSet;
	int loopNumber = 0;
	int pstateNumber = 1;
	int varNumber = 0;
	int processNumber = 0;
	
	public VCGeneratorState() {
		varTypes = new HashMap<>();
		variables = new HashMap<>();
		envVars = new ArrayList<>();
		processes = new HashMap<>();
		initialStates = new HashMap<>();
		vcSet = new ArrayList<>();	
		constants = new ArrayList<>();
		localVars = new HashMap<>();
		localVarTypes = new HashMap<>();
	}
	
	
	public String getVarType(String name) {
		Map<String, String> localScope = localVarTypes.get(currentProcess.getValue());
		if (localScope != null && localScope.get(name) != null)
			return localScope.get(name);
		return varTypes.get(name);
	}
	
	public Constant getVariable(String name) {
		Map<String, Constant> localScope = localVars.get(currentProcess.getValue());
		if (localScope != null && localScope.get(name) != null)
			return localScope.get(name);
		return variables.get(name);
	}
	
	public boolean isConstant(Constant varCode) {
		return constants.contains(varCode);
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
		vcSet.add(vc);
	}
	
	public FunctionSymbol nextLoopInv() {
		++loopNumber;
		return new FunctionSymbol("loopinv"+loopNumber, false);
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
		String varType;
		if (varDecl.getSpec() != null)
			varType = varDecl.getSpec().getType();
		else
			varType = varDecl.getArrSpec().getInit().getType();
		for (SymbolicVariable symVar: varDecl.getVarList().getVars()) {
			++varNumber;
			String fullVarName;
			if (prefix == null)
				fullVarName = symVar.getName();
			else
				fullVarName = prefix + "_" + symVar.getName();
			Constant varCode = new Constant(fullVarName, varNumber);
			if (prefix == null) {
				variables.put(symVar.getName(), varCode);
				varTypes.put(symVar.getName(), varType);
			}
			else {
				Map<String, Constant> varsInScope = localVars.get(prefix);
				if (varsInScope == null) {
					varsInScope = new HashMap<>();
					localVars.put(prefix, varsInScope);
				}
				varsInScope.put(symVar.getName(), varCode);
				Map<String, String> varTypesInScope = localVarTypes.get(prefix);
				if (varTypesInScope == null) {
					varTypesInScope = new HashMap<>();
					localVarTypes.put(prefix, varTypesInScope);
				}
				varTypesInScope.put(symVar.getName(), varType);
			}
			if (modType == ModificationType.CONSTANT)
				constants.add(varCode);
			else if (modType == ModificationType.ENV_VAR)
				envVars.add(varCode);
		}
	}
	
	Constant addProcess(su.nsk.iae.post.poST.Process process) {
		++processNumber;
		String processName = process.getName();
		Constant processCode = new Constant(processName, processNumber);
		processes.put(processName, processCode);
		processStates.put(processName, new StateList());
		return processCode;
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
