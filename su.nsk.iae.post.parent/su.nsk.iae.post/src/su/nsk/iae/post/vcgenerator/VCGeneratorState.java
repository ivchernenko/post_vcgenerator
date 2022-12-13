package su.nsk.iae.post.vcgenerator;

import java.util.*;

public class VCGeneratorState {
	Map<String, String> varTypes;
	Map <String, Constant> variables;
	List<String> envVars;
	int currentProcessState;
	Map<String, Constant> pstates;
	String[] stateNames;
	Constant currentProcess;
	Map<String, Constant> processes;
	Map<String, Constant> initialStates;
	int period;
	
	public VCGeneratorState() {
		varTypes = new HashMap<>();
		variables = new HashMap<>();
		envVars = new ArrayList<>();
		processes = new HashMap<>();
		initialStates = new HashMap<>();
	}
	
	public String getVarType(String name) {
		return varTypes.get(name);
	}
	
	public Constant getVariable(String name) {
		return variables.get(name);
	}
	
	public Constant getState(String name) {
		return pstates.get(name);
	}
	
	public Constant getCurrentState() {
		String stateName =stateNames[currentProcessState];
		return pstates.get(stateName);
	}
	
	public Constant getNextState() {
		String stateName =stateNames[currentProcessState + 1];
		return pstates.get(stateName);
	}
	
	public Constant getProcess(String name) {
		return processes.get(name);
	}
	
	public Constant getInitialState() {
		return pstates.get(stateNames[0]);
	}
	
	public Constant getInitialStateOfProcess(String name) {
		return initialStates.get(name);
	}

}
