package su.nsk.iae.post.vcgenerator;

import java.util.List;
import java.util.Objects;
import java.util.ArrayList;

import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.poST.impl.*;
import su.nsk.iae.post.poST.impl.*;

public class Path {

	Term precondition;
	Term currentState;
	ExecutionStatus status;

	public Path(Term precondition, Term s0) {
		this.precondition = precondition;
		currentState = s0;
		status = ExecutionStatus.NORMAL;
	}

	public void doAssignment(SymbolicVariable variable, Expression valueExpr, VCGeneratorState globVars) {
		if (status != ExecutionStatus.NORMAL)
			return;
		Term value = valueExpr.generateExpression(currentState, globVars);
		Constant varNameCode = globVars.getVariable(variable.getName());
		String varType = globVars.getVarType(varNameCode);
		assertion(value.getPrecondition(), globVars);
		if ("BOOL".equals(varType))
			currentState = new ComplexTerm(FunctionSymbol.setVarBool, currentState, varNameCode, value);
		else if (Utils.isIntegerTypeName(varType))
			currentState = new ComplexTerm(FunctionSymbol.setVarInt, currentState, varNameCode, value);
		else if (Utils.isRealTypeName(varType))
			currentState = new ComplexTerm(FunctionSymbol.setVarReal, currentState, varNameCode, value);
		else // TIME ((getVarInt currentState variable) - 1) div period + 1
			currentState = new ComplexTerm(FunctionSymbol.setVarInt, currentState, varNameCode, value);
	}

	public void doAssignment(AssignmentStatement statement, VCGeneratorState globVars) {
		if (status != ExecutionStatus.NORMAL)
			return;
		if (statement.getVariable() != null) {
			doAssignment(statement.getVariable(), statement.getValue(), globVars);
		}
		else { // Array
			ArrayVariable arrayVariable = statement.getArray();
			SymbolicVariable variable = arrayVariable.getVariable();
			Term index = arrayVariable.getIndex().generateExpression(currentState, globVars);
			Term value = statement.getValue().generateExpression(currentState, globVars);
			Constant varNameCode = globVars.getVariable(variable.getName());
			String varType = globVars.getVarType(varNameCode);
			IndexRange range = globVars.getIndexRange(varNameCode);
			Term assertion = range.contains(index);			
			if (index.getPrecondition() != null)
				assertion = TermFactory.and(index.getPrecondition(), assertion);
			if (value.getPrecondition() != null)
				assertion = TermFactory.and(assertion, value.getPrecondition());
			assertion(assertion, globVars);
			if ("BOOL".equals(varType))
				currentState = new ComplexTerm(FunctionSymbol.setVarArrayBool, currentState, varNameCode,index,  value);
			else if (Utils.isIntegerTypeName(varType))
				currentState = new ComplexTerm(FunctionSymbol.setVarArrayInt, currentState, varNameCode, index, value);
			else if (Utils.isRealTypeName(varType))
				currentState = new ComplexTerm(FunctionSymbol.setVarArrayReal, currentState, varNameCode, index, value);
			else // TIME ((getVarInt currentState variable) - 1) div period + 1
				currentState = new ComplexTerm(FunctionSymbol.setVarArrayInt, currentState, varNameCode, index, value);
		}
	}

	public void setState(SetStateStatement statement, VCGeneratorState globVars) {
		if (status != ExecutionStatus.NORMAL)
			return;
		if (statement.isNext()) {
			Constant stateCode = globVars.getNextState();
			currentState = new ComplexTerm(FunctionSymbol.setPstate, currentState, globVars.currentProcess, stateCode);
		}
		else {
			String stateName = statement.getState().getName();
			Constant stateCode = globVars.getState(stateName);
			currentState = new ComplexTerm(FunctionSymbol.setPstate, currentState, globVars.currentProcess, stateCode);
		}		
	}

	public void resetTimer(ResetTimerStatement statement, VCGeneratorState globVars) {
		if (status != ExecutionStatus.NORMAL)
			return;
		currentState = new ComplexTerm(FunctionSymbol.reset, currentState, globVars.currentProcess);
	}

	public void startProcess(StartProcessStatement statement, VCGeneratorState globVars) {
		if (status != ExecutionStatus.NORMAL)
			return;
		if (statement.getProcess() != null) {
			su.nsk.iae.post.poST.Process process = (su.nsk.iae.post.poST.Process) statement.getProcess();
			String processName = process.getName();
			Constant processCode = globVars.getProcess(processName);
			Constant initialState = globVars.getInitialState(processName);
			currentState = globVars.initializeProcessVars(processName, currentState);
			currentState = new ComplexTerm(FunctionSymbol.setPstate, currentState, processCode, initialState);
		}
		else { // RESTART
			Constant initialState = globVars.getInitialState();
			currentState = globVars.initializeProcessVars(globVars.currentProcessName, currentState);
			currentState = new ComplexTerm(FunctionSymbol.setPstate, currentState, globVars.currentProcess, initialState);
		}
	}

	public void stopProcess(StopProcessStatement statement, VCGeneratorState globVars) {
		if (status != ExecutionStatus.NORMAL)
			return;
		if (statement.getProcess() != null) {
			su.nsk.iae.post.poST.Process process = (su.nsk.iae.post.poST.Process) statement.getProcess();
			String processName = process.getName();
			Constant processCode = globVars.getProcess(processName);
			currentState = new ComplexTerm(FunctionSymbol.setPstate, currentState, processCode, Constant.stop);
		}
		else {
			currentState = new ComplexTerm(FunctionSymbol.setPstate, currentState, globVars.currentProcess, Constant.stop);
		}
	}

	public void errorProcess(ErrorProcessStatement statement, VCGeneratorState globVars) {
		if (status != ExecutionStatus.NORMAL)
			return;
		if (statement.getProcess() != null) {
			su.nsk.iae.post.poST.Process process = (su.nsk.iae.post.poST.Process) statement.getProcess();
			String processName = process.getName();
			Constant processCode = globVars.getProcess(processName);
			currentState = new ComplexTerm(FunctionSymbol.setPstate, currentState, processCode, Constant.error);
		}
		else {
			currentState = new ComplexTerm(FunctionSymbol.setPstate, currentState, globVars.currentProcess, Constant.error);
		}
	}

	public Path addCondition(Term condition) {
		if (condition != null) {
			Term newPrecondition;
			if (precondition != null)
				newPrecondition = TermFactory.and(precondition, condition);
			else
				newPrecondition = condition;
			Path branch = new Path(newPrecondition, currentState);
			return branch;
		}
		else return this;
	}

	public void doExit() {
		if (status == ExecutionStatus.NORMAL)
			status = ExecutionStatus.EXIT;
	}

	public void doReturn() {
		if (status == ExecutionStatus.NORMAL)
			status = ExecutionStatus.RETURN;
	}

	public Term generateVerificationCondition(Term postcondition) {
		if (precondition != null) 
			return new ComplexTerm(FunctionSymbol.IMPL, precondition, postcondition);
		else
			return postcondition;
	}

	public Term generateVerificationCondition(FunctionSymbol loopinv) {
		return generateVerificationCondition(new ComplexTerm(loopinv, currentState));
	}

	public void toEnv() {
		currentState = TermFactory.toEnv(currentState);
	}

	public void assertion(Term assertion, VCGeneratorState globVars) {
		if (status == ExecutionStatus.NORMAL && assertion != null) {
			globVars.addVerificationCondition(generateVerificationCondition(assertion));
			if (precondition != null) 
				precondition = TermFactory.and(precondition, assertion);
			else
				precondition = assertion;
		}		
	}

	public ExecutionStatus getStatus() {
		return status;
	}
	
	public void resetStatus() {
		status = ExecutionStatus.NORMAL;
	}

	public Term getCurrentState() {
		return currentState;
	}

	public Term getPrecondition() {
		return precondition;
	}
	
	@Override
	public boolean equals(Object o) {
		if (o == this) 
			return true;
		else if (o == null || ! (o instanceof Path))
			return false;
		Path another = (Path) o;
		if (precondition == null)
			return another.precondition == null;
		if (currentState == null)
			return another.currentState == null;
		if (currentState instanceof Variable && another.currentState instanceof Variable)
			return status == another.status && precondition.equals(another.precondition);
		return status == another.status && precondition.equals(another.precondition) && currentState.equals(another.currentState);
	}
	
	@Override
	public int hashCode() {
		if (currentState instanceof Variable)
			return Objects.hash(precondition, status);
		return Objects.hash(precondition, currentState, status);
	}
	
	@Override
	public String toString() {
		return "{" + precondition.toString() + ", " + currentState.toString() + ", " + status.toString() + "}";
	}
}
