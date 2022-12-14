package su.nsk.iae.post.vcgenerator;

import java.util.List;


import java.util.ArrayList;

import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.poST.impl.*;
import su.nsk.iae.post.poST.impl.*;

public class Path {

	List<Term> precondition;
	Term currentState;
	ExecutionStatus status;

	public Path(List<Term> precondition, Term s0) {
		this.precondition = new ArrayList<>(precondition);
		currentState = s0;
		status = ExecutionStatus.NORMAL;
	}

	public void doAssignment(SymbolicVariable variable, Expression valueExpr, VCGeneratorState globVars) {
		if (status != ExecutionStatus.NORMAL)
			return;
		Term value = valueExpr.generateExpression(currentState, globVars);
		String varType = globVars.getVarType(variable.getName());
		Constant varNameCode = globVars.getVariable(variable.getName());
		if ("BOOL".equals(varType))
			currentState = new ComplexTerm(FunctionSymbol.setVarBool, currentState, varNameCode, value);
		else if (Utils.isIntegerTypeName(varType))
			currentState = new ComplexTerm(FunctionSymbol.setVarInt, currentState, varNameCode, value);
		else if (Utils.isRealTypeName(varType))
			currentState = new ComplexTerm(FunctionSymbol.setVarReal, currentState, varNameCode, value);
		else // TIME ((getVarInt currentState variable) - 1) div period + 1
			currentState = new ComplexTerm(FunctionSymbol.setVarInt, currentState, varNameCode, value);
	}

	public void increment(SymbolicVariable variable, AddExpression step, VCGeneratorState globVars) {		
		PrimaryExpression varExpr = new PrimaryExpressionImpl();
		varExpr.setVariable(variable);
		AddExpression newValue = new AddExpressionImpl();
		newValue.setAddOp(AddOperator.PLUS);
		newValue.setLeft(varExpr);
		newValue.setRight(step);
		doAssignment(variable, newValue, globVars);
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
			String varType = globVars.getVarType(variable.getName());
			Constant varNameCode = globVars.getVariable(variable.getName());
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
			currentState = new ComplexTerm(FunctionSymbol.setPstate, currentState, processCode, initialState);
		}
		else { // RESTART
			Constant initialState = globVars.getInitialState();
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
		Path branch = new Path(precondition, currentState);
		branch.precondition.add(condition);
		return branch;
	}

	public void doExit() {
		if (status == ExecutionStatus.NORMAL)
			status = ExecutionStatus.EXIT;
	}

	public void doReturn() {
		if (status == ExecutionStatus.NORMAL)
			status = ExecutionStatus.RETURN;
	}

	public Term generateVerificationCondition(FunctionSymbol loopinv) {
		Term preconditionConj = null;
		for (Term cond: precondition)
			if (preconditionConj == null) 
				preconditionConj = cond;
			else preconditionConj = new ComplexTerm(FunctionSymbol.AND, preconditionConj, cond);
		Term inv = new ComplexTerm(loopinv, new ComplexTerm(FunctionSymbol.toEnv, currentState));
		return new ComplexTerm(FunctionSymbol.IMPL, preconditionConj, inv);
	}

	public ExecutionStatus getStatus() {
		return status;
	}

	public Term getCurrentState() {
		return currentState;
	}



}
