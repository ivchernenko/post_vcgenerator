package su.nsk.iae.post.poST.impl;

import java.util.List;
import org.eclipse.emf.common.util.*;
import su.nsk.iae.post.poST.*;

public class StatementFactory {
	public static AssignmentStatement createVariableAssignmentStatement(SymbolicVariable variable, Expression value) {
		AssignmentStatement statement = new AssignmentStatementImpl();
		statement.setVariable(variable);
		statement.setValue(value);
		return statement;
	}

	public static AssignmentStatement createArrayAssignmentStatement(SymbolicVariable variable, Expression index, Expression value) {
		ArrayVariable array = new ArrayVariableImpl();
		array.setVariable(variable);
		array.setIndex(index);
		AssignmentStatement statement = new AssignmentStatementImpl();
		statement.setArray(array);
		statement.setValue(value);
		return statement;
	}

	public static IfStatement createIfStatement(Expression mainCond, List<Statement> mainStatement, List<Expression> elseIfCond,
			List<List<Statement>> elseIfStatements, List<Statement> elseStatement) {
		IfStatementImpl statement = new IfStatementImpl();
		statement.setMainCond(mainCond);
		statement.setMainStatement(createStatementList(mainStatement));
		if (elseIfCond != null)
			statement.elseIfCond = new BasicEList<>(elseIfCond);
		EList<StatementList> elseIfStatementLists = new BasicEList<>();
		if (elseIfStatements != null)
			for (List<Statement> elseIfStatement: elseIfStatements)
				elseIfStatementLists.add(createStatementList(elseIfStatement));
		statement.elseIfStatements = elseIfStatementLists;
		statement.setElseStatement(createStatementList(elseStatement));
		return statement;
	}

	public static CaseElement createCaseElement(List<Integer> caseListValues, List<Statement> statement) {
		CaseListImpl caseList = new CaseListImpl();
		EList<SignedInteger> caseListElement = new BasicEList<>();
		for (int element: caseListValues) {
			SignedInteger signedInteger = new SignedIntegerImpl();
			signedInteger.setISig(element < 0);
			signedInteger.setValue(Integer.toString(Math.abs(element)));
			caseListElement.add(signedInteger);
		}
		caseList.caseListElement = caseListElement;
		CaseElement caseElement = new CaseElementImpl();
		caseElement.setCaseList(caseList);
		caseElement.setStatement(createStatementList(statement));
		return caseElement;
	}

	public static CaseStatement createCaseStatement(Expression cond, List<CaseElement> caseElements, List<Statement> elseStatement) {
		CaseStatementImpl statement = new CaseStatementImpl();
		statement.setCond(cond);
		statement.setElseStatement(createStatementList(elseStatement));
		statement.caseElements = new BasicEList<>(caseElements);
		return statement;
	}

	public static ForStatement createForStatement(SymbolicVariable variable, Expression start, Expression end, Expression step,
			List<Statement> statement) {
		ForList forList = new ForListImpl();
		forList.setStart(start);
		forList.setEnd(end);
		forList.setStep(step);
		ForStatement forStatement = new ForStatementImpl();
		forStatement.setVariable(variable);
		forStatement.setForList(forList);
		forStatement.setStatement(createStatementList(statement));
		return forStatement;
	}

	public static WhileStatement createWhileStatement(Expression cond, List<Statement> statement) {
		WhileStatement whileStatement =new WhileStatementImpl();
		whileStatement.setCond(cond);
		whileStatement.setStatement(createStatementList(statement));
		return whileStatement;
	}

	public static RepeatStatement createRepeatStatement(List<Statement> statement, Expression cond) {
		RepeatStatement repeatStatement =new RepeatStatementImpl();
		repeatStatement.setCond(cond);
		repeatStatement.setStatement(createStatementList(statement));
		return repeatStatement;
	}

	public static StartProcessStatement createStartProcessStatement(su.nsk.iae.post.poST.Process process) {
		StartProcessStatement statement = new StartProcessStatementImpl();
		statement.setProcess(process);
		return statement;
	}

	public static StopProcessStatement createStopProcessStatement(su.nsk.iae.post.poST.Process process) {
		StopProcessStatement statement = new StopProcessStatementImpl();
		statement.setProcess(process);
		return statement;
	}

	public static ErrorProcessStatement createErrorProcessStatement(su.nsk.iae.post.poST.Process process) {
		ErrorProcessStatement statement = new ErrorProcessStatementImpl();
		statement.setProcess(process);
		return statement;
	}

	public static SetStateStatement createSetStateStatement(State state) {
		SetStateStatement statement = new SetStateStatementImpl();
		statement.setState(state);
		return statement;
	}

	public static SetStateStatement createSetNextStateStatement() {
		SetStateStatement statement = new SetStateStatementImpl();
		statement.setNext(true);
		return statement;
	}

	public static ResetTimerStatement createResetTimerStatement() {
		return new ResetTimerStatementImpl();
	}
	
	public static ExitStatement createExitStatement() {
		return new ExitStatementImpl();
	}
	
	public static SubprogramControlStatement createReturnStatement() {
		return new SubprogramControlStatementImpl();
	}

	public static TimeoutStatement createConstTimeout(Constant constant, List<Statement> statement) {
		TimeoutStatement timeout = new TimeoutStatementImpl();
		timeout.setConst(constant);
		timeout.setStatement(createStatementList(statement));
		return timeout;
	}

	public static TimeoutStatement createVariableTimeout(SymbolicVariable variable, List<Statement> statement) {
		TimeoutStatement timeout = new TimeoutStatementImpl();
		timeout.setVariable(variable);
		timeout.setStatement(createStatementList(statement));
		return timeout;
	}

	static StatementList createStatementList(List<Statement> statements) {
		StatementListImpl statementList = new StatementListImpl();
		if (statements != null)
			statementList.statements = new BasicEList<>(statements);
		return statementList;
	}

}
