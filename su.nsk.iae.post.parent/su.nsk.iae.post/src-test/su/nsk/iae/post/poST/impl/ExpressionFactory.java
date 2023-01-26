package su.nsk.iae.post.poST.impl;

import su.nsk.iae.post.poST.*;

public class ExpressionFactory {
	public static Constant createIntConstant(int value) {
		SignedInteger integer = new SignedIntegerImpl();
		if (value < 0)
			integer.setISig(true);
		integer.setValue(Integer.toString(Math.abs(value)));
		IntegerLiteral intLiteral = new IntegerLiteralImpl();
		intLiteral.setValue(integer);
		Constant constant = new ConstantImpl();
		constant.setNum(intLiteral);
		return constant;
	}
	
	public static Constant createRealConstant(double value) {
		RealLiteral realLiteral = new RealLiteralImpl();
		if (value < 0)
			realLiteral.setRSig(true);
		realLiteral.setValue(Double.toString(Math.abs(value)));
		Constant constant = new ConstantImpl();
		constant.setNum(realLiteral);
		return constant;
	}
	
	public static Constant createTimeConstant(String value) {
		TimeLiteral timeLiteral = new TimeLiteralImpl();
		timeLiteral.setInterval(value);
		Constant constant = new ConstantImpl();
		constant.setTime(timeLiteral);
		return constant;
	}
	
	public static Constant createBooleanConstant(boolean value) {
		Constant constant = new ConstantImpl();
		constant.setOth(Boolean.toString(value));
		return constant;
	}
	
	public static SymbolicVariable createSymbolicVariable(String name) {
		SymbolicVariable variable = new SymbolicVariableImpl();
		variable.setName(name);
		return variable;
	}
	
	public static PrimaryExpression createConstantExpression(Constant constant) {
		PrimaryExpression expression = new PrimaryExpressionImpl();
		expression.setConst(constant);
		return expression;
	}
	
	public static PrimaryExpression createVariableExpression(SymbolicVariable variable) {
		PrimaryExpression expression = new PrimaryExpressionImpl();
		expression.setVariable(variable);
		return expression;
	}
	
	public static PrimaryExpression createArrayVariableExpression(SymbolicVariable variable, Expression index) {
		ArrayVariable array = new ArrayVariableImpl();
		array.setIndex(index);
		array.setVariable(variable);
		PrimaryExpression expression = new PrimaryExpressionImpl();
		expression.setArray(array);
		return expression;
	}
	
	public static PrimaryExpression createProcessStopExpression(su.nsk.iae.post.poST.Process process) {
		ProcessStatusExpression procStatusExpression = new ProcessStatusExpressionImpl();
		procStatusExpression.setProcess(process);
		procStatusExpression.setStop(true);
		PrimaryExpression expression = new PrimaryExpressionImpl();
		expression.setProcStatus(procStatusExpression);
		return expression;
	}
	
	public static PrimaryExpression createProcessErrorExpression(su.nsk.iae.post.poST.Process process) {
		ProcessStatusExpression procStatusExpression = new ProcessStatusExpressionImpl();
		procStatusExpression.setProcess(process);
		procStatusExpression.setError(true);
		PrimaryExpression expression = new PrimaryExpressionImpl();
		expression.setProcStatus(procStatusExpression);
		return expression;
	}
	
	public static PrimaryExpression createProcessInactiveExpression(su.nsk.iae.post.poST.Process process) {
		ProcessStatusExpression procStatusExpression = new ProcessStatusExpressionImpl();
		procStatusExpression.setProcess(process);
		procStatusExpression.setInactive(true);
		PrimaryExpression expression = new PrimaryExpressionImpl();
		expression.setProcStatus(procStatusExpression);
		return expression;
	}
	
	public static PrimaryExpression createProcessActiveExpression(su.nsk.iae.post.poST.Process process) {
		ProcessStatusExpression procStatusExpression = new ProcessStatusExpressionImpl();
		procStatusExpression.setProcess(process);
		procStatusExpression.setActive(true);
		PrimaryExpression expression = new PrimaryExpressionImpl();
		expression.setProcStatus(procStatusExpression);
		return expression;
	}
	
	public static PrimaryExpression createNestExpression(Expression nestExpr) {
		PrimaryExpression expression = new PrimaryExpressionImpl();
		expression.setNestExpr(nestExpr);
		return expression;
	}
	
	public static UnaryExpression createUnaryExpression(UnaryOperator op, PrimaryExpression right) {
		UnaryExpression expression = new UnaryExpressionImpl();
		expression.setUnOp(op);
		expression.setRight(right);
		return expression;
	}
	
	public static PowerExpression createPowerExpression(PowerExpression left, UnaryExpression right) {
		PowerExpression expression = new PowerExpressionImpl();
		expression.setLeft(left);
		expression.setRight(right);
		return expression;
	}
	
	public static MulExpression createMulExpression(MulOperator op, MulExpression left, PowerExpression right) {
		MulExpression expression = new MulExpressionImpl();
		expression.setMulOp(op);
		expression.setLeft(left);
		expression.setRight(right);
		return expression;
	}
	
	public static AddExpression createAddExpression(AddOperator op, AddExpression left, MulExpression right) {
		AddExpression expression = new AddExpressionImpl();
		expression.setAddOp(op);
		expression.setLeft(left);
		expression.setRight(right);
		return expression;
	}
	
	public static EquExpression createEquExpression(EquOperator op, EquExpression left, AddExpression right) {
		EquExpression expression = new EquExpressionImpl();
		expression.setEquOp(op);
		expression.setLeft(left);
		expression.setRight(right);
		return expression;
	}
	
	public static CompExpression createCompExpression(CompOperator op, CompExpression left, EquExpression right) {
		CompExpression expression = new CompExpressionImpl();
		expression.setCompOp(op);
		expression.setLeft(left);
		expression.setRight(right);
		return expression;
	}
	
	public static AndExpression createAndExpression(AndExpression left, CompExpression right) {
		AndExpression expression = new AndExpressionImpl();
		expression.setLeft(left);
		expression.setRight(right);
		return expression;
	}
	
	public static XorExpression createXorExpression(XorExpression left, AndExpression right) {
		XorExpression expression = new XorExpressionImpl();
		expression.setLeft(left);
		expression.setRight(right);
		return expression;
	}
	
	public static Expression createOrExpression(Expression left, XorExpression right) {
		Expression expression = new ExpressionImpl();
		expression.setLeft(left);
		expression.setRight(right);
		return expression;
	}

}
