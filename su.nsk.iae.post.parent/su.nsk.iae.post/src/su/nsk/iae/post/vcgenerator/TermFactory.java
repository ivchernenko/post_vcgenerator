package su.nsk.iae.post.vcgenerator;

import java.util.*;

public class TermFactory {
	public static Term  plus(Term left, Term right) {
		DataType resultType;
		if (left.isReal() || right.isReal())
			resultType = DataType.REAL;
		else
			resultType = DataType.INT;
		return new ComplexTerm(resultType, FunctionSymbol.PLUS, left, right);
	}
	
	public static Term  minus(Term left, Term right) {
		DataType resultType;
		if (left.isReal() || right.isReal())
			resultType = DataType.REAL;
		else
			resultType = DataType.INT;
		return new ComplexTerm(resultType, FunctionSymbol.MINUS, left, right);
	}
	
	public static Term unminus(Term right) {
		 return new ComplexTerm(right.getType(), FunctionSymbol.UNMINUS, right);
	}
	
	public static Term  mul(Term left, Term right) {
		DataType resultType;
		if (left.isReal() || right.isReal())
			resultType = DataType.REAL;
		else
			resultType = DataType.INT;
		return new ComplexTerm(resultType, FunctionSymbol.MUL, left, right);
	}
	
	public static Term  rdiv(Term left, Term right) {
		return new ComplexTerm(DataType.REAL, FunctionSymbol.RDIV, left, right);
	}
	
	public static Term  div(Term left, Term right) {
		return new ComplexTerm(DataType.INT, FunctionSymbol.DIV, left, right);
	}
	
	public static Term  mod(Term left, Term right) {
		return new ComplexTerm(DataType.INT, FunctionSymbol.MOD, left, right);
	}
	
	public static Term  pow(Term left, Term right) {
		return new ComplexTerm(DataType.REAL, FunctionSymbol.POW, left, right);
	}
	
	public static Term  less(Term left, Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.LESS, left, right);
	}
	
	public static Term  greater(Term left, Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.GREATER, left, right);
	}
	
	public static Term  leq(Term left, Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.LEQ, left, right);
	}
	
	public static Term  geq(Term left, Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.GEQ, left, right);
	}
	
	public static Term  eq(Term left, Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.EQ, left, right);
	}
	
	public static Term  noteq(Term left, Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.NOTEQ, left, right);
	}
	
	public static Term  and(Term left, Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.AND, left, right);
	}
	
	public static Term  and(Term ... args) {
		Term conj = null;
		for (Term arg: args)
			if (conj == null)
				conj = arg;
			else
				conj = and(conj, arg);
		return conj;
	}
	
	public static Term  or(Term left, Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.OR, left, right);
	}
	
	public static Term  not(Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.NOT, right);
	}
	
	public static Term  impl(Term left, Term right) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.IMPL, left, right);
	}
	
	public static Term  toEnv(Term state) {
		return new ComplexTerm(FunctionSymbol.toEnv, state);
	}
	
	public static Term  toCon(Term state) {
		return new ComplexTerm(FunctionSymbol.toCon, state);
	}
	
	public static Term  setVarBool(Term state, Constant variable, Term value) {
		return new ComplexTerm(FunctionSymbol.setVarBool, state, variable, value);
	}
	
	public static Term  setVarInt(Term state, Constant variable, Term value) {
		return new ComplexTerm(FunctionSymbol.setVarInt, state, variable, value);
	}
	
	public static Term  setVarReal(Term state, Constant variable, Term value) {
		return new ComplexTerm(FunctionSymbol.setVarReal, state, variable, value);
	}
	
	public static Term  setVarArrayBool(Term state, Constant variable, Term index, Term value) {
		return new ComplexTerm(FunctionSymbol.setVarArrayBool, state, variable, index, value);
	}
	
	public static Term  setVarArrayInt(Term state, Constant variable, Term index, Term value) {
		return new ComplexTerm(FunctionSymbol.setVarArrayInt, state, variable, index, value);
	}
	
	public static Term  setVarArrayReal(Term state, Constant variable, Term index, Term value) {
		return new ComplexTerm(FunctionSymbol.setVarArrayReal, state, variable, index, value);
	}
	
	public static Term  setVarAny(Term ... args) {
		return new ComplexTerm(FunctionSymbol.setVarAny, args);
	}
	
	public static Term  setPstate(Term state, Constant process, Constant pstate) {
		return new ComplexTerm(FunctionSymbol.setPstate, state, process, pstate);
	}
	
	public static Term  reset(Term state, Constant process) {
		return new ComplexTerm(FunctionSymbol.reset, state, process);
	}
	
	public static Term  getVarBool(Term state, Constant variable) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.getVarBool, state, variable);
	}
	
	public static Term  getVarInt(Term state, Constant variable) {
		return new ComplexTerm(DataType.INT, FunctionSymbol.getVarInt, state, variable);
	}
	
	public static Term  getVarReal(Term state, Constant variable) {
		return new ComplexTerm(DataType.REAL, FunctionSymbol.getvarReal, state, variable);
	}
	
	public static Term  getVarArrayBool(Term state, Constant variable, Term index) {
		return new ComplexTerm(DataType.BOOL, FunctionSymbol.getVarArrayBool, state, variable, index);
	}
	
	public static Term  getVarArrayInt(Term state, Constant variable, Term index) {
		return new ComplexTerm(DataType.INT, FunctionSymbol.getVarArrayInt, state, variable, index);
	}
	
	public static Term  getVarArrayReal(Term state, Constant variable, Term index) {
		return new ComplexTerm(DataType.REAL, FunctionSymbol.getVarArrayReal, state, variable, index);
	}
	
	public static Term  getPstate(Term state, Constant process) {
		return new ComplexTerm(FunctionSymbol.getPstate, state, process);
	}
	
	public static Term  ltime(Term state, Constant process) {
		return new ComplexTerm(FunctionSymbol.ltime, state, process);
	}
	
	public static Term setVar(String varType, Term state, Constant variable, Term value) {
		if ("BOOL".equals(varType))
			return setVarBool(state, variable, value);
		else if (Utils.isIntegerTypeName(varType))
			return setVarInt(state, variable, value);
		else if (Utils.isRealTypeName(varType))
			return setVarReal(state, variable, value);
		else // TIME 
			return setVarInt(state, variable, value);
	}
	
	public static Term setVarArray(String varType, Term state, Constant variable, Term index, Term value) {
		if ("BOOL".equals(varType))
			return setVarArrayBool(state, variable, index, value);
		else if (Utils.isIntegerTypeName(varType))
			return setVarArrayInt(state, variable, index, value);
		else if (Utils.isRealTypeName(varType))
			return setVarArrayReal(state, variable, index, value);
		else // TIME 
			return setVarArrayInt(state, variable, index, value);
	}
	
	public static Term getVar(String varType, Term state, Constant variable) {
		if ("BOOL".equals(varType))
			return getVarBool(state, variable);
		else if (Utils.isIntegerTypeName(varType))
			return getVarInt(state, variable);
		else if (Utils.isRealTypeName(varType))
			return getVarReal(state, variable);
		else // TIME 
			return getVarInt(state, variable);
	}
	
	public static Term getVarArray(String varType, Term state, Constant variable, Term index) {
		Term value;
		if ("BOOL".equals(varType))
			value = getVarArrayBool(state, variable, index);
		else if (Utils.isIntegerTypeName(varType))
			value = getVarArrayInt(state, variable, index);
		else if (Utils.isRealTypeName(varType))
			value = getVarArrayReal(state, variable, index);
		else // TIME 
			value = getVarArrayInt(state, variable, index);
		return value;
	}
}
