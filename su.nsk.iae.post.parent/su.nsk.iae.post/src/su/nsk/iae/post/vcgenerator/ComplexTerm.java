package su.nsk.iae.post.vcgenerator;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

public class ComplexTerm extends Term {

	private FunctionSymbol function;
	Term[] args;
	
	public ComplexTerm(DataType type, Object value, Term precondition, FunctionSymbol f, Term... args) {
		this.type = type;
		this.value = value;
		this.precondition = precondition;
		this.function = f;
		this.args = args;
		for (int i = 0; i < args.length; ++i)
			if (args[i] == null)
				throw new NullPointerException("Null subterm at index " + i + ". Null subterms are not allowed");
	}

	public ComplexTerm(DataType type, Object value, FunctionSymbol f, Term... args) {
		this(type, value, null, f, args);
	}
	
	public ComplexTerm(DataType type, FunctionSymbol f, Term... args) {
		this(type, null, f, args);
	}

	public ComplexTerm(FunctionSymbol f, Term... args) {
		this(null, f, args);
	}
	
	public FunctionSymbol getFunction() {
		return function;
	}
	
	public Term[] getArgs() {
		return args;
	}

	@Override
	public String toString() {
		if (name != null)
			return name;
		else if (function.infix) {
			StringBuilder sb = new StringBuilder("(");
			sb.append(args[0].toString());
			sb.append(" " + function.toString());
			sb.append(" " + args[1].toString());
			return sb.append(")").toString();
		}
		else {
			StringBuilder sb = new StringBuilder("(" + function.toString());
			for (Term arg: args) 
				sb.append(" " + arg.toString());
			return sb.append(")").toString();
		}
	}
	
	@Override
	public boolean equalsUpToMatching(Term term, VariableMatching matching) {
		if (term == null || ! (term instanceof ComplexTerm))
			return false;
		ComplexTerm another = (ComplexTerm) term;
		if (! function.isVariable()) {
			if (! function.equals(another.function))
				return false;
		}
		else
			if (! another.function.isVariable()) // Variable and not variable
				return false;
			else
				if (! matching.addMatching(function, another.function)) // Function variable conflict
					return false;
		if (args.length != another.args.length)
			return false;
		for (int i = 0; i < args.length; ++i)
			if (! args[i].equalsUpToMatching(another.args[i], matching))
				return false;
		return true;
	}
	
	@Override
	public boolean equals(Object o) {
		if (o == this)
			return true;
		if (o == null || ! (o instanceof Term))
			return false;
		Term term = (Term) o;
		return equalsUpToMatching(term, new VariableMatching());
	}
	
	@Override
	boolean containsVariable(Variable v) {
		for (Term arg: args)
			if (arg.containsVariable(v))
				return true;
		return false;
	}
	
	@Override
	boolean containsFunctionVariable(FunctionSymbol f) {
		if (function.equals(f))
			return true;
		for (Term arg: args)
			if (arg.containsFunctionVariable(f))
				return true;
		return false;
	}
}
