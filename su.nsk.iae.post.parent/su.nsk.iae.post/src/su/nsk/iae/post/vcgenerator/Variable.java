package su.nsk.iae.post.vcgenerator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Variable extends Term {
	
	private String name;
	
	public Variable(String name) {
		this.name = name;
	}
	
	@Override
	public String toString() {
		return name;
	}
	
	@Override
	public boolean equalsUpToMatching(Term term, VariableMatching matching) {
		if (term == null || ! (term instanceof Variable))
			return false;
		Variable v = (Variable) term;			
		return matching.addMatching(this, v);
	}
	
	@Override
	boolean containsVariable(Variable v) {
		return this.equals(v);
	}
	
	@Override
	boolean containsFunctionVariable(FunctionSymbol f) {
		return false;
	}
}
