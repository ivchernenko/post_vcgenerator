package su.nsk.iae.post.vcgenerator;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

public abstract class Term {
	DataType type;
	Object value;
	Term precondition;
	String name;

	public DataType getType() {
		return type;
	}

	public boolean isReal() {
		return type == DataType.REAL;
	}

	public Object getValue() {
		return value;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public Term getPrecondition() {
		return precondition;
	}

	public void addCondition(Term condition) {
		if (condition != null) {			
			if (precondition == null) 
				precondition = condition;
			else
				precondition = new ComplexTerm(FunctionSymbol.AND, precondition, condition);
		}
	}

	public String getValueString() {
		String name = this.name;
		this.name = null;
		String valueString = toString();
		this.name = name;
		return valueString;
	}
	
	public List<Variable> getFreeVariables(List<Variable> variables) {
		return variables.stream()
				.filter(v -> containsVariable(v))
				.collect(Collectors.toList());
	}
	
	public List<FunctionSymbol> getFreeFunctionVariables(List<FunctionSymbol> variables) {
		return variables.stream()
				.filter(v -> containsFunctionVariable(v))
				.collect(Collectors.toList());
	}
	
	abstract boolean equalsUpToMatching(Term term, VariableMatching matching);
	abstract boolean containsVariable(Variable v);
	abstract boolean containsFunctionVariable(FunctionSymbol f);
}
