package su.nsk.iae.post.vcgenerator;

import java.util.List;

public class Term {
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

}
