package su.nsk.iae.post.vcgenerator;

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
}
