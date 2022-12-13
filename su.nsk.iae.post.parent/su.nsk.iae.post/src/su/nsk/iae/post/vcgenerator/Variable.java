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

}
