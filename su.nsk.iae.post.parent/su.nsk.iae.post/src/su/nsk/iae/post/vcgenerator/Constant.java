package su.nsk.iae.post.vcgenerator;

public class Constant extends Term  {
	
	public Constant(DataType type, String name, Object value) {
		this.type = type;
		this.name = name;
		this.value = value;
	}
	
	public Constant(String name, Object value) {
		this.name = name;
		this.value = value;
	}
	
	public Constant(DataType type, Object value) {
		this(type, null, value);
	}
	public Constant(Object value) {
		this(null, null, value);
	}
	
	@Override
	public String toString() {
		if (name != null) 
			return name;
		else
			return value.toString();
	}
	
	@Override
	public boolean equals(Object o) {
		if (o == this)
			return true;
		if (o == null || ! (o instanceof Constant))
			return false;
		Constant c = (Constant) o;
		if (value == null)
			return false;				
		else return value.equals(c.value);
	}
	
	@Override
	public int hashCode() {
		if (value != null)
			return value.hashCode();
		else return 0;
	}
	
	@Override
	public boolean equalsUpToMatching(Term term, VariableMatching matching) {
		return equals(term);
	}
	
	public static Constant emptyState = new Constant("emptyState", null);
	public static Constant stop = new Constant("stop", 0);
	public static Constant error = new Constant( "error", 1);
	public static Constant True = new Constant(DataType.BOOL, "True", true);
	public static Constant False = new Constant(DataType.BOOL, "False", false);
}
