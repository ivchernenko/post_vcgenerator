package su.nsk.iae.post.vcgenerator;

public class Constant extends Term  {
	
	private String name;
	
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
	
	public String getName() {
		return name;
	}
	
	@Override
	public String toString() {
		if (name != null) 
			return name;
		else
			return value.toString();
	}
	
	public static Constant emptyState = new Constant("emptyState", null);
	public static Constant stop = new Constant("stop", 0);
	public static Constant error = new Constant( "error", 1);

}
