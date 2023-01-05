package su.nsk.iae.post.vcgenerator;

public class Term {
	DataType type;
	Object value;
	
	public DataType getType() {
		return type;
	}
	
	public boolean isReal() {
		return type == DataType.REAL;
	}
	
	public Object getValue() {
		return value;
	}

}
