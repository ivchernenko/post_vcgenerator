package su.nsk.iae.post.vcgenerator;

public class Term {
	DataType type;
	
	public DataType getType() {
		return type;
	}
	
	public boolean isReal() {
		return type == DataType.REAL;
	}

}
