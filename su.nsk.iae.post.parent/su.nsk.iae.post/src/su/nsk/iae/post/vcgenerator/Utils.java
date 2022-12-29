package su.nsk.iae.post.vcgenerator;

public class Utils {
	public static boolean isIntegerTypeName(String typeName) {
		return "SINT".equals(typeName) 
				|| "INT".equals(typeName) 
				|| "DINT".equals(typeName) 
				|| "LINT".equals(typeName)
				|| "USINT".equals(typeName)
				|| "UINT".equals(typeName)
				|| "UDINT".equals(typeName)
				|| "ULINT".equals(typeName);
	}

	public static boolean isRealTypeName(String typeName) {
		return "REAL".equals(typeName) || "LREAL".equals(typeName);
	}
}
