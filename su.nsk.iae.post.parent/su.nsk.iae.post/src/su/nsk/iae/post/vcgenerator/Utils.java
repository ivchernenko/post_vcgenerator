package su.nsk.iae.post.vcgenerator;

import java.util.Iterator;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

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
	
	static <T> Stream<T> asStream(Iterator<T> iterator) {
		Iterable<T> iterable = () -> iterator;
		return StreamSupport.stream(iterable.spliterator(), false);
	}
}
