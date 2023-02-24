package su.nsk.iae.post.vcgenerator;

import java.util.Iterator;
import java.util.List;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

public class Utils {
	public static boolean isSignedIntegerTypeName(String typeName) {
		return "SINT".equals(typeName) 
				|| "INT".equals(typeName) 
				|| "DINT".equals(typeName) 
				|| "LINT".equals(typeName);
	}
	
	public static boolean isUnsignedIntegerTypeName(String typeName) {
		return "USINT".equals(typeName)
				|| "UINT".equals(typeName)
				|| "UDINT".equals(typeName)
				|| "ULINT".equals(typeName)
				|| "TIME".equals(typeName)
				|| "BYTE".equals(typeName)
				|| "WORD".equals(typeName)
				|| "DWORD".equals(typeName)
				|| "LWORD".equals(typeName);
	}
	
	public static boolean isIntegerTypeName(String typeName) {
		return isSignedIntegerTypeName(typeName) || isUnsignedIntegerTypeName(typeName);
	}

	public static boolean isRealTypeName(String typeName) {
		return "REAL".equals(typeName) || "LREAL".equals(typeName);
	}
	
	static <T> Stream<T> asStream(Iterator<T> iterator) {
		Iterable<T> iterable = () -> iterator;
		return StreamSupport.stream(iterable.spliterator(), false);
	}

	public static int parseTime(String time) {
		int d = 0, h = 0, m = 0, s = 0, ms = 0;
		int index;
		if ((index = time.indexOf('d')) > 0) {
			d = Integer.parseInt(time.substring(0, index));
			time = time.substring(index + 1, time.length());
		}
		if ((index = time.indexOf('h')) > 0) {
			h = Integer.parseInt(time.substring(0, index));
			time = time.substring(index + 1, time.length());
		}
		if ((index = time.indexOf('h')) > 0) {
			h = Integer.parseInt(time.substring(0, index));
			time = time.substring(index + 1, time.length());
		}
		if ((index = time.indexOf('m')) > 0)
			if (index == time.length() - 1 || time.charAt(index + 1) != 's') {
				m = Integer.parseInt(time.substring(0, index));
				time = time.substring(index + 1, time.length());
			}
		if ((index = time.indexOf('s')) > 0)
			if (time.charAt(index - 1) != 'm') {
				s = Integer.parseInt(time.substring(0, index));
				time = time.substring(index + 1, time.length());
			}
		if ((index = time.indexOf("ms")) > 0) {
			ms = Integer.parseInt(time.substring(0, index));
			time = time.substring(index + 1, time.length());
		}
		return ms + 1000 * s + 1000 * 60 * m + 1000 * 60 * 60 * h + 1000 * 60 * 60 * 24 * d;
	}
}
