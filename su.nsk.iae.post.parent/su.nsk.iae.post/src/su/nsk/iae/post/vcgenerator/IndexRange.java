package su.nsk.iae.post.vcgenerator;

public class IndexRange {
	private Term start, end;
	
	public IndexRange(Term start, Term end) {
		this.start = start;
		this.end = end;
	}
	
	public Term contains(Term index) {
		return TermFactory.and(TermFactory.leq(start, index), TermFactory.leq(index, end));
	}
	
	public Term get(int index) {
		return TermFactory.plus(start, new Constant(index));
	}
	
	public int length() {
		if (this.start.getValue() == null || this.end.getValue() == null)
			return -1;
		int start = (Integer) this.start.getValue();
		int end = (Integer) this.end.getValue();
		return end - start + 1;
	}
	
	public Term getStart() {
		return start;
	}
}
