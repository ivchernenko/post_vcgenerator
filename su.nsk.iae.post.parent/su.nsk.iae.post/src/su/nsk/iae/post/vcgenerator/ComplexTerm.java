package su.nsk.iae.post.vcgenerator;

public class ComplexTerm extends Term {

	private FunctionSymbol function;
	Term[] args;

	public ComplexTerm(DataType type, FunctionSymbol f, Term... args) {
		this.type = type;
		this.function = f;
		this.args = args;
	}

	public ComplexTerm(FunctionSymbol f, Term... args) {
		this(null, f, args);
	}

	@Override
	public String toString() {
		if (function.infix) {
			StringBuilder sb = new StringBuilder("(");
			sb.append(args[0].toString());
			sb.append(" " + function.toString());
			sb.append(" " + args[1].toString());
			return sb.append(")").toString();
		}
		else {
			StringBuilder sb = new StringBuilder("(" + function.toString());
			for (Term arg: args) 
				sb.append(" " + arg.toString());
			return sb.append(")").toString();
		}
	}

}
