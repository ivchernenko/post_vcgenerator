package su.nsk.iae.post.vcgenerator;

public class FunctionSymbol {
	
	private String name;
	boolean infix;
	boolean isVariable;
	
	FunctionSymbol(String name, boolean isVariable, boolean infix) {
		this.name = name;
		this.isVariable = isVariable;
		this.infix = infix;
	}
	
	public FunctionSymbol(String name, boolean variable) {
		this(name, variable, false);
	}
	
	@Override
	public String toString() {
		return name;
	}
	
	public boolean isVariable() {
		return isVariable;
	}
	
	public static final FunctionSymbol PLUS = new FunctionSymbol("+", false, true);
	public static final FunctionSymbol MINUS = new FunctionSymbol("-", false, true);
	public static final FunctionSymbol UNMINUS = new FunctionSymbol("-", false, false);
	public static final FunctionSymbol MUL = new FunctionSymbol("*", false, true);
	public static final FunctionSymbol DIV = new FunctionSymbol("div", false, true);
	public static final FunctionSymbol RDIV = new FunctionSymbol("/", false, true);
	public static final FunctionSymbol MOD = new FunctionSymbol("mod", false, true);
	public static final FunctionSymbol POW = new FunctionSymbol("^", false, true);
	public static final FunctionSymbol LESS = new FunctionSymbol("<", false, true);
	public static final FunctionSymbol GREATER = new FunctionSymbol(">", false, true);
	public static final FunctionSymbol LEQ = new FunctionSymbol("<=", false, true);
	public static final FunctionSymbol GEQ = new FunctionSymbol(">=", false, true);
	public static final FunctionSymbol EQ = new FunctionSymbol("=", false, true);
	public static final FunctionSymbol NOTEQ = new FunctionSymbol("\\<noteq>", false, true);
	public static final FunctionSymbol AND = new FunctionSymbol("/\\", false, true);
	public static final FunctionSymbol OR = new FunctionSymbol("\\/", false, true);
	public static final FunctionSymbol NOT = new FunctionSymbol("\\<not>", false, false);
	public static final FunctionSymbol IMPL = new FunctionSymbol("-->", false, true);
	
	// State constructors
	public static final FunctionSymbol toEnv = new FunctionSymbol("toEnv", false, false);
	public static final FunctionSymbol toCon = new FunctionSymbol("toCon", false, false);
	public static final FunctionSymbol setVarBool = new FunctionSymbol("setVarBool", false, false);
	public static final FunctionSymbol setVarInt = new FunctionSymbol("setVarInt", false, false);
	public static final FunctionSymbol setVarReal = new FunctionSymbol("setVarReal", false, false);
	public static final FunctionSymbol setVarAny = new FunctionSymbol("setVarAny", false, false);
	public static final FunctionSymbol setPstate = new FunctionSymbol("setPstate", false, false);
	public static final FunctionSymbol reset = new FunctionSymbol("reset", false, false);
	public static final FunctionSymbol setVarArrayBool = new FunctionSymbol("setVarArrayBool", false, false);
	public static final FunctionSymbol setVarArrayInt = new FunctionSymbol("setVarArrayInt", false, false);
	public static final FunctionSymbol setVarArrayReal = new FunctionSymbol("setVarArrayReal", false, false);
	
	//State functions
	public static final FunctionSymbol getVarBool = new FunctionSymbol("getVarBool", false, false);
	public static final FunctionSymbol getVarInt = new FunctionSymbol("getVarInt", false, false);
	public static final FunctionSymbol getvarReal = new FunctionSymbol("getVarReal", false, false);
	public static final FunctionSymbol getPstate = new FunctionSymbol("getPstate", false, false);
	public static final FunctionSymbol ltime = new FunctionSymbol("ltime", false, false);
	public static final FunctionSymbol getVarArrayBool = new FunctionSymbol("getVarArrayBool", false, false);
	public static final FunctionSymbol getVarArrayInt = new FunctionSymbol("getVarArrayInt", false, false);
	public static final FunctionSymbol getVarArrayReal = new FunctionSymbol("getVarArrayReal", false, false);	
}
