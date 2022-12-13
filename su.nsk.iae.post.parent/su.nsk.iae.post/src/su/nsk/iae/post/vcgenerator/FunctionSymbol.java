package su.nsk.iae.post.vcgenerator;

public class FunctionSymbol {
	
	private String name;
	boolean infix;
	
	FunctionSymbol(String name, boolean infix) {
		this.name = name;
		this.infix = infix;
	}
	
	@Override
	public String toString() {
		return name;
	}
	
	public static final FunctionSymbol PLUS = new FunctionSymbol("+", true);
	public static final FunctionSymbol MINUS = new FunctionSymbol("-", true);
	public static final FunctionSymbol UNMINUS = new FunctionSymbol("-", false);
	public static final FunctionSymbol MUL = new FunctionSymbol("*", true);
	public static final FunctionSymbol DIV = new FunctionSymbol("div", true);
	public static final FunctionSymbol RDIV = new FunctionSymbol("/", true);
	public static final FunctionSymbol MOD = new FunctionSymbol("mod", true);
	public static final FunctionSymbol POW = new FunctionSymbol("^", true);
	public static final FunctionSymbol LESS = new FunctionSymbol("<", true);
	public static final FunctionSymbol GREATER = new FunctionSymbol(">", true);
	public static final FunctionSymbol LEQ = new FunctionSymbol("<=", true);
	public static final FunctionSymbol GEQ = new FunctionSymbol(">=", true);
	public static final FunctionSymbol EQ = new FunctionSymbol("=", true);
	public static final FunctionSymbol NOTEQ = new FunctionSymbol("\\<noteq>", true);
	public static final FunctionSymbol AND = new FunctionSymbol("/\\", true);
	public static final FunctionSymbol OR = new FunctionSymbol("\\/", true);
	public static final FunctionSymbol NOT = new FunctionSymbol("\\<not>", false);
	public static final FunctionSymbol IMPL = new FunctionSymbol("-->", true);
	
	// State constructors
	public static final FunctionSymbol toEnv = new FunctionSymbol("toEnv", false);
	public static final FunctionSymbol toCon = new FunctionSymbol("toCon", false);
	public static final FunctionSymbol setVarBool = new FunctionSymbol("setVarBool", false);
	public static final FunctionSymbol setVarInt = new FunctionSymbol("setVarInt", false);
	public static final FunctionSymbol setVarDouble = new FunctionSymbol("setVarDouble", false);
	public static final FunctionSymbol setVarAny = new FunctionSymbol("setVarAny", false);
	public static final FunctionSymbol setPstate = new FunctionSymbol("setPstate", false);
	public static final FunctionSymbol reset = new FunctionSymbol("reset", false);
	
	//State functions
	public static final FunctionSymbol getVarBool = new FunctionSymbol("getVarBool", false);
	public static final FunctionSymbol getVarInt = new FunctionSymbol("getVarInt", false);
	public static final FunctionSymbol getvarReal = new FunctionSymbol("getVarDouble", false);
	public static final FunctionSymbol getPstate = new FunctionSymbol("getPstate", false);
	public static final FunctionSymbol ltime = new FunctionSymbol("ltime", false);
	
	
}
