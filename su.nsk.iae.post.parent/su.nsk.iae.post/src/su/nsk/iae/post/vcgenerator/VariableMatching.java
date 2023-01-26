package su.nsk.iae.post.vcgenerator;

import java.util.*;

public class VariableMatching {
	Map<Variable, Variable> varMatching = new HashMap<>();
	Map<FunctionSymbol, FunctionSymbol> functionVarMatching = new HashMap<>();
	
	public boolean addMatching(Variable var1, Variable var2) {
		if (varMatching.containsKey(var1)) {
			Variable matched = varMatching.get(var1);
			return var2.equals(matched);
		}
		else if (varMatching.containsKey(var2))
			return false;
		else {
			varMatching.put(var1, var2);
			varMatching.put(var2, var1);
			return true;
		}
	}
	
	public boolean addMatching(FunctionSymbol var1, FunctionSymbol var2) {
		if (functionVarMatching.containsKey(var1)) {
			FunctionSymbol matched = functionVarMatching.get(var1);
			return var2.equals(matched);
		}
		else if (functionVarMatching.containsKey(var2))
			return false;
		else {
			functionVarMatching.put(var1, var2);
			functionVarMatching.put(var2, var1);
			return true;
		}
	}
}
