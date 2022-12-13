package su.nsk.iae.post.vcgenerator;

import java.util.*;

import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.Constant;

public class VCGenerator {
	VCGeneratorState globVars = new VCGeneratorState();
	
	List<Path> generateTimeout(Path path, TimeoutStatement statement) {
		if (path.getStatus() != ExecutionStatus.NORMAL) {
			List<Path> result = new ArrayList<>();
			result.add(path);
			return result;
		}
		Term time;
		if(statement.getConst() != null) {
			int timeInMilliseconds = (Integer) statement.getConst().generateConstant().getValue();
			int timeInCycles;
			if (timeInMilliseconds % globVars.period == 0)
				timeInCycles = timeInMilliseconds / globVars.period;
			else
				timeInCycles = timeInMilliseconds / globVars.period + 1;
			time = new Constant(timeInCycles);
		}
		else { // Variable
			Term symComputedVar = statement.getVariable().generateVariable(path.getCurrentState(), globVars);
			time = new ComplexTerm(
					FunctionSymbol.PLUS,
					new ComplexTerm(
							FunctionSymbol.DIV,
							new ComplexTerm(FunctionSymbol.MINUS, symComputedVar, new Constant(1)),
							new Constant(globVars.period)),
					new Constant(1));
		}
		Term timeExpiredCondition = new ComplexTerm(
				FunctionSymbol.LEQ,
				time,
				new ComplexTerm(FunctionSymbol.ltime, path.getCurrentState(), globVars.currentProcess));
		Path expired = path.addCondition(timeExpiredCondition);
		Path notExpired = path.addCondition(new ComplexTerm(FunctionSymbol.NOT, timeExpiredCondition));
		List<Path> result = statement.getStatement().applyTo(expired, globVars);
		result.add(notExpired);
		return result;
	}
	
	List<Path> generateState(Path path, State state) {
		if (path.getStatus() != ExecutionStatus.NORMAL) {
			List<Path> result = new ArrayList<>();
			result.add(path);
			return result;
		}
		Term processInState = new ComplexTerm(
				FunctionSymbol.EQ,
				new ComplexTerm(
						FunctionSymbol.getPstate,
						path.getCurrentState(),
						globVars.currentProcess),
				globVars.getCurrentState());
		path = path.addCondition(processInState);
		List<Path> pathsBeforeTimeout = state.getStatement().applyTo(path, globVars);
		if (state.getTimeout() == null)
			return pathsBeforeTimeout;
		else {
			List<Path> result = new ArrayList<>();
			for (Path p: pathsBeforeTimeout)
				result.addAll(generateTimeout(p, state.getTimeout()));
			return result;
		}
	}

}
