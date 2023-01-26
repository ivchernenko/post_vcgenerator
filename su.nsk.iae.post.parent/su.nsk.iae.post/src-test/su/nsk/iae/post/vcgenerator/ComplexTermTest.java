package su.nsk.iae.post.vcgenerator;

import org.junit.Assert;
import org.junit.Test;

public class ComplexTermTest {
	@Test
	public void testEqualsUpToMatchingNull() {
		ComplexTerm term1 = new ComplexTerm(FunctionSymbol.AND, new Variable("a"), new Variable("b"));
		Term term2 = null;
		VariableMatching matching = new VariableMatching();
		Assert.assertFalse(term1.equalsUpToMatching(term2, matching));
	}
	
	@Test
	public void testEqualsUpToMatchingTypeMismatch() {
		ComplexTerm term1 = new ComplexTerm(FunctionSymbol.AND, new Variable("a"), new Variable("b"));
		Term term2 = new Variable("a");
		VariableMatching matching = new VariableMatching();
		Assert.assertFalse(term1.equalsUpToMatching(term2, matching));
	}
	
	@Test
	public void testEqualsUpToMatchingFirstFunctionNotVariableFunctionsNotEqual() {
		ComplexTerm term1 = new ComplexTerm(FunctionSymbol.AND, new Variable("a"), new Variable("b"));
		Term term2 = new ComplexTerm(FunctionSymbol.OR, new Variable("a"), new Variable("b"));
		VariableMatching matching = new VariableMatching();
		Assert.assertFalse(term1.equalsUpToMatching(term2, matching));
	}
	
	@Test
	public void testEqualsUpToMatchingFirstFunctionNotVariableSecondFunctionVariable() {
		ComplexTerm term1 = new ComplexTerm(new FunctionSymbol("f", true), new Variable("a"), new Variable("b"));
		Term term2 = new ComplexTerm(FunctionSymbol.AND, new Variable("a"), new Variable("b"));
		VariableMatching matching = new VariableMatching();
		Assert.assertFalse(term1.equalsUpToMatching(term2, matching));
	}
	
	@Test
	public void testEqualsUpToMatchingFunctionVariableConflict() {
		FunctionSymbol f = new FunctionSymbol("f", true);
		FunctionSymbol g = new FunctionSymbol("g", true);
		FunctionSymbol h = new FunctionSymbol("h", true);
		ComplexTerm term1 = new ComplexTerm(f, new Variable("a"), new Variable("b"));
		Term term2 = new ComplexTerm(h, new Variable("a"), new Variable("b"));
		VariableMatching matching = new VariableMatching();
		matching.addMatching(f, g);
		Assert.assertFalse(term1.equalsUpToMatching(term2, matching));
	}
	
	@Test
	public void testEqualsUpToMatchingDifferentNumberOfArguments() {
		Term term1 = new ComplexTerm(FunctionSymbol.AND, new Variable("a"), new Variable("b"));
		Term term2 = new ComplexTerm(FunctionSymbol.AND, new Variable("a"), new Variable("b"), new Variable("c"));
		VariableMatching matching = new VariableMatching();
		Assert.assertFalse(term1.equalsUpToMatching(term2, matching));
	}
	
	@Test
	public void testEqualsUpToMatchingArgumentsNotEqual() {
		Variable a = new Variable("a");
		Variable b = new Variable("b");
		Variable c = new Variable("c");
		Term term1 = new ComplexTerm(FunctionSymbol.NOT, a);
		Term term2 = new ComplexTerm(FunctionSymbol.NOT, c);
		VariableMatching matching = new VariableMatching();
		matching.addMatching(a, b);
		Assert.assertFalse(term1.equalsUpToMatching(term2, matching));
	}
	
	@Test
	public void testEqualsUpToMatchingEqualsFunctionsNotVariables() {
		Term term1 = new ComplexTerm(FunctionSymbol.AND, new Variable("a"), new Variable("b"));
		Term term2 = new ComplexTerm(FunctionSymbol.AND, new Variable("a"), new Variable("b"));
		VariableMatching matching = new VariableMatching();
		Assert.assertTrue(term1.equalsUpToMatching(term2, matching));
	}
	
	@Test
	public void testEqualsUpToMatchingFunctionsVariables() {
		Term term1 = new ComplexTerm(new FunctionSymbol("f", true), new Variable("a"), new Variable("b"));
		Term term2 = new ComplexTerm(new FunctionSymbol("g", true), new Variable("a"), new Variable("b"));
		VariableMatching matching = new VariableMatching();
		Assert.assertTrue(term1.equalsUpToMatching(term2, matching));
	}

}
