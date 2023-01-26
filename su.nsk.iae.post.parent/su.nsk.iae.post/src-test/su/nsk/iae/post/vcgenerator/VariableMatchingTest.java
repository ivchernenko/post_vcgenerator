package su.nsk.iae.post.vcgenerator;

import org.junit.Assert;
import org.junit.Test;

public class VariableMatchingTest {
	@Test
	public void testAddMatchingNewMatching() {
		VariableMatching matching = new VariableMatching();
		Variable var1 = new Variable("var1");
		Variable var2 =new Variable("var2");
		Assert.assertTrue(matching.addMatching(var1, var2));
	}
	
	@Test
	public void testAddMatchingSameMatching() {
		VariableMatching matching = new VariableMatching();
		Variable var1 = new Variable("var1");
		Variable var2 =new Variable("var2");
		matching.addMatching(var1,  var2);
		Assert.assertTrue(matching.addMatching(var1, var2));
	}
	
	@Test
	public void testAddMatchingConflictMatching() {
		VariableMatching matching = new VariableMatching();
		Variable var1 = new Variable("var1");
		Variable var2 =new Variable("var2");
		Variable var3 = new Variable("var3");
		matching.addMatching(var1,  var2);
		Assert.assertFalse(matching.addMatching(var1, var3));
		Assert.assertFalse(matching.addMatching(var3,  var1));
	}

}
