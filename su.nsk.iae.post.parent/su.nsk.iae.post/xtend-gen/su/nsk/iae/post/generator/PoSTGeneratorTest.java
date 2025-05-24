package su.nsk.iae.post.generator;

import com.google.inject.Injector;
import com.google.inject.Provider;
import java.util.ArrayList;
import org.eclipse.xtend2.lib.StringConcatenation;
import org.eclipse.xtext.testing.XtextRunner;
import org.eclipse.xtext.testing.util.ParseHelper;
import org.eclipse.xtext.xbase.lib.CollectionLiterals;
import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import su.nsk.iae.post.PoSTStandaloneSetup;
import su.nsk.iae.post.poST.Model;
import su.nsk.iae.post.vcgenerator.ComplexTerm;
import su.nsk.iae.post.vcgenerator.Constant;
import su.nsk.iae.post.vcgenerator.FunctionSymbol;
import su.nsk.iae.post.vcgenerator.Term;
import su.nsk.iae.post.vcgenerator.TermFactory;
import su.nsk.iae.post.vcgenerator.Variable;

@RunWith(XtextRunner.class)
@SuppressWarnings("all")
public class PoSTGeneratorTest {
  private Injector injector = new PoSTStandaloneSetup().createInjectorAndDoEMFRegistration();

  ParseHelper<Model> parser = ((ParseHelper) ((Provider) this.injector.<ParseHelper>getProvider(ParseHelper.class)).get());

  private PoSTGenerator generator = new PoSTGenerator();

  @Test
  public void testGenerateVariableCode() {
    final Constant varCode = new Constant("a", Integer.valueOf(2));
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("abbreviation a :: variable where \"a \\<equiv> (Suc (Suc 0))\"");
    _builder.newLine();
    final String expected = _builder.toString();
    final String result = this.generator.generateCode("variable", varCode);
    Assert.assertEquals(expected, result);
  }

  @Test
  public void testGenerateProcessCode() {
    final Constant varCode = new Constant("p", Integer.valueOf(2));
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("abbreviation p :: process where \"p \\<equiv> (Suc (Suc 0))\"");
    _builder.newLine();
    final String expected = _builder.toString();
    final String result = this.generator.generateCode("process", varCode);
    Assert.assertEquals(expected, result);
  }

  @Test
  public void testGenerateProcessStateCode() {
    final Constant varCode = new Constant("s", Integer.valueOf(2));
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("abbreviation s :: pstate where \"s \\<equiv> (Suc (Suc 0))\"");
    _builder.newLine();
    final String expected = _builder.toString();
    final String result = this.generator.generateCode("pstate", varCode);
    Assert.assertEquals(expected, result);
  }

  @Test
  public void testGenerateConstant() {
    final Constant constant = new Constant("a", Integer.valueOf(2));
    final String type = "SINT";
    StringConcatenation _builder = new StringConcatenation();
    _builder.append("abbreviation a :: int where \"a \\<equiv> 2\"");
    _builder.newLine();
    final String expected = _builder.toString();
    final String result = this.generator.generateConstant(type, constant);
    Assert.assertEquals(expected, result);
  }

  @Test
  public void testGenerateVC() {
    final FunctionSymbol inv = new FunctionSymbol("inv", true);
    final Variable s0 = new Variable("s0");
    ComplexTerm _complexTerm = new ComplexTerm(inv, s0);
    Term _env = TermFactory.toEnv(s0);
    ComplexTerm _complexTerm_1 = new ComplexTerm(inv, _env);
    final Term vc = TermFactory.impl(_complexTerm, _complexTerm_1);
    final int num = 1;
    final ArrayList<FunctionSymbol> functionParams = CollectionLiterals.<FunctionSymbol>newArrayList(inv);
    final ArrayList<Variable> variableParams = CollectionLiterals.<Variable>newArrayList(s0);
    StringConcatenation _builder = new StringConcatenation();
    _builder.newLine();
    _builder.append("definition VC1 where");
    _builder.newLine();
    _builder.append("  ");
    _builder.append("\"VC1 inv s0 \\<equiv>");
    _builder.newLine();
    _builder.append("  ");
    _builder.append("(");
    _builder.newLine();
    _builder.append("    ");
    _builder.append("(inv");
    _builder.newLine();
    _builder.append("      ");
    _builder.append("s0");
    _builder.newLine();
    _builder.append("    ");
    _builder.append(")");
    _builder.newLine();
    _builder.append("  ");
    _builder.append("-->");
    _builder.newLine();
    _builder.append("    ");
    _builder.append("(inv");
    _builder.newLine();
    _builder.append("      ");
    _builder.append("(toEnv");
    _builder.newLine();
    _builder.append("        ");
    _builder.append("s0");
    _builder.newLine();
    _builder.append("      ");
    _builder.append(")");
    _builder.newLine();
    _builder.append("    ");
    _builder.append(")");
    _builder.newLine();
    _builder.append("  ");
    _builder.append(")");
    _builder.newLine();
    _builder.append("  ");
    _builder.append("\"");
    _builder.newLine();
    final String expected = _builder.toString();
    final String result = this.generator.generateVC(vc, num, functionParams, variableParams);
    Assert.assertEquals(expected, result);
  }

  @Test
  public void testGenerateTheoryConstantsInTimeout() {
    throw new Error("Unresolved compilation problems:"
      + "\nThe method generateTheory() is undefined for the type PoSTGenerator");
  }
}
