package su.nsk.iae.post.generator;

import com.google.inject.Injector;
import com.google.inject.Provider;
import java.util.ArrayList;
import org.eclipse.xtend2.lib.StringConcatenation;
import org.eclipse.xtext.testing.XtextRunner;
import org.eclipse.xtext.testing.util.ParseHelper;
import org.eclipse.xtext.xbase.lib.CollectionLiterals;
import org.eclipse.xtext.xbase.lib.Exceptions;
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
    try {
      final String theoryName = "TestTheory";
      Constant _constant = new Constant("a\'", Integer.valueOf(1));
      final ArrayList<Constant> envVars = CollectionLiterals.<Constant>newArrayList(_constant);
      StringConcatenation _builder = new StringConcatenation();
      _builder.append("PROGRAM Program");
      _builder.newLine();
      _builder.append("VAR_INPUT");
      _builder.newLine();
      _builder.append("a: BOOL;");
      _builder.newLine();
      _builder.append("END_VAR");
      _builder.newLine();
      _builder.append("VAR_OUTPUT");
      _builder.newLine();
      _builder.append("b: BOOL;");
      _builder.newLine();
      _builder.append("END_VAR");
      _builder.newLine();
      _builder.append("VAR CONSTANT");
      _builder.newLine();
      _builder.append("t: TIME := T#1s;");
      _builder.newLine();
      _builder.append("END_VAR");
      _builder.newLine();
      _builder.append("PROCESS process1");
      _builder.newLine();
      _builder.append("STATE state1");
      _builder.newLine();
      _builder.append("TIMEOUT t THEN");
      _builder.newLine();
      _builder.append("END_TIMEOUT");
      _builder.newLine();
      _builder.append("END_STATE");
      _builder.newLine();
      _builder.append("END_PROCESS");
      _builder.newLine();
      _builder.append("END_PROGRAM");
      _builder.newLine();
      _builder.append("CONFIGURATION Conf");
      _builder.newLine();
      _builder.append("RESOURCE Res1 ON TestCPU");
      _builder.newLine();
      _builder.append("TASK T1 (INTERVAL := T#100ms, PRIORITY := 1);");
      _builder.newLine();
      _builder.append("PROGRAM program1 WITH T1: Program;");
      _builder.newLine();
      _builder.append("END_RESOURCE");
      _builder.newLine();
      _builder.append("END_CONFIGURATION");
      _builder.newLine();
      final String programText = _builder.toString();
      final Model model = this.parser.parse(programText);
      this.generator.setModel(model);
      this.generator.setTheoryName(theoryName);
      StringConcatenation _builder_1 = new StringConcatenation();
      _builder_1.append("theory ");
      _builder_1.append(theoryName);
      _builder_1.append(" imports VCTheory");
      _builder_1.newLineIfNotEmpty();
      _builder_1.append("begin");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("abbreviation a\' :: variable where \"a\' \\<equiv> (Suc 0)\"");
      _builder_1.newLine();
      _builder_1.append("abbreviation b\' :: variable where \"b\' \\<equiv> (Suc (Suc 0))\"");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("abbreviation process1\' :: process where \"process1\' \\<equiv> (Suc 0)\"");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("abbreviation process1\'state1\' :: pstate where \"process1\'state1\' \\<equiv> (Suc (Suc 0))\"");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("abbreviation t\' :: nat where \"t\' \\<equiv> 1000\"");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("abbreviation t\'TIMEOUT :: nat where \"t\'TIMEOUT \\<equiv> 10\"");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("(*Verification conditions*)");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("definition VC1 where");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"VC1 inv0 s0 \\<equiv>");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("=");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(toEnv");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(setPstate");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("emptyState");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("process1\'");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("process1\'state1\'");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("-->");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(inv0");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("definition VC2 where");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"VC2 inv0 env s0 a\'value \\<equiv>");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(inv0");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(env");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(getPstate");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("process1\'");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("=");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("process1\'state1\'");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("t\'TIMEOUT");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("<=");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(ltime");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("process1\'");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("-->");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(inv0");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(toEnv");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("definition VC3 where");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"VC3 inv0 env s0 a\'value \\<equiv>");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(inv0");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(env");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(getPstate");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("process1\'");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("=");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("process1\'state1\'");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(\\<not>");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("t\'TIMEOUT");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("<=");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("(ltime");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("                ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("                ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("                ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("              ");
      _builder_1.append("process1\'");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("-->");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(inv0");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(toEnv");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("definition VC4 where");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"VC4 inv0 env s0 a\'value \\<equiv>");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(inv0");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(env");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(getPstate");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("process1\'");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("=");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("STOP");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("-->");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(inv0");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(toEnv");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"");
      _builder_1.newLine();
      _builder_1.newLine();
      _builder_1.append("definition VC5 where");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"VC5 inv0 env s0 a\'value \\<equiv>");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(inv0");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(env");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("\\<and>");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(getPstate");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("            ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("process1\'");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("=");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("ERROR");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("-->");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append("(inv0");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append("(toEnv");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append("(setVarBool");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("s0");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("a\'");
      _builder_1.newLine();
      _builder_1.append("          ");
      _builder_1.append("a\'value");
      _builder_1.newLine();
      _builder_1.append("        ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("      ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("    ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append(")");
      _builder_1.newLine();
      _builder_1.append("  ");
      _builder_1.append("\"");
      _builder_1.newLine();
      _builder_1.append("end");
      _builder_1.newLine();
      final String expected = _builder_1.toString();
      final String result = this.generator.generateTheory();
      Assert.assertEquals(expected, result);
    } catch (Throwable _e) {
      throw Exceptions.sneakyThrow(_e);
    }
  }
}
