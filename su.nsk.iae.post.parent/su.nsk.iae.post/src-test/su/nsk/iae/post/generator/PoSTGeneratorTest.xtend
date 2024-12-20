package su.nsk.iae.post.generator

import org.junit.Assert
import org.junit.Test
import com.google.inject.Injector
import com.google.inject.Provider
import su.nsk.iae.post.PoSTStandaloneSetup
import su.nsk.iae.post.poST.Model
import su.nsk.iae.post.vcgenerator.Constant
import org.eclipse.xtext.testing.util.ParseHelper
import org.eclipse.xtext.testing.XtextRunner
import org.junit.runner.RunWith
import org.eclipse.xtext.testing.InjectWith
import com.google.inject.Inject
import su.nsk.iae.post.vcgenerator.*
import static su.nsk.iae.post.vcgenerator.TermFactory.*
import java.util.List

@RunWith(XtextRunner)
class PoSTGeneratorTest {
	Injector injector = new PoSTStandaloneSetup().createInjectorAndDoEMFRegistration();
	package ParseHelper<Model> parser = (((injector.getProvider(ParseHelper) as Provider)).get() as ParseHelper)
	PoSTGenerator generator = new PoSTGenerator;

	@Test def void testGenerateVariableCode() {
		val varCode = new Constant("a", 2)
		val expected = '''
		abbreviation a :: variable where "a \<equiv> (Suc (Suc 0))"
		'''
		val result = generator.generateCode("variable", varCode)
		Assert.assertEquals(expected, result)
	}
	
	@Test def void testGenerateProcessCode() {
		val varCode = new Constant("p", 2)
		val expected = '''
		abbreviation p :: process where "p \<equiv> (Suc (Suc 0))"
		'''
		val result = generator.generateCode("process", varCode)
		Assert.assertEquals(expected, result)
	}
	
	@Test def void testGenerateProcessStateCode() {
		val varCode = new Constant("s", 2)
		val expected = '''
		abbreviation s :: pstate where "s \<equiv> (Suc (Suc 0))"
		'''
		val result = generator.generateCode("pstate", varCode)
		Assert.assertEquals(expected, result)
	}
	
	@Test def void testGenerateConstant() {
		val constant = new Constant("a", 2)
		val type = "SINT"
		val expected = '''
		abbreviation a :: int where "a \<equiv> 2"
		'''
		val result = generator.generateConstant(type, constant)
		Assert.assertEquals(expected, result)
	}
	
	@Test def void testGenerateVC() {
		val inv = new FunctionSymbol("inv", true)
		val s0 = new Variable("s0")
		val vc = impl(new ComplexTerm(inv, s0), new ComplexTerm(inv, toEnv(s0)))
		val num = 1
		val functionParams = newArrayList(inv)
		val variableParams = newArrayList(s0)
		val expected = '''
		
		definition VC1 where
		  "VC1 inv s0 \<equiv>
		  (
		    (inv
		      s0
		    )
		  -->
		    (inv
		      (toEnv
		        s0
		      )
		    )
		  )
		  "
		'''
		val result = generator.generateVC(vc, num, functionParams, variableParams)
		Assert.assertEquals(expected, result)
	}
	
	@Test def void testGenerateTheoryConstantsInTimeout() {
		val theoryName = "TestTheory"
		val envVars = newArrayList(new Constant("a'", 1))
		val programText = '''
		PROGRAM Program
		VAR_INPUT
		a: BOOL;
		END_VAR
		VAR_OUTPUT
		b: BOOL;
		END_VAR
		VAR CONSTANT
		t: TIME := T#1s;
		END_VAR
		PROCESS process1
		STATE state1
		TIMEOUT t THEN
		END_TIMEOUT
		END_STATE
		END_PROCESS
		END_PROGRAM
		CONFIGURATION Conf
		RESOURCE Res1 ON TestCPU
		TASK T1 (INTERVAL := T#100ms, PRIORITY := 1);
		PROGRAM program1 WITH T1: Program;
		END_RESOURCE
		END_CONFIGURATION
		'''
		val model = parser.parse(programText)
		generator.model = model
		generator.theoryName = theoryName
		val expected = '''
		theory «theoryName» imports VCTheory
		begin
		
		abbreviation a' :: variable where "a' \<equiv> (Suc 0)"
		abbreviation b' :: variable where "b' \<equiv> (Suc (Suc 0))"
		
		abbreviation process1' :: process where "process1' \<equiv> (Suc 0)"
		
		abbreviation process1'state1' :: pstate where "process1'state1' \<equiv> (Suc (Suc 0))"
		
		abbreviation t' :: nat where "t' \<equiv> 1000"
		
		abbreviation t'TIMEOUT :: nat where "t'TIMEOUT \<equiv> 10"
		
		(*Verification conditions*)
		
		
		definition VC1 where
		  "VC1 inv0 s0 \<equiv>
		  (
		    (
		      s0
		    =
		      (toEnv
		        (setPstate
		          emptyState
		          process1'
		          process1'state1'
		        )
		      )
		    )
		  -->
		    (inv0
		      s0
		    )
		  )
		  "
		
		definition VC2 where
		  "VC2 inv0 env s0 a'value \<equiv>
		  (
		    (
		      (
		        (inv0
		          s0
		        )
		      \<and>
		        (env
		          (setVarBool
		            s0
		            a'
		            a'value
		          )
		        )
		      )
		    \<and>
		      (
		        (
		          (getPstate
		            (setVarBool
		              s0
		              a'
		              a'value
		            )
		            process1'
		          )
		        =
		          process1'state1'
		        )
		      \<and>
		        (
		          t'TIMEOUT
		        <=
		          (ltime
		            (setVarBool
		              s0
		              a'
		              a'value
		            )
		            process1'
		          )
		        )
		      )
		    )
		  -->
		    (inv0
		      (toEnv
		        (setVarBool
		          s0
		          a'
		          a'value
		        )
		      )
		    )
		  )
		  "
		
		definition VC3 where
		  "VC3 inv0 env s0 a'value \<equiv>
		  (
		    (
		      (
		        (inv0
		          s0
		        )
		      \<and>
		        (env
		          (setVarBool
		            s0
		            a'
		            a'value
		          )
		        )
		      )
		    \<and>
		      (
		        (
		          (getPstate
		            (setVarBool
		              s0
		              a'
		              a'value
		            )
		            process1'
		          )
		        =
		          process1'state1'
		        )
		      \<and>
		        (\<not>
		          (
		            t'TIMEOUT
		          <=
		            (ltime
		              (setVarBool
		                s0
		                a'
		                a'value
		              )
		              process1'
		            )
		          )
		        )
		      )
		    )
		  -->
		    (inv0
		      (toEnv
		        (setVarBool
		          s0
		          a'
		          a'value
		        )
		      )
		    )
		  )
		  "
		
		definition VC4 where
		  "VC4 inv0 env s0 a'value \<equiv>
		  (
		    (
		      (
		        (inv0
		          s0
		        )
		      \<and>
		        (env
		          (setVarBool
		            s0
		            a'
		            a'value
		          )
		        )
		      )
		    \<and>
		      (
		        (getPstate
		          (setVarBool
		            s0
		            a'
		            a'value
		          )
		          process1'
		        )
		      =
		        STOP
		      )
		    )
		  -->
		    (inv0
		      (toEnv
		        (setVarBool
		          s0
		          a'
		          a'value
		        )
		      )
		    )
		  )
		  "
		
		definition VC5 where
		  "VC5 inv0 env s0 a'value \<equiv>
		  (
		    (
		      (
		        (inv0
		          s0
		        )
		      \<and>
		        (env
		          (setVarBool
		            s0
		            a'
		            a'value
		          )
		        )
		      )
		    \<and>
		      (
		        (getPstate
		          (setVarBool
		            s0
		            a'
		            a'value
		          )
		          process1'
		        )
		      =
		        ERROR
		      )
		    )
		  -->
		    (inv0
		      (toEnv
		        (setVarBool
		          s0
		          a'
		          a'value
		        )
		      )
		    )
		  )
		  "
		end
		'''
		val result = generator.generateTheory()
		Assert.assertEquals(expected, result)
	}
}
