package su.nsk.iae.post.generator

import org.eclipse.emf.ecore.resource.Resource
import org.eclipse.xtext.generator.IFileSystemAccess2

import su.nsk.iae.post.poST.Model;
import su.nsk.iae.post.generator.IPoSTGenerator
import su.nsk.iae.post.vcgenerator.*
import java.util.List
import org.eclipse.xtext.generator.IGeneratorContext
import java.io.File

import static su.nsk.iae.post.vcgenerator.VCGeneratorState.*
import org.eclipse.xtext.generator.AbstractGenerator

class PoSTGenerator extends AbstractGenerator {
	String theoryName;
	public String interval;
	Model model;
	final int MAX_VC_NUMBER_PER_FILE = 1000;
	
	def String generateBaseTheory(VCGeneratorState vcGenVars) {
		return '''
			theory «theoryName» imports VCProving.VCTheory
			begin
			
			«FOR v : vcGenVars.getVariables()»
				«generateCode("variable", v)»
			 «ENDFOR»
			
			«FOR p : vcGenVars.getProcesses()»
				«generateCode("process", p)»
			 «ENDFOR»
			
			«FOR s : vcGenVars.getProcessStates()»
				«generateCode("pstate", s)»
			«ENDFOR»
			
			«FOR c : vcGenVars.getConstants().entrySet()»
				«generateConstant(vcGenVars.getVarType(c.getKey()), c.getValue())»
			«ENDFOR»	
			
			«FOR c : vcGenVars.getTimeoutConstants().entrySet()»
				«IF c.getValue() !== null»
					«generateConstant(vcGenVars.getVarType(c.getKey()), c.getValue())»
				«ENDIF»
			«ENDFOR»
			
			end
			
		'''
	}

	def String generateVCTheory(VCGeneratorState vcGenVars, int start, int end) {
		var vcList = new StringBuilder()
		for (var i = start; i < end; i++) {
			val vc = vcGenVars.vcSet.get(i)
			vcList.append(
				generateVC(vc, i + 1, vc.getFreeFunctionVariables(vcGenVars.getVcFunctionParams()),
					vc.getFreeVariables(vcGenVars.getVcVariableParams())))
				
		}
		return '''
			theory «theoryName»_VC_«start + 1»_«end» imports «theoryName»
			begin
			
			«vcList»
			end
		'''
	}

	def String generateCode(String type, Constant constant) {
		val value = constant.getValue() as Integer
		var stringValue = ""
		for (var i = 0; i < value; i++) {
			stringValue = stringValue + "(Suc "
		}
		stringValue = stringValue + "0"
		for (var i = 0; i < value; i++) {
			stringValue = stringValue + ")"
		}
		return '''
			abbreviation «constant.getName()» :: «type» where "«constant.getName()» \<equiv> «stringValue»"
		'''
	}

	def String generateConstant(String type, Term constant) {
		val isabelleType = getIsabelleType(type)
		return '''
			abbreviation «constant.getName()» :: «isabelleType» where "«constant.getName()» \<equiv> «constant.getValueString()»"
		'''
	}

	def String generateStateDataType(List<String> envVarTypes) {
		return '''
			datatype state =
			  emptyState |
			  toEnv state |
			  setVarBool state variable bool |
			  setVarInt state variable int |
			  setVarReal state variable real |
			  setVarArrayBool state variable int bool |
			  setVarArrayInt state variable int int |
			  setVarArrayReal state variable int real |
			  setVarAny state«FOR t : envVarTypes» «getIsabelleType(t)»«ENDFOR» |
			  setPstate state process pstate |
			  reset state process
		'''
	}

	def String generateGetVarBoolFunction(List<Constant> envVars, List<Constant> boolEnvVars) {
		return '''
			fun getVarBool:: "state => variable => bool" where
			  "getVarBool emptyState _ = False" |
			  "getVarBool (toEnv s) x = getVarBool s x" |
			  "getVarBool (setVarBool s y v) x = (if x = y then v else (getVarBool s x))" |
			  "getVarBool (setVarInt s _ _) x = getVarBool s x" |
			  "getVarBool (setVarReal s _ _) x = getVarBool s x" |
			  "getVarBool (setVarArrayBool s _ _ _) x = getVarBool s x" |
			  "getVarBool (setVarArrayInt s _ _ _) x = getVarBool s x" |
			  "getVarBool (setVarArrayReal s _ _ _) x = getVarBool s x" |
			«FOR x : boolEnvVars»
				«"  "»"getVarBool (setVarAny s «FOR v: envVars» «v.getName()»'value«ENDFOR») «x.getName()» = «x.getName()»'value" |
			«ENDFOR»
			  "getVarBool (setVarAny s «FOR v : envVars» «v.getName()»«NAME_SEPARATOR»value«ENDFOR») x = getVarBool s x" |
			  "getVarBool (setPstate s _ _) x = getVarBool s x" |
			  "getVarBool (reset s _) x = getVarBool s x"
		'''
	}

	def String generateGetVarIntFunction(List<Constant> envVars, List<Constant> intEnvVars) {
		return '''
			fun getVarInt:: "state => variable => int" where
			  "getVarInt emptyState _ = 0" |
			  "getVarInt (toEnv s) x = getVarInt s x" |
			  "getVarInt (setVarBool s _ _) x = getVarInt s x" |
			  "getVarInt (setVarInt s y v) x = (if x = y then v else (getVarInt s x))" |
			  "getVarInt (setVarReal s _ _) x = getVarInt s x" |
			  "getVarInt (setVarArrayBool s _ _ _) x = getVarInt s x" |
			  "getVarInt (setVarArrayInt s _ _ _) x = getVarInt s x" |
			  "getVarInt (setVarArrayReal s _ _ _) x = getVarInt s x" |
			«FOR x : intEnvVars»
				«"  "»"getVarInt (setVarAny s «FOR v: envVars» «v.getName()»'value«ENDFOR») «x.getName()» = «x.getName()»'value" |
			«ENDFOR»
			  "getVarInt (setVarAny s «FOR v : envVars» «v.getName()»'value«ENDFOR») x = getVarInt s x" |
			  "getVarInt (setPstate s _ _) x = getVarInt s x" |
			  "getVarInt (reset s _) x = getVarInt s x"
		'''
	}

	def String generateGetVarRealFunction(List<Constant> envVars, List<Constant> realEnvVars) {
		return '''
			fun getVarReal:: "state => variable => real" where
			  "getVarReal emptyState _ = 0" |
			  "getVarReal (toEnv s) x = getVarReal s x" |
			  "getVarReal (setVarBool s _ _) x = getVarReal s x" |
			  "getVarReal (setVarInt s _ _) x = getVarReal s x" |
			  "getVarReal (setVarReal s y v) x = (if x = y then v else (getVarReal s x))" |
			  "getVarReal (setVarArrayBool s _ _ _) x = getVarReal s x" |
			  "getVarReal (setVarArrayInt s _ _ _) x = getVarReal s x" |
			  "getVarReal (setVarArrayReal s _ _ _) x = getVarReal s x" |
			«FOR x : realEnvVars»
				«"  "»"getVarReal (setVarAny s «FOR v: envVars» «v.getName()»'value«ENDFOR») «x.getName()» = «x.getName()»'value" |
			«ENDFOR»
			  "getVarReal (setVarAny s «FOR v : envVars» «v.getName()»'value«ENDFOR») x = getVarReal s x" |
			  "getVarReal (setPstate s _ _) x = getVarReal s x" |
			  "getVarReal (reset s _) x = getVarReal s x"
		'''
	}

	def String generateGetVarArrayBoolFunction(List<Constant> envVars) {
		return '''
			fun getVarArrayBool:: "state => variable => int => bool" where
			  "getVarArrayBool emptyState _ _ = False" |
			  "getVarArrayBool (toEnv s) x i = getVarArrayBool s x i" |
			  "getVarArrayBool (setVarBool s _ _) x i = getVarArrayBool s x i" |
			  "getVarArrayBool (setVarInt s _ _) x i = getVarArrayBool s x i" |
			  "getVarArrayBool (setVarReal s _ _) x i = getVarArrayBool s x i" |
			  "getVarArrayBool (setVarArrayBool s y j v) x i = (if x = y \<and> i = j then v else (getVarArrayBool s x i))" |
			  "getVarArrayBool (setVarArrayInt s _ _ _) x i = getVarArrayBool s x i" |
			  "getVarArrayBool (setVarArrayReal s _ _ _) x i = getVarArrayBool s x i" |
			  "getVarArrayBool (setVarAny s «FOR v : envVars» «v.getName()»'value«ENDFOR») x i = getVarArrayBool s x i" |
			  "getVarArrayBool (setPstate s _ _) x i = getVarArrayBool s x i" |
			  "getVarArrayBool (reset s _) x i = getVarArrayBool s x i"
		'''
	}

	def String generateGetVarArrayIntFunction(List<Constant> envVars) {
		return '''
			fun getVarArrayInt:: "state => variable => int => int" where
			  "getVarArrayInt emptyState _ _ = 0" |
			  "getVarArrayInt (toEnv s) x i = getVarArrayInt s x i" |
			  "getVarArrayInt (setVarBool s _ _) x i = getVarArrayInt s x i" |
			  "getVarArrayInt (setVarInt s _ _) x i = getVarArrayInt s x i" |
			  "getVarArrayInt (setVarReal s _ _) x i = getVarArrayInt s x i" |
			  "getVarArrayInt (setVarArrayBool s _ _ _) x i = getVarArrayInt s x i" |
			  "getVarArrayInt (setVarArrayInt s y j v) x i = (if x = y \<and> i = j then v else (getVarArrayInt s x i))" |
			  "getVarArrayInt (setVarArrayReal s _ _ _) x i = getVarArrayInt s x i" |
			  "getVarArrayInt (setVarAny s «FOR v : envVars» «v.getName()»'value«ENDFOR») x i = getVarArrayInt s x i" |
			  "getVarArrayInt (setPstate s _ _) x i = getVarArrayInt s x i" |
			  "getVarArrayInt (reset s _) x i = getVarArrayInt s x i"
		'''
	}

	def String generateGetVarArrayRealFunction(List<Constant> envVars) {
		return '''
			fun getVarArrayReal:: "state => variable => int => real" where
			  "getVarArrayReal emptyState _ _ = 0" |
			  "getVarArrayReal (toEnv s) x i = getVarArrayReal s x i" |
			  "getVarArrayReal (setVarBool s _ _) x i = getVarArrayReal s x i" |
			  "getVarArrayReal (setVarInt s _ _) x i = getVarArrayReal s x i" |
			  "getVarArrayReal (setVarReal s _ _) x i = getVarArrayReal s x i" |
			  "getVarArrayReal (setVarArrayBool s _ _ _) x i = getVarArrayReal s x i" |
			  "getVarArrayReal (setVarArrayInt s _ _ _) x i = getVarArrayReal s x i" |
			  "getVarArrayReal (setVarArrayReal s y j v) x i = (if x = y \<and> i = j then v else (getVarArrayReal s x i))" |
			  "getVarArrayReal (setVarAny s «FOR v : envVars» «v.getName()»'value«ENDFOR») x i = getVarArrayReal s x i" |
			  "getVarArrayReal (setPstate s _ _) x i = getVarArrayReal s x i" |
			  "getVarArrayReal (reset s _) x i = getVarArrayReal s x i"
		'''
	}

	def String generateGetPstateFunction(List<Constant> envVars) {
		return '''
			fun getPstate:: "state => process => pstate" where
			  "getPstate emptyState _ = 0" |
			  "getPstate (toEnv s) p = getPstate s p" |
			  "getPstate (setVarBool s _ _) p = getPstate s p" |
			  "getPstate (setVarInt s _ _) p = getPstate s p" |
			  "getPstate (setVarReal s _ _) p = getPstate s p" |
			  "getPstate (setVarArrayBool s _ _ _) p = getPstate s p" |
			  "getPstate (setVarArrayInt s _ _ _) p = getPstate s p" |
			  "getPstate (setVarArrayReal s _ _ _) p = getPstate s p" |
			  "getPstate (setVarAny s «FOR v : envVars» «v.getName()»'value«ENDFOR») p = getPstate s p" |
			  "getPstate (setPstate s p1 q) p = (if p = p1 then q else (getPstate s p))" |
			  "getPstate (reset s _) p = getPstate s p"
		'''
	}

	def generateSubstateFunction(List<Constant> envVars) {
		val setVarAnys1 = '''(setVarAny s1 «FOR v : envVars» «v.getName()»'value«ENDFOR»)'''
		return '''
			fun substate:: "state => state => bool" where
			  "substate s emptyState =
			    (if s = emptyState then True else False)" |
			  "substate s (toEnv s1) =
			    (if s = toEnv s1 then True else substate s s1)" |
			  "substate s (setVarBool s1 x v) = 
			    (if s = setVarBool s1 x v then True else substate s s1)" |
			  "substate s (setVarInt s1 x v) =
			    (if s = setVarInt s1 x v then True else substate s s1)" |
			  "substate s (setVarReal s1 x v) =
			    (if s = setVarReal s1 x v then True else substate s s1)" |
			  "substate s (setVarArrayBool s1 x i v) =
			    (if s = setVarArrayBool s1 x i v then True else substate s s1)" |
			  "substate s (setVarArrayInt s1 x i v) =
			    (if s = setVarArrayInt s1 x i v then True else substate s s1)" |
			  "substate s (setVarArrayReal s1 x i v) =
			    (if s = setVarArrayReal s1 x i v then True else substate s s1)" |
			  "substate s «setVarAnys1» =
			    (if s = «setVarAnys1» then True else substate s s1)" |
			  "substate s (setPstate s1 p q) =
			    (if s = setPstate s1 p q then True else substate s s1)" |
			  "substate s (reset s1 p) =
			    (if s = reset s1 p then True else substate s s1)"
		'''
	}

	def String generateToEnvNumFunction(List<Constant> envVars) {
		val setVarAnys1 = '''(setVarAny s1 «FOR v : envVars» «v.getName()»'value«ENDFOR»)'''
		return '''
			fun toEnvNum:: "state => state => nat" where 
			  "toEnvNum s emptyState = 0" |
			  "toEnvNum s (toEnv s1) = 
			    (if s = toEnv s1 then 0 else toEnvNum s s1 + 1)" |
			  "toEnvNum s (setVarBool s1 x v) =
			    (if s = setVarBool s1 x v then 0 else toEnvNum s s1)" |
			  "toEnvNum s (setVarInt s1 x v) =
			    (if s = setVarInt s1 x v then 0 else toEnvNum s s1)" |
			  "toEnvNum s (setVarReal s1 x v) =
			    (if s = setVarReal s1 x v then 0 else toEnvNum s s1)" |
			  "toEnvNum s (setVarArrayBool s1 x i v) =
			    (if s = setVarArrayBool s1 x i v then 0 else toEnvNum s s1)" |
			  "toEnvNum s (setVarArrayInt s1 x i v) =
			    (if s = setVarArrayInt s1 x i v then 0 else toEnvNum s s1)" |
			  "toEnvNum s (setVarArrayReal s1 x i v) =
			    (if s = setVarArrayReal s1 x i v then 0 else toEnvNum s s1)" |
			  "toEnvNum s «setVarAnys1» =
			    (if s = «setVarAnys1» then 0 else toEnvNum s s1)" |
			  "toEnvNum s (setPstate s1 p q) =
			    (if s = setPstate s1 p q then 0 else toEnvNum s s1)" |
			  "toEnvNum s (reset s1 p) =
			    (if s = reset s1 p then 0 else toEnvNum s s1)"
		'''
	}

	def String generateToEnvPFunction() {
		return '''
			fun toEnvP::"state => bool" where
			  "toEnvP (toEnv _) = True" |
			  "toEnvP _ = False"
		'''
	}

	def String generateLtimeFunction(List<Constant> envVars) {
		val setVarAnys = '''(setVarAny s «FOR v : envVars» «v.getName()»'value«ENDFOR»)'''
		return '''
			fun ltime:: "state => process => nat" where 
			  "ltime emptyState _ = 0" |
			  "ltime (toEnv s) p = (ltime s p) + 1" |
			  "ltime (setVarBool s _ _) p = ltime s p" |
			  "ltime (setVarInt s _ _) p = ltime s p" |
			  "ltime (setVarReal s _ _) p = ltime s p" |
			  "ltime (setVarArrayBool s _ _ _) p = ltime s p" |
			  "ltime (setVarArrayInt s _ _ _) p = ltime s p" |
			  "ltime (setVarArrayReal s _ _ _) p = ltime s p" |
			  "ltime «setVarAnys» p = ltime s p" |
			  "ltime (setPstate s p1 _) p = (if p = p1 then 0 else ltime s p)" |
			  "ltime (reset s p1) p = (if p = p1 then 0 else ltime s p)"
		'''
	}

	def String generatePredEnvFunction(List<Constant> envVars) {
		val setVarAnys = '''(setVarAny s «FOR v : envVars» «v.getName()»'value«ENDFOR»)'''
		return '''
			fun predEnv:: "state => state" where
			  "predEnv emptyState = emptyState" |
			  "predEnv (toEnv s) =
			    (if (toEnvP s) then s else predEnv s)" |		
			  "predEnv (setVarBool s _ _) = 
			    (if (toEnvP s) then s else predEnv s)" |
			  "predEnv (setVarInt s _ _) = 
			    (if (toEnvP s) then s else predEnv s)" |
			  "predEnv (setVarReal s _ _) = 
			    (if (toEnvP s) then s else predEnv s)" |
			  "predEnv (setVarArrayBool s _ _ _) = 
			    (if (toEnvP s) then s else predEnv s)" |
			  "predEnv (setVarArrayInt s _ _ _) = 
			    (if (toEnvP s) then s else predEnv s)" |
			  "predEnv (setVarArrayReal s _ _ _) = 
			    (if (toEnvP s) then s else predEnv s)" |
			  "predEnv «setVarAnys» = 
			    (if (toEnvP s) then s else predEnv s)" |
			  "predEnv (setPstate s _ _) = 
			    (if (toEnvP s) then s else predEnv s)" |
			  "predEnv (reset s _) = 
			    (if (toEnvP s) then s else predEnv s)"
		'''
	}

	def String generateShiftFunction() {
		return '''
			fun shift:: "state => nat => state" where
			  "shift s 0 = s" |
			  "shift s (Suc n) = predEnv (shift s n)"
		'''
	}
	
	def String generateVC(Term vc, int num, List<FunctionSymbol> functionParams, List<Variable> variableParams) {
		return '''
			
			definition VC«num» where
			  "VC«num»«FOR param : functionParams» «param»«ENDFOR»«FOR param : variableParams» «param»«ENDFOR» \<equiv>
			  «generateTerm(vc)»"
		'''
	}

	def String generateTerm(Term term) {
		switch term {
			Constant:
				return term.toString()
			Variable:
				return term.toString()
			ComplexTerm: {
				return '''
					(«IF term.function.infix»
						  «generateTerm(term.args.get(0))»
						«term.function»
						  «generateTerm(term.args.get(1))»
					«ELSE»	
						«term.function»
						  «generateSubterms(term.args)»
					«ENDIF»
					)
				'''
			}
		}
	}

	def String generateSubterms(Term[] terms) {
		return '''
			«FOR t : terms»
				«generateTerm(t)»
			«ENDFOR»
		'''
	}

	def String getIsabelleType(String type) {
		if ("BOOL".equals(type)) {
			return "bool"
		} 
		else if (Utils.isUnsignedIntegerTypeName(type)) {
			return "nat"
		}
		else if (Utils.isIntegerTypeName(type)) {
			return "int"
		} else if (Utils.isRealTypeName(type)) {
			return "real"
		} else
			return "int"

	}
	
	def String encodeFileName(String fileName) {
		var encodedName = new StringBuilder()
		for (var i = 0; i < fileName.length(); i++) {
			var ch = fileName.charAt(i)
			if (Character.isLetterOrDigit(ch)) {
				encodedName.append((ch))
			}
			else {
				val char underscore = '_'
				if (ch == underscore ) {
					encodedName.append("__")
				}
				else {
					encodedName.append('_').append(Integer.toHexString(ch))
					}
			}
		}
		return encodedName.toString() 
	}

	def void setInterval(String interval) {
		this.interval = interval
	}

	def void setModel(Model model) {
		this.model = model
	}
	
	def void setTheoryName(String theoryName) {
		this.theoryName = theoryName
	}

	override afterGenerate(Resource input, IFileSystemAccess2 fsa, IGeneratorContext context) {}

	override beforeGenerate(Resource input, IFileSystemAccess2 fsa, IGeneratorContext context) {}

	override doGenerate(Resource input, IFileSystemAccess2 fsa, IGeneratorContext context) {
		theoryName = new File(input.getURI().toFileString()).getName()
		theoryName = theoryName.substring(0, theoryName.lastIndexOf("."))
		theoryName = encodeFileName(theoryName)
		model = input.getContents().get(0) as Model
			if (interval === null || interval.isEmpty()) {
			interval = "T#100ms"
		}
		interval = interval.substring(2)
		val vcGenerator = new VCGenerator(Utils.parseTime(interval))
		val vcGenVars = vcGenerator.generateVCsForConfiguredProgram(model)
		val vcNumber = vcGenVars.getVcSet().size()
		System.out.println(vcNumber);
		val vcParams = vcGenVars.getVcVariableParams()
		for (var i =0; i < vcParams.size(); i++) {
			System.out.print(vcParams.get(i) + ' ')
		} 
		fsa.generateFile(theoryName + ".thy", 
				generateBaseTheory(vcGenVars)
			)
		for (var i = 0; i < vcNumber; i += MAX_VC_NUMBER_PER_FILE) {
			val start = i
			val end = Math.min(i + MAX_VC_NUMBER_PER_FILE, vcNumber);
			fsa.generateFile(theoryName + '_' + (start + 1) + '_' + end + ".thy", 
				generateVCTheory(vcGenVars, start, end)
			)
		}
	}

}
