package run;

import java.io.ByteArrayInputStream;
import org.eclipse.emf.ecore.resource.Resource.Diagnostic;
import java.io.InputStream;
import java.util.List;
import java.io.*;

import org.eclipse.emf.common.util.EList;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.Term;
import su.nsk.iae.post.vcgenerator.VCGenerator;
import su.nsk.iae.post.*;

import com.google.inject.Injector;

public class AutoExec {
	static int period = 100;
	static String inFile = "example.post";
	static String outFile = null; //"VC.txt";
	static String text = "PROGRAM Controller\r\n"
			+ "	VAR_INPUT\r\n"
			+ "		hands : BOOL;\r\n"
			+ "	END_VAR\r\n"
			+ "\r\n"
			+ "	VAR_OUTPUT\r\n"
			+ "		dryer : BOOL;\r\n"
			+ "	END_VAR\r\n"
			+ "\r\n"
			+ "	PROCESS Ctrl\r\n"
			+ "		STATE waiting\r\n"
			+ "			IF hands  THEN\r\n"
			+ "				dryer := TRUE;\r\n"
			+ "				SET NEXT;\r\n"
			+ "			ELSE\r\n"
			+ "				dryer := FALSE;\r\n"
			+ "			END_IF\r\n"
			+ "		END_STATE\r\n"
			+ "\r\n"
			+ "		STATE drying\r\n"
			+ "			IF hands  THEN\r\n"
			+ "				RESET TIMER;\r\n"
			+ "			END_IF\r\n"
			+ "			TIMEOUT T#1s THEN\r\n"
			+ "				SET STATE waiting;\r\n"
			+ "			END_TIMEOUT\r\n"
			+ "		END_STATE\r\n"
			+ "	END_PROCESS\r\n"
			+ "END_PROGRAM\r\n"
			+ "CONFIGURATION Conf\r\n"
			+ "RESOURCE Res1 ON TestCPU\r\n"
			+ "TASK T1 (INTERVAL := T#100ms, PRIORITY := 1);\r\n"
			+ "PROGRAM program1 WITH T1: Controller;\r\n"
			+ "END_RESOURCE\r\n"
			+ "END_CONFIGURATION"
			+ "\r\n";
			

	public static void main(String[] args) {
		Injector injector = new PoSTStandaloneSetup().createInjectorAndDoEMFRegistration();
		XtextResourceSet resourceSet = injector.getInstance(XtextResourceSet.class);
		resourceSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);
		Resource resource = resourceSet.createResource(URI.createURI("dummy:/example.post"));

		try {
			InputStream in;
			if (text != null)
				in = new ByteArrayInputStream(text.getBytes());
			else
				in = new FileInputStream(inFile);
			resource.load(in, resourceSet.getLoadOptions());
			EList<Diagnostic> errors = resource.getErrors();
			if (errors != null && ! errors.isEmpty()) {
				for (Diagnostic error: errors)
					System.err.println(error);
				System.exit(1);
			}
			Model model = (Model) resource.getContents().get(0);
			VCGenerator vcGen = new VCGenerator(period);			
			List<Term> verificationConditions = vcGen.generateVCsForConfiguredProgram(model);
			PrintStream out;
			if (outFile != null)
				out = new PrintStream(new FileOutputStream(outFile));
			else
				out = System.out;
			for (Term vc: verificationConditions)
				out.println(vc);
		}
		catch (IOException ex) {
			System.out.println(ex.getMessage());
		}
	}

}
