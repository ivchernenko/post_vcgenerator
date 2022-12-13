package test;

import java.io.ByteArrayInputStream;
import java.io.InputStream;
import java.io.*;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.xtext.resource.XtextResource;
import org.eclipse.xtext.resource.XtextResourceSet;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.poST.Process;
import su.nsk.iae.post.*;

import com.google.inject.Injector;

public class Test {
	public static void main(String[] args) {
		Injector injector = new PoSTStandaloneSetup().createInjectorAndDoEMFRegistration();
		 XtextResourceSet resourceSet = injector.getInstance(XtextResourceSet.class);
		 resourceSet.addLoadOption(XtextResource.OPTION_RESOLVE_ALL, Boolean.TRUE);
		 Resource resource = resourceSet.createResource(URI.createURI("dummy:/example.post"));
		 String programText = "PROGRAM Ctrl\r\n"
		 		+ "VAR_INPUT\r\n"
		 		+ "a, b, c, d: BOOL;\r\n"
		 		+ "END_VAR\r\n"
		 		+ "VAR_OUTPUT\r\n"
		 		+ "e: BOOL;\r\n"
		 		+ "END_VAR\r\n"
		 		+ "PROCESS Init\r\n"
		 		+ "STATE init\r\n"
		 		+ "e:= NOT a;\r\n"
		 		+ "END_STATE\r\n"
		 		+ "END_PROCESS\r\n"
		 		+ "END_PROGRAM";
		 InputStream in = new ByteArrayInputStream(programText.getBytes());
		 try {
			  resource.load(in, resourceSet.getLoadOptions());
			  System.out.println(resource.getErrors());
			  Model model = (Model) resource.getContents().get(0);
			  Program program = model.getPrograms().get(0);
			  Process process = program.getProcesses().get(0);
			  State state = process.getStates().get(0);
			  Statement st = state.getStatement().getStatements().get(0);
			  AssignmentStatement as = (AssignmentStatement) st;
			  Expression expr = as.getValue();
			  Expression left = expr.getLeft();
			  XorExpression right = expr.getRight();
			  UnaryExpression un = (UnaryExpression) expr;
			  UnaryOperator op = un.getUnOp();
			  System.out.println(op.getLiteral());
			  System.out.println(op.getName());
			  System.out.println(op.getValue());
		 }
		catch (IOException ex) {}
	}

}
