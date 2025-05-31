package su.nsk.iae.post.generator;

import java.util.Arrays;
import java.util.List;
import java.util.Scanner;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.xtext.diagnostics.Severity;
import org.eclipse.xtext.generator.GeneratorContext;
import org.eclipse.xtext.generator.GeneratorDelegate;
import org.eclipse.xtext.generator.IGeneratorContext;
import org.eclipse.xtext.generator.JavaIoFileSystemAccess;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;

import com.google.inject.Inject;
import com.google.inject.Injector;
import com.google.inject.Provider;

import su.nsk.iae.post.PoSTStandaloneSetup;
import su.nsk.iae.post.generator.PoSTGenerator;

public class Main {

	public static void main(String[] args) {
		String interval = null;
		String maxVCNumberPerFile = null;
		int intervalOptionIndex = Arrays.asList(args).indexOf("-i");
		if (intervalOptionIndex >= 0 && intervalOptionIndex < args.length - 1)
			interval = args[intervalOptionIndex + 1];
		int maxVCOptionIndex = Arrays.asList(args).indexOf("-n");
		if (maxVCOptionIndex >= 0 && maxVCOptionIndex < args.length - 1)
			maxVCNumberPerFile = args[maxVCOptionIndex + 1];
		if (!Arrays.stream(args).anyMatch(x -> x.equals("-d"))) {
			singleExecutions(args, interval, maxVCNumberPerFile);
		} else {
			service(args, interval, maxVCNumberPerFile);
		}
	}

	private static void singleExecutions(String[] args, String interval, String maxVCNumberPerFile) {
		if (args.length == 0) {
			System.err.println("Aborting: no path to poST file provided!");
			return;
		}
		Injector injector = new PoSTStandaloneSetup().createInjectorAndDoEMFRegistration();
		Main main = injector.getInstance(Main.class);
		main.runGenerator(
				Arrays.stream(args).filter(x -> x.contains(".post")).findFirst().get(), 
				Arrays.stream(args).anyMatch(x -> x.equals("-l")),
				interval, maxVCNumberPerFile);
	}

	private static boolean loop = true;

	private static void service(String[] args, String interval, String maxVCNumberPerFile) {
		boolean local = Arrays.stream(args).anyMatch(x -> x.equals("-l"));
		Injector injector = new PoSTStandaloneSetup().createInjectorAndDoEMFRegistration();
		Main main = injector.getInstance(Main.class);
		Runtime.getRuntime().addShutdownHook(new Thread() {
			@Override
			public void run() {
				loop = false;
			}
		});
		Scanner scanner = new Scanner(System.in);
		while (loop) {
			String file = scanner.next();
			main.runGenerator(file, local, interval, maxVCNumberPerFile);
		}
		scanner.close();
	}

	@Inject
	private Provider<ResourceSet> resourceSetProvider;

	@Inject
	private IResourceValidator validator;

	@Inject
	//private GeneratorDelegate generator;
	private PoSTGenerator generator;

	@Inject 
	private JavaIoFileSystemAccess fileAccess;

	protected void runGenerator(String string, boolean local, String interval, String maxVCNumberPerFile) {
		// Load the resource
		ResourceSet set = resourceSetProvider.get();
		Resource resource = set.getResource(URI.createFileURI(string), true);

		// Validate the resource
		List<Issue> issues = validator.validate(resource, CheckMode.ALL, CancelIndicator.NullImpl);
		if (checkErrors(issues)) {
			System.out.println("Code generation aborted.");
			printIssues(issues);
			return;
		}

		// Configure and start the generator
		fileAccess.setOutputPath(".");
		GeneratorContext context = new GeneratorContext();
		context.setCancelIndicator(CancelIndicator.NullImpl);
		if (interval != null) {
			generator.interval = interval;
		}
		if (maxVCNumberPerFile != null) {
			generator.maxVCNumberPerFile = Integer.parseInt(maxVCNumberPerFile);
		}
		try {
			generator.doGenerate(resource, fileAccess, context);
		} catch (Exception e) {
			System.err.println(e.getMessage());
			System.out.println("Code generation aborted.");
			return;
		}

		printIssues(issues);
	}

	private boolean checkErrors(List<Issue> issues) {
		for (Issue issue : issues) {
			if (issue.getSeverity() == Severity.ERROR) {
				return true;
			}
		}
		return false;
	}

	private void printIssues(List<Issue> issues) {
		for (Issue issue : issues) {
			System.err.println(issue);
		}
	}
}
