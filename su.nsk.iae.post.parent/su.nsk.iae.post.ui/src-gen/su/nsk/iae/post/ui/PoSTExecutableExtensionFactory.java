/*
 * generated by Xtext 2.25.0
 */
package su.nsk.iae.post.ui;

import com.google.inject.Injector;
import org.eclipse.xtext.ui.guice.AbstractGuiceAwareExecutableExtensionFactory;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;
import su.nsk.iae.post.ui.internal.PostActivator;

/**
 * This class was generated. Customizations should only happen in a newly
 * introduced subclass. 
 */
public class PoSTExecutableExtensionFactory extends AbstractGuiceAwareExecutableExtensionFactory {

	@Override
	protected Bundle getBundle() {
		return FrameworkUtil.getBundle(PostActivator.class);
	}
	
	@Override
	protected Injector getInjector() {
		PostActivator activator = PostActivator.getInstance();
		return activator != null ? activator.getInjector(PostActivator.SU_NSK_IAE_POST_POST) : null;
	}

}
