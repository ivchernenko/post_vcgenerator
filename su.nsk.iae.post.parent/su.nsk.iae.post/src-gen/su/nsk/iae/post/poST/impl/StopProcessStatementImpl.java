/**
 * generated by Xtext 2.28.0
 */
package su.nsk.iae.post.poST.impl;

import org.eclipse.emf.ecore.EClass;

import su.nsk.iae.post.poST.PoSTPackage;
import su.nsk.iae.post.poST.StopProcessStatement;

import su.nsk.iae.post.vcgenerator.*;
import java.util.List;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Stop Process Statement</b></em>'.
 * <!-- end-user-doc -->
 *
 * @generated
 */
public class StopProcessStatementImpl extends ProcessStatementsImpl implements StopProcessStatement
{
  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  protected StopProcessStatementImpl()
  {
    super();
  }
  
	@Override
	public List<Path> applyTo(List<Path> paths, VCGeneratorState globVars) {
		for (Path path: paths)
			  path.stopProcess(this, globVars);
		return paths;
	}

  /**
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @generated
   */
  @Override
  protected EClass eStaticClass()
  {
    return PoSTPackage.Literals.STOP_PROCESS_STATEMENT;
  }

} //StopProcessStatementImpl
