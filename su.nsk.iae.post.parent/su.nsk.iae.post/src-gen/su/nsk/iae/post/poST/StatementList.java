/**
 * generated by Xtext 2.28.0
 */
package su.nsk.iae.post.poST;

import org.eclipse.emf.common.util.EList;

import org.eclipse.emf.ecore.EObject;

import su.nsk.iae.post.vcgenerator.*;
import java.util.List;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Statement List</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link su.nsk.iae.post.poST.StatementList#getStatements <em>Statements</em>}</li>
 * </ul>
 *
 * @see su.nsk.iae.post.poST.PoSTPackage#getStatementList()
 * @model
 * @generated
 */
public interface StatementList extends EObject
{
	List<Path> applyTo(Path path, VCGeneratorState globVars);
  /**
   * Returns the value of the '<em><b>Statements</b></em>' containment reference list.
   * The list contents are of type {@link su.nsk.iae.post.poST.Statement}.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the value of the '<em>Statements</em>' containment reference list.
   * @see su.nsk.iae.post.poST.PoSTPackage#getStatementList_Statements()
   * @model containment="true"
   * @generated
   */
  EList<Statement> getStatements();

} // StatementList
