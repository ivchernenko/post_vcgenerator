/**
 * generated by Xtext 2.25.0
 */
package su.nsk.iae.post.poST;

import org.eclipse.emf.ecore.EObject;

/**
 * <!-- begin-user-doc -->
 * A representation of the model object '<em><b>Case List Element</b></em>'.
 * <!-- end-user-doc -->
 *
 * <p>
 * The following features are supported:
 * </p>
 * <ul>
 *   <li>{@link su.nsk.iae.post.poST.CaseListElement#getNum <em>Num</em>}</li>
 *   <li>{@link su.nsk.iae.post.poST.CaseListElement#getVariable <em>Variable</em>}</li>
 * </ul>
 *
 * @see su.nsk.iae.post.poST.PoSTPackage#getCaseListElement()
 * @model
 * @generated
 */
public interface CaseListElement extends EObject
{
  /**
   * Returns the value of the '<em><b>Num</b></em>' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the value of the '<em>Num</em>' containment reference.
   * @see #setNum(SignedInteger)
   * @see su.nsk.iae.post.poST.PoSTPackage#getCaseListElement_Num()
   * @model containment="true"
   * @generated
   */
  SignedInteger getNum();

  /**
   * Sets the value of the '{@link su.nsk.iae.post.poST.CaseListElement#getNum <em>Num</em>}' containment reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Num</em>' containment reference.
   * @see #getNum()
   * @generated
   */
  void setNum(SignedInteger value);

  /**
   * Returns the value of the '<em><b>Variable</b></em>' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @return the value of the '<em>Variable</em>' reference.
   * @see #setVariable(SymbolicVariable)
   * @see su.nsk.iae.post.poST.PoSTPackage#getCaseListElement_Variable()
   * @model
   * @generated
   */
  SymbolicVariable getVariable();

  /**
   * Sets the value of the '{@link su.nsk.iae.post.poST.CaseListElement#getVariable <em>Variable</em>}' reference.
   * <!-- begin-user-doc -->
   * <!-- end-user-doc -->
   * @param value the new value of the '<em>Variable</em>' reference.
   * @see #getVariable()
   * @generated
   */
  void setVariable(SymbolicVariable value);

} // CaseListElement
