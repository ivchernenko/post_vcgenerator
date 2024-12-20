/**
 * generated by Xtext 2.28.0
 */
package su.nsk.iae.post.poST.impl;

import org.eclipse.emf.ecore.EClass;

import su.nsk.iae.post.poST.Expression;
import su.nsk.iae.post.poST.PoSTPackage;
import su.nsk.iae.post.poST.XorExpression;

import su.nsk.iae.post.vcgenerator.*;

/**
 * <!-- begin-user-doc -->
 * An implementation of the model object '<em><b>Xor Expression</b></em>'.
 * <!-- end-user-doc -->
 *
 * @generated
 */
public class XorExpressionImpl extends ExpressionImpl implements XorExpression
{
	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	protected XorExpressionImpl()
	{
		super();
	}

	@Override
	public Term generateExpression(Term currentState, VCGeneratorState globVars) {
		Expression left = getLeft();
		Expression right = getRight();
		Term symComputedLeft = left.generateExpression(currentState, globVars);
		Term symComputedRight = right.generateExpression(currentState, globVars);
		Term result = TermFactory.noteq(symComputedLeft, symComputedRight);
		result.addCondition(symComputedLeft.getPrecondition());
		result.addCondition(symComputedRight.getPrecondition());
		return result;
	}

	/**
	 * <!-- begin-user-doc -->
	 * <!-- end-user-doc -->
	 * @generated
	 */
	@Override
	protected EClass eStaticClass()
	{
		return PoSTPackage.Literals.XOR_EXPRESSION;
	}

} //XorExpressionImpl
