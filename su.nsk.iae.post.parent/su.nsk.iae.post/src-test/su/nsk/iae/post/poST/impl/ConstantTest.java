package su.nsk.iae.post.poST.impl;

import org.junit.Assert;
import org.junit.Test;
import su.nsk.iae.post.poST.*;
import su.nsk.iae.post.vcgenerator.*;

public class ConstantTest {
	@Test
	public void generateConstantPosIntegerLiteral() {
		int value = 1;
		SignedInteger signedInteger = new SignedIntegerImpl();
		signedInteger.setValue(Integer.toString(value));
		IntegerLiteral intLiteral = new IntegerLiteralImpl();
		intLiteral.setValue(signedInteger);
		su.nsk.iae.post.poST.Constant constant = new ConstantImpl();
		constant.setNum(intLiteral);
		su.nsk.iae.post.vcgenerator.Constant result = constant.generateConstant();
		Assert.assertEquals(value, result.getValue());
		Assert.assertEquals(DataType.INT, result.getType());
		Assert.assertNull(result.getName());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void generateConstantNegIntegerLiteral() {
		int value = -2;
		SignedInteger signedInteger = new SignedIntegerImpl();
		signedInteger.setValue(Integer.toString(Math.abs(value)));
		signedInteger.setISig(true);
		IntegerLiteral intLiteral = new IntegerLiteralImpl();
		intLiteral.setValue(signedInteger);
		su.nsk.iae.post.poST.Constant constant = new ConstantImpl();
		constant.setNum(intLiteral);
		su.nsk.iae.post.vcgenerator.Constant result = constant.generateConstant();
		Assert.assertEquals(value, result.getValue());
		Assert.assertEquals(DataType.INT, result.getType());
		Assert.assertNull(result.getName());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void generateConstantPosRealLiteral() {
		double value = 0.5;
		RealLiteral realLiteral = new RealLiteralImpl();
		realLiteral.setValue(Double.toString(value));
		su.nsk.iae.post.poST.Constant constant = new ConstantImpl();
		constant.setNum(realLiteral);
		su.nsk.iae.post.vcgenerator.Constant result = constant.generateConstant();
		Assert.assertEquals(value, result.getValue());
		Assert.assertEquals(DataType.REAL, result.getType());
		Assert.assertNull(result.getName());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void generateConstantNegRealLiteral() {
		double value = -0.5;
		RealLiteral realLiteral = new RealLiteralImpl();
		realLiteral.setValue(Double.toString(Math.abs(value)));
		realLiteral.setRSig(true);
		su.nsk.iae.post.poST.Constant constant = new ConstantImpl();
		constant.setNum(realLiteral);
		su.nsk.iae.post.vcgenerator.Constant result = constant.generateConstant();
		Assert.assertEquals(value, result.getValue());
		Assert.assertEquals(DataType.REAL, result.getType());
		Assert.assertNull(result.getName());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void generateConstantTimeWithMsWithoutMWithoutS () {
		int d = 1, h = 1, m = 0, s = 0, ms = 100;
		int timeInMilliseconds = toMilliseconds(d, h, m, s, ms);
		TimeLiteral timeLiteral = new TimeLiteralImpl();
		timeLiteral.setInterval(generateTimeLiteral(d, h, m, s, ms));
		su.nsk.iae.post.poST.Constant constant = new ConstantImpl();
		constant.setTime(timeLiteral);
		su.nsk.iae.post.vcgenerator.Constant result = constant.generateConstant();
		Assert.assertEquals(timeInMilliseconds, result.getValue());
		Assert.assertEquals(DataType.INT, result.getType());
		Assert.assertNull(result.getName());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void generateConstantHexInteger() {
		int value = 10;
		su.nsk.iae.post.poST.Constant constant = new ConstantImpl();
		constant.setOth("16#" + Integer.toHexString(value));
		su.nsk.iae.post.vcgenerator.Constant result = constant.generateConstant();
		Assert.assertEquals(value, result.getValue());
		Assert.assertEquals(DataType.INT, result.getType());
		Assert.assertNull(result.getName());
		Assert.assertNull(result.getPrecondition());
	}
	
	@Test
	public void generateConstantBoolean() {
		boolean value = true;
		su.nsk.iae.post.vcgenerator.Constant expected =su.nsk.iae.post.vcgenerator.Constant.True;
		su.nsk.iae.post.poST.Constant constant = new ConstantImpl();
		constant.setOth(Boolean.toString(value).toUpperCase());
		su.nsk.iae.post.vcgenerator.Constant result = constant.generateConstant();
		Assert.assertEquals(expected, result);
		Assert.assertEquals(DataType.BOOL, result.getType());
		Assert.assertEquals(expected.getName(), result.getName());
		Assert.assertNull(result.getPrecondition());
	}
	
	private String generateTimeLiteral(int d, int h, int m, int s, int ms) {
		StringBuilder str = new StringBuilder();
		if (d != 0)
			str.append(Integer.toString(d) + "d");
		if (h != 0)
			str.append(Integer.toString(h) + "h");
		if (m != 0)
			str.append(Integer.toString(m) + "m");
		if (s != 0)
			str.append(Integer.toString(s) + "s");
		if (ms != 0)
			str.append(Integer.toString(ms) + "ms");
		return str.toString();
	}
	
	private int toMilliseconds(int d, int h, int m, int s, int ms) {
		int msTotal = 0;
		msTotal += ms;
		msTotal += s * 1000;
		msTotal += m * 1000 * 60;
		msTotal += h * 1000 * 60 * 60;
		msTotal += d * 1000 * 60 * 60 * 24;
		return msTotal;
	}
}
