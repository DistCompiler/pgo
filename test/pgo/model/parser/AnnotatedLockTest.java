package pgo.model.parser;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import org.junit.Test;

import pgo.parser.PGoParseException;

public class AnnotatedLockTest {

	@Test
	public void testParse() throws PGoParseException {
		String[] annot = new String[] { "lock", "true" };
		AnnotatedLock l = AnnotatedLock.parse(annot, 0);
		assertTrue(l.needsLock());
		assertEquals(0, l.getLine());
		annot[1] = "false";
		l = AnnotatedLock.parse(annot, 4);
		assertFalse(l.needsLock());
		assertEquals(4, l.getLine());
	}

	@Test(expected = PGoParseException.class)
	public void testParseFail() throws PGoParseException {
		String[] annot = new String[] { "lock", "bad" };
		try {
			AnnotatedLock l = AnnotatedLock.parse(annot, 0);
			fail("Expected PGoParseException");
		} catch (PGoParseException e) {
			annot = new String[] { "lock", "true", "too many" };
			AnnotatedLock l = AnnotatedLock.parse(annot, 0);
		}
	}
}
