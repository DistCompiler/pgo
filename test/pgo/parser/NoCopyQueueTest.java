package pgo.parser;

import org.junit.Assert;
import org.junit.Test;

import java.awt.image.AreaAveragingScaleFilter;
import java.util.*;

import static org.hamcrest.CoreMatchers.*;

public class NoCopyQueueTest {

	private void testContents(ParsingContext.NoCopyQueue<Integer> q, List<Integer> expected) {
		List<Integer> actual = new ArrayList<>();
		Optional<Integer> element;
		while((element = q.dequeue()).isPresent()) {
			actual.add(element.get());
		}
		Assert.assertThat(actual, is(expected));
	}

	@Test
	public void testSimpleScenario(){
		ParsingContext.NoCopyQueue<Integer> q = new ParsingContext.NoCopyQueue<>(Arrays.asList(1, 2, 3, 4, 5));
		testContents(q, Arrays.asList(1, 2, 3, 4, 5));
	}

	@Test
	public void testDoublePrepend(){
		ParsingContext.NoCopyQueue<Integer> q = new ParsingContext.NoCopyQueue<>(Arrays.asList(1, 2));
		q.prepend(Arrays.asList(3, 4));
		q.prepend(Arrays.asList(5, 6));
		testContents(q, Arrays.asList(5, 6, 3, 4, 1, 2));
	}

	@Test
	public void testPrependToDuplicate(){
		ParsingContext.NoCopyQueue<Integer> q = new ParsingContext.NoCopyQueue<>(Arrays.asList(1, 2));
		ParsingContext.NoCopyQueue<Integer> q2 = q.duplicate();

		q.prepend(Arrays.asList(3, 4));
		q2.prepend(Arrays.asList(5, 6));
		testContents(q, Arrays.asList(3, 4, 1, 2));
		testContents(q2, Arrays.asList(5, 6, 1, 2));
	}

	@Test
	public void testPrependEmpty(){
		ParsingContext.NoCopyQueue<Integer> q = new ParsingContext.NoCopyQueue<>(Arrays.asList(1, 2));

		q.prepend(Collections.emptyList());
		testContents(q, Arrays.asList(1, 2));
	}

	@Test
	public void testPrependEmptyAfterReading(){
		ParsingContext.NoCopyQueue<Integer> q = new ParsingContext.NoCopyQueue<>(Arrays.asList(1, 2));

		q.prepend(Arrays.asList(3, 4));
		q.dequeue(); q.dequeue();
		q.prepend(Collections.emptyList());
		testContents(q, Arrays.asList(1, 2));
	}
}
