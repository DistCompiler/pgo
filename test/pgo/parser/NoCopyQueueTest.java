package pgo.parser;

import org.junit.Assert;
import org.junit.Test;

import java.util.*;

import static org.hamcrest.CoreMatchers.*;

public class NoCopyQueueTest {

	private void testContents(NoCopyQueue<Integer> q, List<Integer> expected) {
		List<Integer> actual = new ArrayList<>();
		Optional<Integer> element;
		while((element = q.dequeue()).isPresent()) {
			actual.add(element.get());
		}
		Assert.assertThat(actual, is(expected));
	}

	@Test
	public void testSimpleScenario(){
		NoCopyQueue<Integer> q = new NoCopyQueue<>(Arrays.asList(1, 2, 3, 4, 5));
		testContents(q, Arrays.asList(1, 2, 3, 4, 5));
	}

	@Test
	public void testDoublePrepend(){
		NoCopyQueue<Integer> q = new NoCopyQueue<>(Arrays.asList(1, 2));
		q.prepend(Arrays.asList(3, 4));
		q.prepend(Arrays.asList(5, 6));
		testContents(q, Arrays.asList(5, 6, 3, 4, 1, 2));
	}

	@Test
	public void testPrependToDuplicate(){
		NoCopyQueue<Integer> q = new NoCopyQueue<>(Arrays.asList(1, 2));
		NoCopyQueue<Integer> q2 = q.duplicate();

		q.prepend(Arrays.asList(3, 4));
		q2.prepend(Arrays.asList(5, 6));
		testContents(q, Arrays.asList(3, 4, 1, 2));
		testContents(q2, Arrays.asList(5, 6, 1, 2));
	}

	@Test
	public void testPrependEmpty(){
		NoCopyQueue<Integer> q = new NoCopyQueue<>(Arrays.asList(1, 2));

		q.prepend(Collections.emptyList());
		testContents(q, Arrays.asList(1, 2));
	}

	@Test
	public void testPrependEmptyAfterReading(){
		NoCopyQueue<Integer> q = new NoCopyQueue<>(Arrays.asList(1, 2));

		q.prepend(Arrays.asList(3, 4));
		q.dequeue(); q.dequeue();
		q.prepend(Collections.emptyList());
		testContents(q, Arrays.asList(1, 2));
	}
}
