package pgo.parser;

import pgo.util.EmptyHeterogenousList;
import pgo.util.SourceLocatable;

import java.util.function.Function;
import java.util.function.Predicate;

/**
 * An grammar representing a sequence, to be used Builder-style as a fluent interface to build sequences of grammars.
 * @param <Sequence> a {@link pgo.util.HeterogenousList} containing all the non-dropped results of parsing this
 *                  sequence.
 */
public abstract class AbstractSequenceGrammar<Sequence extends EmptyHeterogenousList> extends Grammar<Located<Sequence>> {

	/**
	 * Returns a new sequence grammar whose results will contain all the results of {@param grammar} prepended to the
	 * existing results of the current sequence.
	 *
	 * <p>Note: when parsing a sequence, results will be combined in lexicographical order, with the results of
	 * the first element changing the least frequently. When accessing the result of this grammar however,
	 * the results will be in reverse parse order. The most "recent" part will be first.</p>
	 * @param grammar the grammar to append to this sequence
	 * @param <Result> the result type of {@param grammar}
	 * @return a new sequence grammar yielding all the results of this current sequence, but with all the results of
	 * {@param grammar} prepended.
	 */
	public <Result extends SourceLocatable> PartSequenceGrammar<Result, Sequence> part(Grammar<Result> grammar) {
		return new PartSequenceGrammar<>(this, grammar);
	}

	/**
	 * Returns a new sequence grammar that parses {@param grammar} in addition to the existing sequence, but does not
	 * yield any more results. All results yielded by {@param grammar} will be discarded, though their
	 * locations will still be combined with the location of the overall sequence result. The semantics are otherwise
	 * the same as {@link AbstractSequenceGrammar#part(Grammar)}.
	 * @param grammar the grammar to append to the sequence
	 * @param <Dropped> the type of results yielded by that grammar.
	 * @return a new sequence grammar yielding the same results as the current sequence (but maybe more or them if the
	 * dropped grammar is ambiguous).
	 */
	public <Dropped extends SourceLocatable> DropSequenceGrammar<Dropped, Sequence> drop(Grammar<Dropped> grammar) {
		return new DropSequenceGrammar<>(this, grammar);
	}

	/**
	 * Returns a new sequence grammar that parses {@param grammar} under a new parser state provided by applying
	 * {@param mappingGenerator} to the current sequence result as well as the existing parser state. This is only
	 * useful if you need to do something that cannot be expressed in BNF grammars like indentation-sensitivity.
	 *
	 * <p>Note: the parser cannot reliably memoize across dependentPart grammars since the new state could
	 * affect calls to {@link Grammar#filter(Predicate)}. Repeatedly crossing the boundary will not however
	 * wipe memoization of calls on either side of that boundary, so this should be safe for backtracking.</p>
	 * @param grammar the grammar to execute under the new parser state
	 * @param mappingGenerator a generator to generate the new parser state based on existing state and the current
	 *                         sequence result
	 * @param <Result> the result type of {@param grammar}
	 * @return a new sequence grammar with the same semantics as {@link AbstractSequenceGrammar#part} aside from the
	 * addition of a nested parser state that may affect how {@param grammar} executes.
	 */
	public <Result extends SourceLocatable> CallGrammar<Result, Sequence> dependentPart(
			Grammar<Result> grammar, Function<ParseInfo<Located<Sequence>>, VariableMap> mappingGenerator) {
		return new CallGrammar<>(this, grammar, mappingGenerator);
	}

}
