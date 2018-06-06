package pgo.trans.intermediate;

import static org.junit.Assert.assertEquals;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collection;

import org.json.JSONObject;
import org.junit.After;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import pgo.PGoNetOptions;
import pgo.PGoOptionException;
import pgo.parser.PGoParseException;
import pgo.trans.PGoTransException;
import pgo.util.IOUtil;

@RunWith(Parameterized.class)
public class PGoTransStageModelCheckTest {

	protected PGoPluscalStageTesterBase tester;
	private PGoTransStageModelCheck p;

	public PGoTransStageModelCheckTest(PGoPluscalStageTesterBase tester) {
		this.tester = tester;
	}

	@Parameterized.Parameters
	public static Collection testSpecifications() {
		return Arrays.asList(new Object[][] { { new EuclidIntermediateTester() },
				{ new QueensPluscalIntermediateTester() } });
	}

	@Before
	public void SetUp() throws PGoParseException, PGoTransException, PGoOptionException {
		p = new PGoTransStageModelCheck(
				new PGoTransStageTLAParse(
						new PGoTransStageInitParse(tester.getParsedPcal(), new PGoNetOptions(new JSONObject()))));
	}

	// This stage modifies the ParsedPcal object, so need to reset it
	@After
	public void cleanup() {
		tester.clearPcal();
	}

	@Test
	public void testASTModification() throws PGoTransException, IOException {
		IOUtil.WriteAST(p.data.ast, "test/pluscal/ast/mctest/output/" + p.data.algName + ".tla");
		assertEquals(
				new String(
						Files.readAllBytes(Paths.get("test/pluscal/ast/mctest/expected/" + p.data.algName + ".tla")),
						StandardCharsets.UTF_8),
				new String(Files.readAllBytes(Paths.get("test/pluscal/ast/mctest/output/" + p.data.algName + ".tla")),
						StandardCharsets.UTF_8));
	}
}