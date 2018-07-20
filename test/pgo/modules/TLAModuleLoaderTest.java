package pgo.modules;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;

import org.junit.Test;

import pgo.model.tla.PGoTLAModule;
import pgo.parser.TLAParseException;

public class TLAModuleLoaderTest {

	@Test
	public void testModuleNotFound() throws IOException, TLAParseException, NoModulesFoundInFileError {
		TLAModuleLoader loader = new TLAModuleLoader(Arrays.asList());
		try {
			loader.loadModule("Test");
			fail("should have thrown ModuleLoadError");
		}catch(ModuleNotFoundError ex) {
			assertThat(ex.getPathsChecked(), is(Arrays.asList()));
		}
	}
	
	@Test
	public void testModuleFoundOneOption() throws ModuleNotFoundError, IOException, TLAParseException, NoModulesFoundInFileError {
		TLAModuleLoader loader = new TLAModuleLoader(Arrays.asList(new Path[] {
				Paths.get("test", "pluscal"),
		}));
		
		PGoTLAModule m = loader.loadModule("Sum");
		assertThat(m.getName().getId(), is("Sum"));
	}
	
	@Test
	public void testModuleFoundFailOver() throws ModuleNotFoundError, IOException, TLAParseException, NoModulesFoundInFileError {
		TLAModuleLoader loader = new TLAModuleLoader(Arrays.asList(new Path[] {
				Paths.get("test", "tla", "tokens"),
				Paths.get("test", "pluscal"),
		}));
		
		PGoTLAModule m = loader.loadModule("Sum");
		assertThat(m.getName().getId(), is("Sum"));
	}

}
