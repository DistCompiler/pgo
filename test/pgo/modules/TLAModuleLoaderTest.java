package pgo.modules;

import static org.junit.Assert.*;
import static org.hamcrest.CoreMatchers.*;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;

import org.junit.Test;

import pgo.model.tla.PGoTLAModule;

public class TLAModuleLoaderTest {

	@Test
	public void testModuleNotFound() {
		TLAModuleLoader loader = new TLAModuleLoader(Arrays.asList());
		try {
			loader.loadModule("Test");
			fail("should have thrown ModuleLoadError");
		}catch(ModuleLoadError ex) {
			assertThat(ex.getCause(), is(ModuleNotFoundError.class));
			ModuleNotFoundError err = (ModuleNotFoundError)ex.getCause();
			assertThat(err.getPathsChecked(), is(Arrays.asList()));
		}
	}
	
	@Test
	public void testModuleFoundOneOption() throws ModuleLoadError {
		TLAModuleLoader loader = new TLAModuleLoader(Arrays.asList(new Path[] {
				Paths.get("test", "pluscal"),
		}));
		
		PGoTLAModule m = loader.loadModule("Sum");
		assertThat(m.getName(), is("Sum"));
	}
	
	@Test
	public void testModuleFoundFailOver() throws ModuleLoadError {
		TLAModuleLoader loader = new TLAModuleLoader(Arrays.asList(new Path[] {
				Paths.get("test", "tla", "tokens"),
				Paths.get("test", "pluscal"),
		}));
		
		PGoTLAModule m = loader.loadModule("Sum");
		assertThat(m.getName(), is("Sum"));
	}

}
