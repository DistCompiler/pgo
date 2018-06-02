package pgo;

import static org.hamcrest.CoreMatchers.is;
import static org.junit.Assert.assertThat;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;

public class IntegrationTestingUtils {
	
	private IntegrationTestingUtils() {}
	
	public static void expungeFile(File file) {
		if(file.isDirectory()) {
			for(File f : file.listFiles()) {
				expungeFile(f);
			}
		}
		if(!file.delete()) {
			System.err.println("WARNING: could not delete file "+file+"; check your temp folder");
		}
	}
	
	public static void testRunGoCode(Path codePath, List<String> expected) throws IOException {
		// try to run the compiled Go code, check that it prints the right thing
		ProcessBuilder pb = new ProcessBuilder("go", "run", codePath.toString());
		Process p = pb.start();
		// print stderr in case it says something interesting
		try(InputStream err = p.getErrorStream();
				InputStreamReader r = new InputStreamReader(err);
				BufferedReader bw = new BufferedReader(r)){
			bw.lines().forEach(line -> {
				System.out.println("stderr: "+line);
			});
		}
		try(InputStream results = p.getInputStream();
				InputStreamReader r = new InputStreamReader(results);
				BufferedReader bw = new BufferedReader(r)){
			List<String> lines = bw.lines().collect(Collectors.toList());
			assertThat(lines, is(expected));
		}
	}

}
