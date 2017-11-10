package pgo.util;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Vector;
import java.util.logging.Logger;

import pcal.AST;
import pcal.PcalParams;
import pcal.exception.FileToStringVectorException;
import pcal.exception.StringVectorToFileException;

public class IOUtil {
	/***************** METHODS FOR READING AND WRITING FILES *****************/

	/***********************************************************************
	 * Writes the Vector of strings inputVec to file named fileName, with * each
	 * element of inputVec written on a new line. *
	 ***********************************************************************/
	public static void WriteStringVectorToFile(Vector inputVec, String fileName) throws StringVectorToFileException {
		try {
			Path filePath = Paths.get(fileName);
			if(!Files.exists(filePath.getParent())){
				Files.createDirectories(filePath.getParent());
				Files.createFile(filePath);
			}
			BufferedWriter fileW = new BufferedWriter(new FileWriter(fileName));
			int lineNum = 0;
			while (lineNum < inputVec.size()) {
				fileW.write((String) inputVec.elementAt(lineNum));
				fileW.newLine();
				lineNum = lineNum + 1;
			}

			fileW.close();
		} catch (Exception e) {
			throw new StringVectorToFileException("Could not write file " + fileName);
		}

	}

	/***********************************************************************
	 * Reads file fileName into a StringVector, a vector in which each * element
	 * is a line of the file. *
	 ***********************************************************************/
	public static Vector fileToStringVector(String fileName) throws FileToStringVectorException {
		Vector inputVec = new Vector(100);
		try {
			BufferedReader bufferedReader = new BufferedReader(new InputStreamReader(new FileInputStream(fileName)));
			try {
				String nextLine = bufferedReader.readLine();
				while (nextLine != null) {
					inputVec.addElement(nextLine);
					nextLine = bufferedReader.readLine();
				}
				;
				bufferedReader.close();
			} catch (IOException e) {
				/*********************************************************
				 * Error while reading input file. *
				 *********************************************************/
				throw new FileToStringVectorException("Error reading file " + fileName + ".");
			}
		}

		catch (FileNotFoundException e) {
			/**************************************************************
			 * Input file could not be found. *
			 **************************************************************/
			throw new FileToStringVectorException("Input file " + fileName + " not found.");
		}

		return inputVec;
	}
	
	/**********************
	 * Writing the AST
	 ************************************/
	public static boolean WriteAST(AST ast, String outfile) {
		Vector astFile = new Vector();
		astFile.addElement("------ MODULE AST -------");
		astFile.addElement("EXTENDS TLC");
		astFile.addElement("fairness == \"" + PcalParams.FairnessOption + "\"");
		astFile.addElement(" ");
		astFile.addElement("ast == ");
		astFile.addElement(ast.toString());
		astFile.addElement("==========================");
		try {
			WriteStringVectorToFile(astFile, outfile);
		} catch (StringVectorToFileException e) {
			Logger.getLogger("PGo Util").severe(e.getMessage());
			return false;
		}
		Logger.getLogger("PGo Util").info("Wrote file " + outfile);
		return true;
	}

}
