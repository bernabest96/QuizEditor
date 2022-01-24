package swing;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.util.regex.Pattern;

public class OtherTests {

	public static void main(String[] args) {
//		try {
//			BufferedWriter bw = new BufferedWriter(new FileWriter(new File("./test/swing/file.txt")));
//			bw.write("Scrivi cose" + System.lineSeparator());
//			bw.write("\\r\\n" + System.lineSeparator());
//			String s = "line separator \r\n";
//			s.replace("\r\n", "\\r\\n");
//			bw.write(s);
//			bw.close();
//		} catch (IOException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
		
		String ab = "aaaaaab";
		assert Pattern.matches("a+b", ab);
		String q = "\"pipp\\\"odsadklasj\",\"pattern\",\"pattern2\"";
		assert Pattern.matches("\"[^\" | (\\\")]+(\",\"[^\"]+)+\"", q) : "Attenzione";

		String DASHQUOTE = "\\\"";
		String QUOTE = "\"";
		String line = "\"category\",\"question\",\"rispA\",\"rispB\",\"rispC\",\"rispD\",\"A\",\"caption\"";
		assert Pattern.matches(QUOTE + "[^" + QUOTE + "]" + "(\",\"" + "[^" + QUOTE + "])+" + QUOTE, line) : "Pattern sbagliato";
	}

}
