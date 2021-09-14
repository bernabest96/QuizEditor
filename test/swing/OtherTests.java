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

public class OtherTests {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
//		String s = "aaa\nbbbb\ncccc\n";
//		String[] ss = s.split("\n");
//		System.out.println(s.split("\n")[s.split("\n").length - 1]);
//		for (String sr : ss) {
//			System.out.println(sr.toString());
//		}
//		//ultima riga esce null
		String filename = "./test/swing/file.txt";
		File file = new File(filename);
//		try {
//			BufferedReader br = new BufferedReader(new FileReader(file));
//			br.mark(1000);
//			String l1 = br.readLine();
//			String l2 = br.readLine();
//			System.out.println(l1);
//			System.out.println(l2);
//			String[] lsplit = l2.split("\",\"");
//			String[] expected = new String[] {"a1", "a2", "a3"};
//			for (int i = 0; i < lsplit.length; i++) {
//				lsplit[i] = lsplit[i].replace("\"", "");
//				System.out.println("char : " + lsplit[i]);
//				assert lsplit[i].equals(expected[i]) : "Non sono uguali";
//			}
//			br.close();
//		} catch (FileNotFoundException e) {
//			e.printStackTrace();
//		} catch (IOException e) {
//			e.printStackTrace();
//		}
		
		FileWriter fw;
		try {
			fw = new FileWriter(filename,true);
			fw.write("add a line\n");//appends the string to the file
		    fw.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} //the true will append the new data
	    
		
		
		
	}

}
