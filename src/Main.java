import model.McModel;
import model.TfModel;
import view.IView;
import view.View;

import java.io.IOException;

import controller.Controller;

public class Main {

	private static final String FILEPATH_MC_DEFAULT = "C:\\Users\\berna\\Davide\\Anno Extra\\Testing e Verifica del Software\\Progetto\\file_to_test\\mc_quiz.txt";
	private static final String FILEPATH_TF_DEFAULT = "C:\\Users\\berna\\Davide\\Anno Extra\\Testing e Verifica del Software\\Progetto\\file_to_test\\tf_quiz.txt";
	
	public static void main(String[] args) {
		IView v;
		McModel model_mc;
		TfModel model_tf;
		try {
			model_mc = new McModel(FILEPATH_MC_DEFAULT);
			model_tf = new TfModel(FILEPATH_TF_DEFAULT);
			v = new View();
			Controller c = new Controller(model_mc, model_tf, v);
		} catch (IOException e) {
			e.printStackTrace();
		} catch (Exception e) {
			e.printStackTrace();
		}
		
	}

}
