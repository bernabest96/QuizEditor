package view;

import controller.IController;

public interface IView {
	public String[] getSelectedAnswer();
	public String getCategory();
	public void displayInfoErrorMessages(String message);
	public void displayQuizMessages(String message);
	public void registerListener(IController controller);
}
