package controller;

public interface IController {
	public boolean onInsertMCButtonPressed(String category, String question, String[] answers, String correctAns, String caption);
	public boolean onInsertTFButtonPressed(String category, String question, boolean correctAnserwer, String caption);
	public boolean onSearchButtonPressed(String category);
	public boolean onChangeMCFilePath(String filename);
	public boolean onChangeTFFilePath(String filename);
}
