package model;

public interface IMCAnswers extends IAnswers {
	public String[] getMCAnswers();
	public boolean isCorrect(String answer);
	public String getCorrectAnswer();
	public String getA();
	public String getB();
	public String getC();
	public String getD();
}
