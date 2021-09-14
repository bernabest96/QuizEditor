package model;

public class AnswerTF implements ITFAnswers {

	//@ public invariant category != null && !category.isEmpty();
	//@ public invariant question != null && !question.isEmpty();
	//@ public invariant caption != null && !caption.isEmpty();
	private /*@ spec_public @*/ boolean correctAnswer;
	private /*@ spec_public @*/ String category;
	private /*@ spec_public @*/ String question;
	private /*@ spec_public @*/ String caption;
	
	//@ requires category != null && !category.isEmpty();
	//@ requires question != null && !question.isEmpty();
	//@ requires caption != null && !question.isEmpty();
	public AnswerTF(String category, String question, boolean correctAnswer, String caption) {
		if (category == null || question == null || caption == null) {
			throw new IllegalArgumentException("Hai inserito in input valori nulli");
		}
		if (category.isEmpty() || question.isEmpty() || caption.isEmpty()) {
			throw new IllegalArgumentException("Hai inserito almeno una stringa vuota");
		}
		this.category = category;
		this.caption = question;
		this.caption = caption;
		this.correctAnswer = correctAnswer;
	}
	
	//@ also ensures \result <==> answer == correctAnswer;
	@Override
	public boolean isCorrect(boolean answer) {
		return correctAnswer == answer;
	}

	@Override
	public boolean getCorrectAnswer() {
		return correctAnswer;
	}

	@Override
	public String getQuestion() {
		return question;
	}

	@Override
	public String getCaption() {
		return caption;
	}
	
	//@ ensures \result != null && !(\result.isEmpty());
	@Override
	public String toString() {
		String tfStr = correctAnswer? "t" : "f";
		return "\"" + category + "\",\"" + question + "\",\"" + tfStr + "\",\"" + caption + "\"";
	}
	
	//@ also ensures \result <==> (o != null && !(o instanceof AnswerTF) && (category.equals(((AnswerTF) o).category) && question.equals(((AnswerTF) o).question)));
	@Override
	public boolean equals(Object o) {
		if (o == null) {
			return false;
		}
		if (!(o instanceof AnswerTF)) {
			return false;
		}
		AnswerTF a = (AnswerTF) o;
		return category.equals(a.category) && question.equals(a.question);
	}
}
