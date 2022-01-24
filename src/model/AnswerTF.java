package model;

public class AnswerTF implements ITFAnswers {

	//@ public invariant line >= 0;
	//@ public invariant category != null && !category.isEmpty();
	//@ public invariant question != null && !question.isEmpty();
	//@ public invariant caption != null && !caption.isEmpty();
	private /*@ spec_public @*/ int line;
	private /*@ spec_public @*/ boolean correctAnswer;
	private /*@ spec_public @*/ String category;
	private /*@ spec_public @*/ String question;
	private /*@ spec_public @*/ String caption;
	
	//@ requires line >= 0;
	//@ requires category != null && !category.isEmpty();
	//@ requires question != null && !question.isEmpty();
	//@ requires caption != null && !question.isEmpty();
	public AnswerTF(int line, String category, String question, boolean correctAnswer, String caption) {
		if (line < 0)	throw new IllegalArgumentException("linea negativa");
		if (category == null || question == null || caption == null) {
			throw new IllegalArgumentException("Hai inserito in input valori nulli");
		}
		if (category.isEmpty() || question.isEmpty() || caption.isEmpty()) {
			throw new IllegalArgumentException("Hai inserito almeno una stringa vuota");
		}
		this.line = line;
		this.category = category;
		this.question = question;
		this.caption = caption;
		this.correctAnswer = correctAnswer;
	}
	
	/**
	 * ONLY FOR TESTING
	 * */
	//@ also ensures \result <==> answer == correctAnswer;
	@Override
	public boolean isCorrect(boolean answer) {
		return correctAnswer == answer;
	}

	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public boolean getCorrectAnswer() {
		return correctAnswer;
	}

	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public String getQuestion() {
		return question;
	}

	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public String getCaption() {
		return caption;
	}
	
	/*@ also ensures \result <==> (o != null && o instanceof AnswerTF &&
		(category.equals(((AnswerTF) o).category) && question.equals(((AnswerTF) o).question)));
	@*/
	//@   
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

	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public String getCategory() {
		return category;
	}
	
	//@ also ensures line == 0 <==> \result.equals("Nessuna linea del file è associata al quiz");
	//  also ensures line > 0 <==> \result.contains(QUOTE) && !\result.contains(DASHQUOTE);
	/*@ also ensures (line > 0 && correctAnswer) <==> \result.equals("Line " + line + ": " + 
	"\"" + category.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + question.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + "t" + 
	"\",\"" + caption.replace(DASHQUOTE, QUOTE) + "\"");
	@*/
	/*@ also ensures (line > 0 && !correctAnswer) <==> \result.equals("Line " + line + ": " + 
	"\"" + category.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + question.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + "f" + 
	"\",\"" + caption.replace(DASHQUOTE, QUOTE) + "\"");
	@*/
	@Override
	public String toStringWithLine() {
		if (line == 0) {
			return "Nessuna linea del file è associata al quiz";
		}
		//linea > 0
		assert line > 0 : "linea negativa o zero";
		String tfStr = correctAnswer? "t" : "f";
		String s =  "\"" + category.replace(DASHQUOTE, QUOTE) + "\",\"" + question.replace(DASHQUOTE, QUOTE) + "\",\"" + tfStr + "\",\"" + caption.replace(DASHQUOTE, QUOTE) + "\"";
		return "Line " + line + ": " + s;
	}

	
	/*@ also ensures correctAnswer <==> \result.equals("\"" + category.replace(QUOTE, DASHQUOTE) .replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
				+ "\",\"" + question.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
				+ "\",\"" + "t" + "\",\"" + caption.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
				+ "\""); 
	@*/
	/*@ also ensures !correctAnswer <==> \result.equals("\"" + category.replace(QUOTE, DASHQUOTE) .replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
				+ "\",\"" + question.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
				+ "\",\"" + "f" + "\",\"" + caption.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
				+ "\""); 
	@*/
	@Override
	public String toStringToFile() {
		String tfStr = correctAnswer? "t" : "f";
		return "\"" + category.replace(QUOTE, DASHQUOTE) .replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
				+ "\",\"" + question.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
				+ "\",\"" + tfStr + "\",\"" + caption.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
				+ "\"";
	}
}
