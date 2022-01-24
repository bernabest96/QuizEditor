package model;

public class AnswerMC implements IMCAnswers {

	//@ public invariant line >= 0;
	//@ public invariant category != null && !category.isEmpty();
	//@ public invariant question != null && !question.isEmpty();
	//@ public invariant A != null && B != null && C != null && D != null;
	//@ public invariant !A.isEmpty() && !B.isEmpty() || !C.isEmpty() && !D.isEmpty();
	//@ public invariant correctAnswer != null && !correctAnswer.isEmpty();
	//@ public invariant caption != null && !caption.isEmpty();
	//@ public invariant (\exists int i; 0<= i && i < ANSWERS_TYPE.length; correctAnswer.equals(ANSWERS_TYPE[i]));
	
	private /*@ spec_public @*/ int line;
	private /*@ spec_public @*/ static final String[] ANSWERS_TYPE = {"A", "B", "C", "D"};
	private /*@ spec_public @*/ String category;
	private /*@ spec_public @*/ String question;
	private /*@ spec_public @*/ String A, B, C, D;
	private /*@ spec_public @*/ String correctAnswer;
	private /*@ spec_public @*/ String caption;
 	
	//@ requires line >= 0;
	//@ requires category != null && !category.isEmpty();
	//@ requires question != null && !question.isEmpty();
	//@ requires A != null && B != null && C != null && D != null;
	//@ requires !A.isEmpty() && !B.isEmpty() || !C.isEmpty() && !D.isEmpty();
	//@ requires correctAnswer != null && !correctAnswer.isEmpty();
	//@ requires caption != null && !caption.isEmpty();
	//@ requires (\exists int i; 0 <= i && i < ANSWERS_TYPE.length; correctAnswer.equals(ANSWERS_TYPE[i]));
	public AnswerMC(int line, String category, String question, String A, 
			String B, String C, String D, String correctAnswer, String caption) {
		//checks
		if (line < 0)	throw new IllegalArgumentException("La linea non deve essere negativa!");
		if (category == null || question == null || A == null || B == null || C == null ||
				D == null || correctAnswer == null || caption == null) {
			throw new IllegalArgumentException("Alcune stringhe sono nulle");
		}
		if (category.isEmpty() || question.isEmpty() || A.isEmpty() || B.isEmpty() || C.isEmpty()
				|| D.isEmpty() || correctAnswer.isEmpty() || caption.isEmpty()) {
			throw new IllegalArgumentException("Alcune stringhe sono vuote");
		}
		boolean notOk = true;
		for (String ANS : ANSWERS_TYPE) {
			notOk = notOk && !correctAnswer.equals(ANS);
		}
		if (notOk) {
			throw new IllegalArgumentException("Correct Answers NON è A, B, C, D");
		}
		
		this.line = line;
		this.category = category;
		this.question = question;
		this.A = A;
		this.B = B;
		this.C = C;
		this.D = D;
		this.correctAnswer = correctAnswer;
		this.caption = caption;
	}
	
	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public String getCategory() {
		return category;
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
	
	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public String getCorrectAnswer() {
		return correctAnswer;
	}

	/**
	 * ONLY FOR TESTING
	 * */
	//@ also ensures \result != null && \result.length == 4 && (\forall int i; 0<= i && i < 4; \result[i] != null && !(\result[i].isEmpty()));
	@Override
	public String[] getMCAnswers() {
		String[] answers = {A, B, C, D};
		return answers;
	}

	/**
	 * ONLY FOR TESTING
	 * */
	//@ also requires answer != null && answer.isEmpty() && (\exists int i; 0 <= i && i < ANSWERS_TYPE.length; answer.equals(ANSWERS_TYPE[i]));
	//@ also ensures \result <==> correctAnswer.equals(answer);
	@Override
	public boolean isCorrect(String answer) {
		if (answer == null) {
			throw new IllegalArgumentException("La stringa di input è nulla");
		}
		if (answer.isEmpty()) {
			throw new IllegalArgumentException("La stringa di input è vuota");
		}
		boolean notOk = true;
		for (String ANS : ANSWERS_TYPE) {
			notOk = notOk && !answer.equals(ANS);
		}
		if (notOk) {
			throw new IllegalArgumentException("La stringa di input non corrisponde ad A, B, C o D");
		}
		return correctAnswer.equals(answer);
	}

	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public String getA() {
		return A;
	}
	
	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public String getB() {
		return B;
	}

	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public String getC() {
		return C;
	}

	/**
	 * ONLY FOR TESTING
	 * */
	@Override
	public String getD() {
		return D;
	}
	
	/*@ also ensures \result <==> (o != null && (o instanceof AnswerMC) && 
	  (category.equals(((AnswerMC) o).category) && question.equals(((AnswerMC) o).question))); 
	  @*/
	@Override
	public boolean equals(Object o) {
		if (o == null) {
			return false;
		}
		if (!(o instanceof AnswerMC)) {
			return false;
		}
		assert o instanceof AnswerMC;
		AnswerMC a = (AnswerMC) o;
		return this.category.equals(a.category) && this.question.equals(a.question);
	}

	//@ also ensures line == 0 <==> \result.equals("Nessuna linea del file è associata al quiz");
	//  also ensures line > 0 <==> \result.contains(QUOTE) && !\result.contains(DASHQUOTE);
	/*@ also ensures line > 0 <==> \result.equals("Line " + line + ": " + 
	"\"" + category.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + question.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + A.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + B.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + C.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + D.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + correctAnswer.replace(DASHQUOTE, QUOTE) + 
	"\",\"" + caption.replace(DASHQUOTE, QUOTE) + "\"");
	@*/
	@Override
	public String toStringWithLine() {
		if (line == 0) {
			return "Nessuna linea del file è associata al quiz";
		}
		assert line > 0 : "linea negativa o zero";
		String s = "\"" + category.replace(DASHQUOTE, QUOTE) + 
				"\",\"" + question.replace(DASHQUOTE, QUOTE) + 
				"\",\"" + A.replace(DASHQUOTE, QUOTE) + 
				"\",\"" + B.replace(DASHQUOTE, QUOTE) + 
				"\",\"" + C.replace(DASHQUOTE, QUOTE) + 
				"\",\"" + D.replace(DASHQUOTE, QUOTE) + 
				"\",\"" + correctAnswer.replace(DASHQUOTE, QUOTE) + 
				"\",\"" + caption.replace(DASHQUOTE, QUOTE) + "\"";
		return "Line " + line + ": " + s;
	}

	
	/*@ also ensures \result.equals("\"" + category.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
	+ "\",\"" + question.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
	+ "\",\"" + A.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
	+ "\",\"" + B.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
	+ "\",\"" + C.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
	+ "\",\"" + D.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
	+ "\",\"" + correctAnswer.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
	+ "\",\"" + caption.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) + "\"");
	@*/
	@Override
	public String toStringToFile() {
		return "\"" + category.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
				+ "\",\"" + question.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
				+ "\",\"" + A.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
				+ "\",\"" + B.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
				+ "\",\"" + C.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) 
				+ "\",\"" + D.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
				+ "\",\"" + correctAnswer.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR)
				+ "\",\"" + caption.replace(QUOTE, DASHQUOTE).replace(System.lineSeparator(), WIN_LINE_SEPARATOR) + "\"";
	}
	
	
	
}
