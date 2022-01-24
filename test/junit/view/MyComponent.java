package junit.view;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JLabel;
import javax.swing.JPanel;

public class MyComponent extends JPanel implements ActionListener{
	/**
	 * 
	 */
	private static final long serialVersionUID = 1L;
	private JButton b;
	private JLabel l;
	boolean ok;
	
	public MyComponent() {
		ok = true;
		b = new JButton("OK");
		l = new JLabel("Label di prova");
		b.addActionListener(new ActionListener() {
			
			@Override
			public void actionPerformed(ActionEvent e) {
				// TODO Auto-generated method stub
				System.out.println("ok var: " + ok);
				if (ok) {
					l.setText("NO");
					
				}else {
					l.setText("OK");
				}
				ok = !ok;
			}
		});
		add(b); add(l);
	}

	@Override
	public void actionPerformed(ActionEvent e) {
		// TODO Auto-generated method stub
		System.out.print("Scooby doo");
		System.out.flush();
	}

}