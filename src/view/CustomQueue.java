package view;

import static org.junit.Assert.assertArrayEquals;

import java.util.LinkedList;
import java.util.Queue;

public class CustomQueue implements ICustomQueue{
	// public invariant max_capacity > 0;
	// public invariant queue.size() >= 0;
	// public invariant queue.size() <= max_capacity;
	private /* non_null */ /* spec_public */ LinkedList<String> queue;
	private /* spec_public */ int max_capacity;
	
	//requires max_capacity > 0;
	public CustomQueue(int max_capacity){
		if (max_capacity <= 0) {
			throw new IllegalArgumentException("La capacità massima deve essere superiore a 1");
		}
		queue = new LinkedList<String>();
		assert max_capacity > 0;
		this.max_capacity = max_capacity;
	}

	// also ensures \result <==> queue.size() == max_capacity;
	@Override
	public boolean enqueue(/* non_null */ String e) {
		if (e == null) {
			throw new IllegalArgumentException("Valore nullo");
		}
		queue.addLast(e);
		if (queue.size() == max_capacity + 1) {
			queue.removeFirst();
		}
		assert 0<=queue.size() && queue.size() <= max_capacity : "Violazione della capacità corrente: " + queue.size() + "; dimensione massima : " + max_capacity + ";";
		return queue.size() == max_capacity;
	}
	
	// also ensures \result <==> queue.isEmpty();
	@Override
	public boolean isEmpty() {
		//assert queue.isEmpty() <==> queue.size() == 0;
		assert (!queue.isEmpty() || queue.size() == 0)
			&& (!(queue.size() == 0) || queue.isEmpty());
		return queue.isEmpty();
	}
	
	// also ensures queue.size() == 0;
	@Override
	public void reset() {
		queue.clear();
		assert queue.size() == 0;
	}
	//Ricontrolla
	// also ensures \result != null;
	@Override
	@SuppressWarnings("unchecked")
	public String[] getArray() {
		return (String[]) queue.toArray();
	}
	
	//come di concatena una stringa
	// also ensures \result.equals(\strcat int i; 0<=i && i<queue.size(); queue.get(i).toString() + System.lineSeparator());
	@Override
	public String toString() {
		String str = "";
		for (String t : queue) {
			str += t.toString() + System.lineSeparator();
		}
		return str;
	}
	
	// also ensures \result <==> o != null && o instanceof CustomQueue && ((CustomQueue) o).queue.equals(this.queue) && ((CustomQueue) o).max_capacity == this.max_capacity;
	@Override
	public boolean equals(Object o) {
		if (o == null)	return false;
		if (!(o instanceof CustomQueue))	return false;
		@SuppressWarnings("unchecked")
		CustomQueue cq = (CustomQueue) o;
		return cq.queue.equals(this.queue) && cq.max_capacity == this.max_capacity;
	}

	// also ensures \result >= 0;
	@Override
	public int size() {
		return queue.size();
	}

	@Override
	public int maxSize() {
		return max_capacity;
	}

	// also ensures \result <==> queue.size() == max_capacity;
	@Override
	public boolean hasReachedMaxsize() {
		return queue.size() == max_capacity;
	}
}
