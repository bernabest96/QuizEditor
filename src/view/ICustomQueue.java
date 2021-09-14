package view;

/**
 * L'oggetto rappresenta una struttura dati a coda (LIFO), generica (parametro T), a capacità massima:
 * una volta raggiunta la capacità massima, ogni volta che si aggiunge un oggetto di T, l'ultimo oggetto
 * in coda viene eliminato.
 * @author berna
 *
 * @param <T> Tipo generico di oggetto (estende Object)
 */
public interface ICustomQueue<T> {

	/**
	 * Il metodo controlla che la coda abbia raggiunto la dimensione massima
	 * @return true se ha raggiunto la capacità massima, false altrimenti
	 */
	boolean hasReachedMaxsize();
	
	/**
	 * Inserisce in coda l'oggetto di tipo T (se raggiunge la capacità massima, elimina l'ultimo in coda).
	 * @param e Oggetto di tipo T inserito in coda
	 * @return true se la coda ha raggiunto la capacità massima (elimina l'ultimo elemento), false altrimenti
	 */
	boolean enqueue(T e);

	/**
	 * Ritorna la dimensione corrente della coda
	 * @return Dimensione corrente
	 */
	int size();
	
	/**
	 * Ritorna la dimensione massima della coda
	 * @return Dimensione massima
	 */
	int maxSize();
	
	/**
	 * Verifica se la coda è vuota
	 * @return true se vuota, false altrimenti
	 */
	boolean isEmpty();

	/**
	 * Svuota la coda
	 */
	void reset();

	/**
	 * Ritorna come array di tipo T gli elementi correnti nella coda
	 * @return array di tipo T della coda
	 */
	T[] getArray();

}