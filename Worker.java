

public class Worker /*implements Runnable*/ {
/*
	
		predicate WorkerInv() =
				    this.queue |-> ?q
				&*& this.b_chain |-> ?bc
				&*& isBlockchain(bc)
				&*& q != null &*& CQueueInv(q);
	

	private CQueue queue;
	private BlockChain b_chain;*/

	public Worker() 
	// requires isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue);
	// ensures WorkerInv() // isto nao vai impedir depois criar outros workers a apontar para o mesmo sitio e ate impedir usar a bchain na main?
	// ensures isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue);
	//@ requires true;
	//@ ensures true;
	{
		//this.queue = queue;
		//this.b_chain = b_chain;
	}
	
	public void work(CQueue queue, BlockChain b_chain) 
	//@ requires isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue) &*& [_]System.out |-> ?o &*& o != null;
	//@ ensures isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue) &*& o != null;
	{
		Transaction[] ts = new Transaction[Block.MAX_TX];
		int i = 0;
		while( i < Block.MAX_TX )
		/*@ invariant 0 <= i &*& i <= Block.MAX_TX 
			&*& array_slice_deep(ts, 0, i, TransHash, unit, ?transactions, ?hashes)
			&*& array_slice(ts,i,ts.length,_) 
			&*& isBlockchain(b_chain) 
			&*& queue != null &*& CQueueInv(queue);
		@*/
		{
			Transaction t = queue.dequeue();
			//@ assert TransHash(_, t, _);
			//@ open TransHash(_, t, _);
			//@ assert t != null;
			ts[i] = t;
			i++;

		} 
		//@ close ValidSimple(ts, _);
		
		//@ open isBlockchain(b_chain);
		boolean status = b_chain.appendBlock(ts);
		
		// Re-insert transactions in the queue
		if(!status) {
			for(int j = 0; j < Block.MAX_TX; j++ ) 
			/*@ invariant 0 <= j &*& j <= Block.MAX_TX 
					&*& array_slice_deep(ts, j+1, ts.length, TransHash, unit, ?trans, ?hx)
					&*& array_slice(ts,0,j,_); // como fazer isto?
			
			@*/
			{
				queue.enqueue(ts[j]);
				ts[j] = null; // ?
			}
		}
	}
	
}
