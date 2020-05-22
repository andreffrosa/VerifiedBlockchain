

public class Worker {


	public Worker() 
	//@ requires true;
	//@ ensures true;
	{}
	
	public void work(CQueue queue, BlockChain b_chain) 
	//@ requires isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue) &*& [_]System.out |-> ?o &*& o != null;
	//@ ensures isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue) &*& o != null;
	{
		Transaction[] ts = new Transaction[Block.MAX_TX];
		//int i = 0;
		//while( i < Block.MAX_TX )
		for(int i = 0; i < Block.MAX_TX; i++)
		/*@ invariant 0 <= i &*& i <= Block.MAX_TX 
			&*& array_slice_deep(ts, 0, i, TransHash, unit, ?transactions, ?hashes)
			&*& array_slice(ts,i,ts.length,_) 
			&*& isBlockchain(b_chain) 
			&*& queue != null &*& CQueueInv(queue);
		@*/
		{
			Transaction t = queue.dequeue();
			ts[i] = t;

		} 
		//@ close ValidSimple(ts, ?transactions, ?hashes);
		
		//@ open isBlockchain(b_chain);
		boolean status = b_chain.appendBlock(ts);
		
		// Re-insert transactions in the queue
		if(!status) {
			//@ open ValidSimple(ts, ?elms, ?vls);
			
			for(int j = 0; j < Block.MAX_TX; j++ ) 
			/*@ invariant 0 <= j &*& j <= Block.MAX_TX 
					&*& queue != null &*& CQueueInv(queue)
					&*& array_slice_deep(ts, 0, ts.length, TransHash, unit, ?trans, ?hx);	 
			@*/
			{
				Transaction t = ts[j];
				ts[j] = null;
				
				if(t != null)
					queue.enqueue(t);
			}
		}
	}
	
}
