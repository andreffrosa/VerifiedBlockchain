

public final class Worker implements Runnable {
	
	/*@
	
	predicate WorkerInv() = this.queue |-> ?q 
			      &*& this.b_chain |-> ?bc
			      &*& [_]isCQueue(q)
			      &*& [_]isCBlockchain(bc)
			      &*& this.max_retries |-> ?r
			      &*& r >= 0
			      &*& this.discard |-> ?d;
	
	predicate pre() = this.WorkerInv() &*& [_]System.out |-> ?o &*& o != null;
	
	predicate post() = true;
	
	@*/
	
	private CQueue queue;
	private CBlockChain b_chain;
	private int max_retries;
	private boolean discard;

	public Worker(CQueue queue, CBlockChain b_chain, int max_retries, boolean discard) 
	//@ requires b_chain_frac(?bf) &*& [bf]isCBlockchain(b_chain) &*& queue_frac(?qf) &*& [qf]isCQueue(queue) &*& max_retries > 0 &*& [_]System.out |-> ?o &*& o != null;
	//@ ensures pre();
	{
		this.queue = queue;
		this.b_chain = b_chain;
		this.max_retries = max_retries;
		this.discard = discard;
		//@ close WorkerInv();
		//@ close pre();
	}
	
	public void run() 
	//@ requires pre();
	//@ ensures post();
	{
		while(true) 
		/*@ invariant WorkerInv() &*& [_]System.out |-> ?o2 &*& o2 != null;
		@*/
		{
			work();
		}
	}
	
	public void work() 
	//@ requires WorkerInv() &*& [_]System.out |-> ?o &*& o != null;
	//@ ensures WorkerInv() &*& o != null;
	{
		Transaction[] ts = new Transaction[Block.MAX_TX];

		for(int i = 0; i < Block.MAX_TX; i++)
		/*@ invariant 0 <= i &*& i <= Block.MAX_TX 
			&*& array_slice_deep(ts, 0, i, TransHash, unit, ?transactions, ?hashes)
			&*& array_slice(ts,i,ts.length,_) 
			&*& WorkerInv();
		@*/
		{
			//@ open WorkerInv();
			//@ open isCQueue(queue);
			Transaction t = queue.dequeue();
			ts[i] = t;

		} 
		//@ close ValidSimple(ts, ?transactions, ?hashes);

		boolean status = false;
		
		// Re-try the insertion
		//@ open WorkerInv();
		for(int i = 0; i < this.max_retries && !status; i++) 
		/*@ invariant (!status ? ValidSimple(ts, transactions, hashes) : true)
			&*& this.queue |-> ?q 
			&*& this.b_chain |-> ?bc
			&*& [_]isCQueue(q)
			&*& [_]isCBlockchain(bc)
			&*& this.max_retries |-> ?r
			&*& r >= 0
			&*& this.discard |-> ?d
			&*& [_]System_out(o) &*& o != null
			&*& 0 <= i &*& i <= r;
		@*/
		{
			//@ open isCBlockchain(b_chain);
			status = b_chain.appendBlock(ts);
		}
		
		// Re-insert transactions in the queue
		if(!status) {
			//@ open ValidSimple(ts, ?elms, ?vls);
			
			for(int j = 0; j < Block.MAX_TX; j++ ) 
			/*@ invariant 0 <= j &*& j <= Block.MAX_TX 
					&*& WorkerInv()
					&*& array_slice_deep(ts, 0, ts.length, TransHash, unit, ?trans, ?hx)
					&*& [_]System_out(o) &*& o != null;	 
			@*/
			{
				Transaction t = ts[j];
				ts[j] = null;
				
				if(t != null) {
					if(this.discard) {
						int sender = t.getSender();
						int receiver = t.getReceiver();
						int amount = t.getAmount();
						String txt = "["+Util.time()+"] "
							   + "[DISCARDED TRANSACTION]"
							   + " from " + (sender < 10 ? "  " : sender < 100 ? " " : "") + String.valueOf(sender)
							   + " to " + (receiver < 10 ? "  " : receiver < 100 ? " " : "") + String.valueOf(receiver)
							   + " " + (amount < 10 ? "  " : amount < 100 ? " " : "") + String.valueOf(amount) + " coins.";
						System.out.println(txt);
					} else {
						//@ open WorkerInv();
						//@ open isCBlockchain(b_chain);
						//@ open isCQueue(queue);
						queue.enqueue(t); // May block the worker if the queue is full
					}
				}	
			}
		}
	}
	
}
