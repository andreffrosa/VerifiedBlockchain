

public class Worker /*implements Runnable*/ {

	/*@
		predicate WorkerInv() =
				    this.queue |-> ?q
				&*& this.b_chain |-> ?bc
				&*& isBlockchain(bc)
				&*& q != null &*& CQueueInv(q);
	@*/

	private CQueue queue;
	private BlockChain b_chain;

	public Worker(CQueue queue, BlockChain b_chain) 
	//@ requires isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue);
	// ensures WorkerInv() // isto nao vai impedir depois criar outros workers a apontar para o mesmo sitio e ate impedir usar a bchain na main?
	//@ ensures isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue);
	{
		this.queue = queue;
		this.b_chain = b_chain;
	}
	
	public void work() 
	//@ requires this.b_chain |-> ?bc &*& isBlockchain(bc) &*& this.queue |-> ?q &*& q != null &*& CQueueInv(q);
	//@ ensures isBlockchain(bc) &*& q != null &*& CQueueInv(q);
	{
	
		Transaction[] ts = new Transaction[Block.MAX_TX];
		int counter = 0;
		while( counter < Block.MAX_TX )
		//@ invariant 0 <= counter &*& counter <= Block.MAX_TX &*& array_slice(ts,0,ts.length,_) &*& isBlockchain(bc) &*& q != null &*& CQueueInv(q);
		{
			Transaction t = queue.dequeue();
			
			boolean valid = b_chain.balanceOf(t.getSender()) >= t.getAmount();
			
			if(valid) {
				ts[counter] = t;
				counter++;
			} 
			//else {
				// Discard t
			//}
		}
		
		boolean status = b_chain.appendBlock(ts); // Fazer o que?
	}
	
}
