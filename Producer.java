

public final class Producer implements Runnable {

	public static final int TRANSFERENCE_FACTOR = 15; 
	
	/*@
	
	predicate ProducerInv() = this.queue |-> ?q 
			      &*& this.b_chain |-> ?bc
			      &*& this.max_sleep |-> ?s
			      &*& s >= 0
			      &*& [_]isCQueue(q)
			      &*& [_]isCBlockchain(bc);
	
	predicate pre() = this.ProducerInv();
	
	predicate post() = true;
	
	@*/
	
	private CQueue queue;
	private CBlockChain b_chain;
	private int max_sleep;

	public Producer(CQueue queue, CBlockChain b_chain, int max_sleep) 
	//@ requires b_chain_frac(?bf) &*& [bf]isCBlockchain(b_chain) &*& queue_frac(?qf) &*& [qf]isCQueue(queue) &*& max_sleep >= 0;
	//@ ensures pre();
	{
		this.queue = queue;
		this.b_chain = b_chain;
		this.max_sleep = max_sleep;
		//@ close pre();
	}
	
	public void run() 
	//@ requires pre();
	//@ ensures post();
	{
		while(true) 
		/*@ invariant ProducerInv();
		@*/
		{
			produce();
		}
	}

	public void produce() 
	//@ requires ProducerInv();
	//@ ensures ProducerInv();
	{
		double ratio = TRANSFERENCE_FACTOR * 0.01;
		
		int sender = Util.randomInt(0, Block.MAX_ID-1);
		int receiver = Util.randomInt(0, Block.MAX_ID-1);
		
		//@ open ProducerInv();
		//@ open isCBlockchain(b_chain);
		int max_amount = (int) (b_chain.balanceOf(sender) * ratio);
			
		if(max_amount > 0) {
			int amount = Util.randomInt(1, max_amount);
			
			//@ open ProducerInv();
			//@ open isCBlockchain(b_chain);
			//@ open isCQueue(queue);
			queue.enqueue( new Transaction(sender, receiver, amount) );
				
			try{ Thread.sleep( Util.randomInt(0, this.max_sleep) ); } catch(InterruptedException e) {}
		}
	}

}
