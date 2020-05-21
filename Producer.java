

public class Producer  /*implements Runnable*/ {

	/*@
		predicate ProducerInv() =
				    this.queue |-> ?q
				&*& this.b_chain |-> ?bc
				&*& isBlockchain(bc)
				&*& q != null &*& CQueueInv(q);
	@*/

	private CQueue queue;
	private BlockChain b_chain;

	public Producer(CQueue queue, BlockChain b_chain) 
	//@ requires isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue);
	// ensures WorkerInv() // isto nao vai impedir depois criar outros workers a apontar para o mesmo sitio e ate impedir usar a bchain na main?
	//@ ensures isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue);
	{
		this.queue = queue;
		this.b_chain = b_chain;
	}

	public void produce() 
	//@ requires true;
	//@ ensures true;
	{
		double ratio = Client.TRANSFERENCE_FACTOR / 100.0;
		
		int counter = 0; 
		while( counter < Block.MAX_TX )
		//@ invariant 0 <= counter &*& counter <= Block.MAX_TX &*& isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue);
		{
			int sender = Util.randomInt(0, Block.MAX_ID-1);
			int receiver = Util.randomInt(0, Block.MAX_ID-1);
			// assert ValidID(sender);
			
			int max_amount = (int) (b_chain.balanceOf(sender) * ratio);
			
			if(max_amount > 0) {
				int amount = Util.randomInt(1, max_amount);
		
				queue.enqueue( new Transaction(sender, receiver, amount) );
				
				counter++;
			}
		}
	}

}
