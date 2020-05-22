

public class Producer {

	public static final int MAX_SLEEP = 10;
	public static final int TRANSFERENCE_FACTOR = 15; 

	public Producer() 
	//@ requires true;
	//@ ensures true;
	{
	}

	public void produce(CQueue queue, BlockChain b_chain) 
	//@ requires isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue) &*& [_]System.out |-> ?o &*& o != null;
	//@ ensures isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue) &*& o != null;
	{
		double ratio = TRANSFERENCE_FACTOR * 0.01;
		
		int counter = 0; 
		while( counter < Block.MAX_TX )
		//@ invariant 0 <= counter &*& counter <= Block.MAX_TX &*& isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue);
		{
			int sender = Util.randomInt(0, Block.MAX_ID-1);
			int receiver = Util.randomInt(0, Block.MAX_ID-1);
			
			//@ open isBlockchain(b_chain);
			int max_amount = (int) (b_chain.balanceOf(sender) * ratio);
			
			if(max_amount > 0) {
				int amount = Util.randomInt(1, max_amount);
		
				queue.enqueue( new Transaction(sender, receiver, amount) );
				
				counter++;
				
				try{ Thread.sleep(Util.randomInt(0, MAX_SLEEP)); } catch(InterruptedException e) {}
			}
		}
	}

}
