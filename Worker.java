

public class Worker /*implements Runnable*/ {

	private CQueue queue;
	private BlockChain b_chain;

	public Worker(CQueue queue, BlockChain b_chain) 
	// requires isBlockchain(b_chain) &*& isQueue(queue);
	// ensures isBlockchain(b_chain) &*& isQueue(queue);
	{
		this.queue = queue;
		this.b_chain = b_chain;
	}
	
	public void work() {
	
		Transaction[] ts = new Transaction[Block.MAX_TX];
		for(int j = 0; j < Block.MAX_TX; j++) {
			ts[j] = queue.dequeue();
		}
		int hp = b_chain.headHash();
		
		int nonce = SimpleBlock.mine(hp, ts);
		
		boolean status = b_chain.appendBlock(hp, nonce, ts); // fazer o que com isto?
		
		//System.out.printf("%s : %b \n", "Simple", status);
		
		if(b_chain.isNextSummary()) {
			int[] balances = b_chain.getBalances();
			hp = b_chain.headHash();
			
			nonce = SummaryBlock.mine(hp, balances);
			
			b_chain.appendSummary(hp, nonce, balances);
			
			//System.out.printf("%s : %b \n", "Summary", status);
        	}
	}
	
}
