
//import verifast.internal.*;

public class Client {

    private static final int INITIAL_BALANCE = 100;
    private static final int TRANSFERENCE_FACTOR = 15; 
    private static final int ITERATIONS = 110;
    private static final int QUEUE_SIZE = 150;

    public static void main(String[] args)
    //@ requires true;
    //@ ensures true;
    {
    	//double TRANSFERENCE_FACTOR = 0.15;
    	
        // Create a blockchain with an initial block
        int[] initial_balances = new int[Block.MAX_ID];
        for(int i = 0; i < Block.MAX_ID; i++) 
        //@ invariant 0 <= i &*& i <= Block.MAX_ID &*& array_slice(initial_balances,0,initial_balances.length,_);
        {
        	initial_balances[i] = Client.INITIAL_BALANCE;
        }
        //@ close ValidCheckpoint(initial_balances);
        
        int nonce = SummaryBlock.mine(0, initial_balances);
        BlockChain b_chain = new BlockChain(nonce, initial_balances);

	// Transaction Queue
	CQueue queue = new CQueue(QUEUE_SIZE);

	// Worker
	Worker w1 = new Worker(queue, b_chain);

	// Append new Blocks to the blockchain
	for(int i = 0; i < ITERATIONS; i++) 
	//@ invariant 0 <= i &*& i <= ITERATIONS &*& b_chain.BlockchainInv(_, _, _);
	{
		// Produce some new transactions
		for(int j = 0; j < Block.MAX_TX; j++) {
			int sender = (int)(Math.random()*Block.MAX_ID);
			int receiver = (int)(Math.random()*Block.MAX_ID);
			int amount = (int)(Math.random()*b_chain.balanceOf(sender)*(TRANSFERENCE_FACTOR/100.0));
			
			queue.enqueue( new Transaction(sender, receiver, amount) );
		}
		
		// Consume
		w1.work();
	}
	
	// Print all the balances
	System.out.println("\nBalances");
	int[] balances = b_chain.getBalances();
	for(int j = 0; j < Block.MAX_ID; j++) {
		System.out.printf("% 3d : % 3d \n", j, balances[j]);
	}


        
       // b_chain.appendBlock(b); // DEVIA DAR ERRO
        



        // como é que esta class vai ficar??

        // preciso criar um produtor que está sempre a criar transções e a metê-as na queue.
        // a transaction queue sacahar não precsa de umacass e deve ficar com a aua teo de producers e consumers

        // fazer o worer especia dos blocos sumário

/*        for(int i = 0; i < 10; i++) {
            Transaction t = new Transaction(1, 2, 100);
            TransactionQueue.getInstance().insertTransaction(t);
        }

        System.out.println("fhaifohaf");

        Worker w = new Worker();
        w.mine();


*/
    }

}
