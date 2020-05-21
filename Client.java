
//import verifast.internal.*;

public class Client {

    public static final int INITIAL_BALANCE = 100;
    public static final int TRANSFERENCE_FACTOR = 15; 
    public static final int ITERATIONS = 110;
    public static final int QUEUE_SIZE = 150;

    public static void main(String[] args)
    //@ requires [_]System.out |-> ?o &*& o != null;
    //@ ensures true;
    {
        // Create a blockchain with an initial block
        int[] initial_balances = new int[Block.MAX_ID];
        //@ assert initial_balances |-> ?b;
        for(int i = 0; i < Block.MAX_ID; i++) 
        /*@ invariant 0 <= i &*& i <= Block.MAX_ID 
        	&*& array_slice_deep(b, 0, i, Positive, unit, ?elems, ?vls)
        	&*& array_slice(b,i,b,_);
        @*/
        {
        	initial_balances[i] = Client.INITIAL_BALANCE;
        }
        //@ close ValidSummary(initial_balances);
        
        BlockChain b_chain = new BlockChain(initial_balances);

	// Transaction Queue
	CQueue queue = new CQueue(QUEUE_SIZE);

	// Producer
	Producer p1 = new Producer(queue, b_chain);

	// Worker
	Worker w1 = new Worker(queue, b_chain);

	// Append new Blocks to the blockchain
	for(int i = 0; i < ITERATIONS; i++) 
	//@ invariant 0 <= i &*& i <= ITERATIONS &*& isBlockchain(b_chain) &*& queue != null &*& CQueueInv(queue);
	{
		// Produce some new transactions
		p1.produce();
		
		// Consume
		w1.work();
	}
	
	// Print all the balances
	System.out.println("\nBalances\nAccount | Coins");
	int[] balances = b_chain.getBalances();
	//@ assert array_slice(balances,0,balances.length,_);
	for(int j = 0; j < balances.length; j++) 
	/*@ invariant 0 <= j &*& j <= balances.length
		&*& [_]System.out |-> ?x &*& x != null
		&*& array_slice(balances,0,balances.length,_); 
	@*/
	{ 
		//System.out.printf("% 3d : % 3d \n", j, balances[j]);
		System.out.print("    ");
		System.out.print((j<10 ? "  " : j<100 ? " " : ""));
		System.out.print(j);
		System.out.print(" | ");
		System.out.print((balances[j]<10 ? "  " : balances[j]<100 ? " " : ""));
		System.out.println(balances[j]);
	}
    }
}
