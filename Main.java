
//import verifast.internal.*;

/*@
predicate queue_frac(real f) = true;

predicate b_chain_frac(real f) = true;
@*/

public class Main {

    public static final int INITIAL_BALANCE = 100;
    public static final int ITERATIONS = 110;
    public static final int QUEUE_SIZE = 300;
    
    public static final int N_WORKERS = 10;
    public static final int N_PRODUCERS = 20;
    
    public static final int SLEEP_INTERVAL = 60*1000; 

    public static void main(String[] args)
    //@ requires [_]System.out |-> ?o &*& o != null;
    //@ ensures true;
    {
        // Create a blockchain with an initial block
        int[] initial_balances = new int[Block.MAX_ID];
        
        for(int i = 0; i < Block.MAX_ID; i++) 
        /*@ invariant 0 <= i &*& i <= Block.MAX_ID 
        	&*& array_slice_deep(initial_balances, 0, i, Positive, unit, ?elems, ?vls)
        	&*& array_slice(initial_balances,i,initial_balances.length,_);
        @*/
        {
        	initial_balances[i] = INITIAL_BALANCE;
        }
        //@ close ValidSummary(initial_balances);
        
        CBlockChain b_chain = new CBlockChain(initial_balances);

	// Transaction Queue
	CQueue queue = new CQueue(QUEUE_SIZE);

	// Create Producers
	//@ close queue_frac(1/2);
	//@ close b_chain_frac(1/2);
	for(int i = 0; i < N_PRODUCERS; i++) 
	/*@ invariant b_chain_frac(?bf) &*& [bf]isCBlockchain(b_chain) 
		  &*& queue_frac(?qf) &*& [qf]isCQueue(queue) 
		  &*& [_]System.out |-> o &*& o != null;
	@*/
	{
		//@ open queue_frac(qf);
		//@ close queue_frac(qf/2);
		//@ open b_chain_frac(bf);
		//@ close b_chain_frac(bf/2);
		
		Producer p = new Producer(queue, b_chain);
		new Thread(p).start();
		
		//@ close queue_frac(qf/4);
		//@ close b_chain_frac(bf/4);
	}

	// Create Workers
	for(int i = 0; i < N_WORKERS; i++) 
	/*@ invariant b_chain_frac(?bf) &*& [bf]isCBlockchain(b_chain) 
		  &*& queue_frac(?qf) &*& [qf]isCQueue(queue) 
		  &*& [_]System.out |-> o &*& o != null;
	@*/
	{
		//@ open queue_frac(qf);
		//@ close queue_frac(qf/2);
		//@ open b_chain_frac(bf);
		//@ close b_chain_frac(bf/2);
		
		Worker w = new Worker(queue, b_chain);
		new Thread(w).start();
		
		//@ close queue_frac(qf/4);
		//@ close b_chain_frac(bf/4);
	}

	while(true) 
	/*@ invariant b_chain_frac(?bf) &*& [bf]isCBlockchain(b_chain) 
		  &*& [_]System.out |-> o &*& o != null;
	@*/
	{
		// Print all the balances
		//int[] balances = b_chain.getBalances();
		//printBalances(balances);
		
		// @ close [bf]isCBlockchain(b_chain);
	
		// try{ Thread.sleep( SLEEP_INTERVAL ); } catch(InterruptedException e) {}	
	}

    }
    
    private static void printBalances(int[] balances) 
    //@ requires array_slice(balances,0,balances.length,_) &*& [_]System.out |-> ?o &*& o != null;
    //@ ensures array_slice(balances,0,balances.length,_) &*& o != null;
    {
    	System.out.println("\nBalances\nAccount | Coins");
	//@ assert array_slice(balances,0,balances.length,_);
	for(int j = 0; j < balances.length; j++) 
	/*@ invariant 0 <= j &*& j <= balances.length
		&*& [_]System.out |-> ?x &*& x != null
		&*& array_slice(balances,0,balances.length,_); 
	@*/
	{ 
		String txt = "    "
		           + (j < 10 ? "  " : j < 100 ? " " : "")
		           + String.valueOf(j)
		           + " | "
		           + (balances[j] < 10 ? "  " : balances[j] < 100 ? " " : "")
		           + String.valueOf(balances[j]);
		           
		System.out.println(txt);
	}
    }
}