


/*
   This class should be implemented in the course of the project
   development with the expected operations to add and inspect the
   blocks
*/

/*@
	inductive chain = nill | conc(chain, Block);

	fixpoint int len(chain c) {
	    switch(c) {
		case nill : return 0;
		case conc(c2, b) : return 1 + len(c2);
	    }
	}


    predicate isBlockchain(BlockChain bc;) = bc == null ? emp : bc.BlockchainInv(?h, ?hx, ?s, ?c);
    
    
@*/

/*

predicate validNextBlock(Block b, Block h, int s) =
					    b != null
					&*& h != null
					&*& h.BlockInv(_, _, ?hp, _)
					&*& b.BlockInv(h, hp, ?hx, _)
					&*& hx % 100 == 0
					&*& s % (BlockChain.SUMMARY_INTERVAL + 1) == 0 ? b.getClass() == SummaryBlock.class : b.getClass() == SimpleBlock.class;
*/

final class BlockChain {

	public static final int SUMMARY_INTERVAL = 10;

	/*@
	predicate BlockchainInv(Block h, int hx, int s, chain c) =
				    this.head |-> h
				&*& this.size |-> s
				&*& this.ch |-> c
				&*& s > 0
				&*& len(c) == s
				&*& h != null
				&*& c != nill
				&*& c == conc(_, h)
				&*& h.BlockInv(_, _, hx, _)
				//&*& hx % 100 == 0
				;
	@*/

	private Block head;
	private int size;
	//@ private chain ch; // ghost var

	private static void log(int size, String b) 
	//@ requires b != null &*& [_]System.out |-> ?o &*& o != null;
	//@ ensures o != null;
	{
		System.out.print("["+Util.time()+"] " + (size<10 ? "  " : size<100 ? " " : ""));
		System.out.print(size);
		System.out.println(" : " + b);
	}

	public BlockChain(int[] initial_balances)
	/*@ requires ValidSummary(initial_balances, ?vls) 
		&*& [_]System.out |-> ?o &*& o != null;
	@*/
	//@ ensures BlockchainInv(_, _, 1, _) &*& o != null;
	{
		int nonce = SummaryBlock.mine(0, initial_balances);
		
		SummaryBlock b = new SummaryBlock(null, nonce, initial_balances);
		
		//@ open ValidNonce(nonce, 0, sum(vls));
		//@ open b.BlockInv(null, 0, ?hx, nonce);
		//@ assert hx % 100 == 0;
		
		this.head = b;
		this.size = 1;
		//@ this.ch = conc(nill, this.head);
		
		log(this.size, "Summary");

		//@ close BlockchainInv(this.head, hx, 1, conc(nill, this.head));
	}
	
	/*public Block getHead()
	//@ requires BlockchainInv(?h, ?s, ?c);
	//@ ensures BlockchainInv(h, s, c) &*& result == h &*& result != null &*& c == conc(_, h);
	{
		//@ open BlockchainInv(h, s, c);
		//@ assert h.BlockInv(_, _, _, _);
		return this.head;
	}

	public int getSize()
	//@ requires BlockchainInv(?h, ?s, ?c);
	//@ ensures BlockchainInv(h, s, c) &*& result == s &*& result == len(c);
	{
		return this.size;
	}*/


	public boolean isNextSummary()
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c);
	//@ ensures BlockchainInv(h, hx, s, c) &*& result ? (s % (BlockChain.SUMMARY_INTERVAL + 1) == 0) : true;
	{
		return this.size % (BlockChain.SUMMARY_INTERVAL + 1) == 0;
	}
	
	private int headHash() 
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c);
	//@ ensures BlockchainInv(h, hx, s, c) &*& result == hx;
	{
		return this.head.hash();
	}

	private boolean appendSimple(int hp, int nonce, Transaction[] ts) 
	/*@ requires BlockchainInv(?h, hp, ?s, ?c) &*& ts.length == Block.MAX_TX 
				&*& array_slice_deep(ts,0,ts.length,TransHash,unit, ?els, ?vls) 
				&*& ValidNonce(nonce, hp, sum(vls)) 
				&*& s % (BlockChain.SUMMARY_INTERVAL + 1) != 0
				&*& [_]System.out |-> ?o &*& o != null; @*/
	//@ ensures o != null &*& result ? BlockchainInv(?b, _, s+1, conc(c, b)) : BlockchainInv(h, hp, s, c);
	{ 
		//if(this.head.hash() != hp) // e' preciso meter sequer? como meter na pre-cond? -> tem de se alterar a inv e meter no valid nextB
		//	return false;
		
		SimpleBlock b = new SimpleBlock(this.head, nonce, ts);
		
		//@ assert b.BlockInv(h, hp, ?hx1, nonce);
		
		int i = 0;
		boolean valid = true;
		while( i < Block.MAX_ID && valid ) // Esta validacao deveria vir de fora?
		//@ invariant i >= 0 &*& i <= Block.MAX_ID &*& b.BlockInv(h, hp, hx1, nonce);
		{
			valid = valid && b.balanceOf(i) > 0;
			i++;
		}
		
		// Se nao for valido, como recuperar a BlockInv da cabeca?

		if(valid) {
			this.head = b;
			this.size++;
			//@ this.ch = conc(c, b);
			
			//@ close BlockchainInv(b, _, s+1, conc(c, b));
			
			log(this.size, "Simple");
		} else {
			//@ open b.BlockInv(h, hp, hx1, nonce);
			//@ close BlockchainInv(h, hp, s, c);
		}

		return valid;
	}
	
	private boolean appendSummary(int hp, int nonce, int[] balances) 
	/*@ requires BlockchainInv(?h, hp, ?s, ?c) 
				&*& ValidSummary(balances, ?vls)  
				&*& ValidNonce(nonce, hp, sum(vls)) 
				&*& s % (BlockChain.SUMMARY_INTERVAL + 1) == 0
				&*& [_]System.out |-> ?o &*& o != null; @*/
	//@ ensures o != null &*& result ? BlockchainInv(?b, _, s+1, conc(c, b)) : BlockchainInv(h, hp, s, c);
	{
		//if(this.head.hash() != hp) // e' preciso meter sequer? como meter na pre-cond? -> tem de se alterar a inv e meter no valid nextB
		//	return false;
		
		boolean valid = isNextSummary();
		
		// assert b.BlockInv(h, hp, ?hx, nonce);
		
		// open BlockchainInv(h, s, c);
		// assert this.head |-> ?he;
		// assert he.BlockInv(_, _, hp, _);
		
		if(valid) {
			SummaryBlock b = new SummaryBlock(this.head, nonce, balances);
			this.head = b;
			this.size++;
			//@ this.ch = conc(c, b);
			
			//@ close BlockchainInv(b, _, s+1, conc(c, b));
			
			log(this.size, "Summary");
		} else {
			// open b.BlockInv(h, hp, hx, nonce);
			// close BlockchainInv(h, s, c);
		}
		
		return valid;
	}

	public int[] getBalances()
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c);
	//@ ensures BlockchainInv(h, hx, s, c) &*& ValidSummary(result, _); 
	{
		int[] balances = new int[Block.MAX_ID];
		for(int i = 0; i < Block.MAX_ID; i++) 
		/*@ invariant 0 <= i &*& i <= Block.MAX_ID 
				&*& array_slice_deep(balances, 0, i, Positive, unit, ?elems, ?vls)
				&*& array_slice(balances,i,balances.length,_) 
				&*& BlockchainInv(h, hx, s, c);
		@*/
		{
			//@ open BlockchainInv(h, hx, s, c);
			balances[i] = this.head.balanceOf(i);
			//@ assert balances[i] >= 0;
			//@ close BlockchainInv(h, hx, s, c);
		}
		//@ assert BlockchainInv(h, hx, s, c);
		
		// assert array_slice(balances,0,balances.length,_);
		//@ array_slice_deep(balances, 0, balances.length, Positive, unit, ?elems, ?vls);
		
		//@ close ValidSummary(balances,vls);
		return balances;
	}
	
	public boolean appendBlock(Transaction[] ts) 
	/*@ requires BlockchainInv(?h, ?hp, ?s, ?c) 
				&*& ValidSimple(ts, ?vls)
				&*& [_]System.out |-> ?o &*& o != null; @*/
	//@ ensures o != null &*& result ? BlockchainInv(?b, _, s+1, conc(c, b)) : BlockchainInv(h, hp, s, c);
	{
	
		int hp = this.headHash();
		
		int nonce = SimpleBlock.mine(hp, ts);
		
		boolean status = this.appendSimple(hp, nonce, ts); // fazer o que com isto?
		
		if(this.isNextSummary()) {
			int[] balances = this.getBalances();
			hp = this.headHash();
			
			nonce = SummaryBlock.mine(hp, balances);
			
			status = this.appendSummary(hp, nonce, balances); // fazer o que com isto?
        	}
        	
        	return true; // retornar o que?
	}
	
	public int balanceOf(int id)
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c) &*& ValidID(id) == true;
	//@ ensures BlockchainInv(h, hx, s, c) &*& result >= 0;
	{
		return this.head.balanceOf(id);
	}
	
}
