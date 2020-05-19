


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

@*/

/*@
    predicate isBlockchain(BlockChain bc;) = bc == null ? emp : bc.BlockchainInv(?h, ?s, ?c);
    
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
	predicate BlockchainInv(Block h, int s, chain c) =
				    this.head |-> h
				&*& this.size |-> s
				&*& this.ch |-> c
				&*& s > 0
				&*& len(c) == s
				&*& h != null
				&*& c != nill
				&*& c == conc(_, h)
				&*& h.BlockInv(_, _, ?hx, _)
				//&*& hx % 100 == 0
				;
	@*/

	private Block head;
	private int size;

	//@ private chain ch; // ghost var

	private static void log(int size, String b) 
	//@ requires b != null;
	//@ ensures true;
	{
		/*
		System.out.print("["+Util.time()+"] " + (size<10 ? "  " : size<100 ? " " : ""));
		System.out.print(size);
		System.out.println(" : " + b);
		*/
	}

	public BlockChain(int nonce, int[] initial_balances)
	//@ requires ValidCheckpoint(initial_balances) &*& array_slice(initial_balances,0,initial_balances.length, ?items) &*& validNonce(nonce, 0, sum(items));
	//@ ensures BlockchainInv(_, 1, _);
	{
		SummaryBlock b = new SummaryBlock(null, nonce, initial_balances);
		
		//@ open validNonce(nonce, 0, sum(items));
		//@ open b.BlockInv(null, 0, ?hx, nonce);
		//@ assert hx % 100 == 0;
		
		this.head = b;
		this.size = 1;
		//@ this.ch = conc(nill, this.head);
		
		log(this.size, "Summary");

		//@ close BlockchainInv(this.head, 1, conc(nill, this.head));
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
	//@ requires BlockchainInv(?h, ?s, ?c);
	//@ ensures BlockchainInv(h, s, c) &*& result ? (s % (BlockChain.SUMMARY_INTERVAL + 1) == 0) : true;
	{
		return this.size % (BlockChain.SUMMARY_INTERVAL + 1) == 0;
	}
	
	public int headHash() 
	//@ requires BlockchainInv(?h, ?s, ?c);
	//@ ensures BlockchainInv(h, s, c);
	{
		return this.head.hash();
	}

	public boolean appendBlock(int hp, int nonce, Transaction[] ts) 
	/*@ requires BlockchainInv(?h, ?s, ?c) &*& ts.length == Block.MAX_TX 
				&*& array_slice_deep(ts,0,ts.length,TransHash,unit, ?els, ?vls) 
				&*& validNonce(nonce, hp, sum(vls)) 
				&*& s % (BlockChain.SUMMARY_INTERVAL + 1) != 0; @*/
	//@ ensures result ? BlockchainInv(?b, s+1, conc(c, b)) : BlockchainInv(h, s, c);
	{ 
		if(this.head.hash() != hp) // e' preciso meter sequer? como meter na pre-cond? -> tem de se alterar a inv e meter no valid nextB
			return false;
		
		SimpleBlock b = new SimpleBlock(this.head, nonce, ts);
		
		//@ assert b.BlockInv(h, hp, ?hx, nonce);
		
		int i = 0;
		boolean valid = true;
		while( i < Block.MAX_ID && valid ) // Esta validacao deveria vir de fora?
		//@ invariant i >= 0 &*& i <= Block.MAX_ID &*& b.BlockInv(h, hp, hx, nonce);
		{
			valid = valid && b.balanceOf(i) > 0;
			i++;
		}
		
		// Se nao for valido, como recuperar a BlockInv da cabeca?

		if(valid) {
			this.head = b;
			this.size++;
			//@ this.ch = conc(c, b);
			
			//@ close BlockchainInv(b, s+1, conc(c, b));
			
			log(this.size, "Simple");
		} else {
			//@ open b.BlockInv(h, hp, hx, nonce);
			//@ close BlockchainInv(h, s, c);
		}

		return valid;
	}
	
	public boolean appendSummary(int hp, int nonce, int[] balances) 
	/*@ requires BlockchainInv(?h, ?s, ?c) &*& ValidCheckpoint(balances) 
				&*& array_slice(balances,0,balances.length, ?items) 
				&*& validNonce(nonce, hp, sum(items)) 
				&*& s % (BlockChain.SUMMARY_INTERVAL + 1) == 0; @*/
	//@ ensures result ? BlockchainInv(?b, s+1, conc(c, b)) : BlockchainInv(h, s, c);
	{
		if(this.head.hash() != hp) // e' preciso meter sequer? como meter na pre-cond? -> tem de se alterar a inv e meter no valid nextB
			return false;
		
		boolean valid = isNextSummary();
		
		SummaryBlock b = new SummaryBlock(this.head, nonce, balances);
		
		//@ assert b.BlockInv(h, hp, ?hx, nonce);
		
		if(valid) {
			this.head = b;
			this.size++;
			//@ this.ch = conc(c, b);
			
			//@ close BlockchainInv(b, s+1, conc(c, b));
			
			log(this.size, "Summary");
		} else {
			//@ open b.BlockInv(h, hp, hx, nonce);
			//@ close BlockchainInv(h, s, c);
		}
		
		return valid;
	}

	/*public boolean appendBlock(Block b)
	//@ requires BlockchainInv(?h, ?s, ?c) &*& validNextBlock(b, h, s);
	//@ ensures result ? BlockchainInv(b, s+1, conc(c, b)) : BlockchainInv(h, s, c);
	{
		int i = 0;
		boolean valid = true;
		while( i < Block.MAX_ID && valid )
		//@ invariant BlockchainInv(h, s, c) &*& validNextBlock(b, h, s) &*& i >= 0 &*& i <= Block.MAX_ID;
		{
			//@ open validNextBlock(b, h, s);
			valid = valid && b.balanceOf(i) > 0;
			i++;
			//@ close validNextBlock(b, h, s);
		}
		//@ open validNextBlock(b, h, s);

		if(valid) {
			this.head = b;
			this.size++;
			//@ this.ch = conc(c, b);
		}

		return valid;
	}
	*/
	
	public int[] getBalances()
	//@ requires BlockchainInv(?h, ?s, ?c);
	//@ ensures BlockchainInv(h, s, c) &*& ValidCheckpoint(result);
	{
		int[] balances = new int[Block.MAX_ID];
		for(int i = 0; i < Block.MAX_ID; i++) 
		//@ invariant 0 <= i &*& i <= Block.MAX_ID &*& array_slice(balances,0,balances.length,_) &*& BlockchainInv(h, s, c);
		{
			//@ open BlockchainInv(h, s, c);
			balances[i] = this.head.balanceOf(i);
			//@ close BlockchainInv(h, s, c);
		}
		//@ assert BlockchainInv(h, s, c);
		
		//@ close ValidCheckpoint(balances);
		return balances;
	}
	
	public int balanceOf(int id)
	//@ requires BlockchainInv(?h, ?s, ?c) &*& ValidID(id) == true;
	//@ ensures BlockchainInv(h, s, c);
	{
		return this.head.balanceOf(id);
	}
	
}
