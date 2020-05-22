


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


    predicate isBlockchain(BlockChain bc;) = bc != null &*& bc.BlockchainInv(?h, ?hx, ?s, ?c);
    
    predicate ValidTransactions(Transaction[] ts) = true;
    
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
		String txt = "["+Util.time()+"] "
			   + "Block "
		           + (size < 10 ? "  " : size < 100 ? " " : "")
		           + String.valueOf(size)
		           + " : " + b;
		           
		System.out.println(txt);
	}

	public BlockChain(int[] initial_balances)
	/*@ requires ValidSummary(initial_balances) &*& array_slice_deep(initial_balances,0,initial_balances.length,Positive,unit, ?els, ?vls) 
		&*& [_]System.out |-> ?o &*& o != null;
	@*/
	//@ ensures BlockchainInv(_, _, 1, _) &*& o != null;
	{
		//@ array_slice_convert(initial_balances,0,initial_balances.length);
		//@ open ValidSummary(initial_balances);
		
		int nonce = SummaryBlock.mine(0, initial_balances);
		
		SummaryBlock b = new SummaryBlock(null, nonce, initial_balances);
		
		//@ open ValidNonce(nonce, 0, sum(els));
		//@ open b.BlockInv(null, 0, ?hx, nonce);
		//@ assert hx % 100 == 0;
		
		this.head = b;
		this.size = 1;
		//@ this.ch = conc(nill, this.head);
		
		log(this.size, "Summary");

		//@ close BlockchainInv(this.head, hx, 1, conc(nill, this.head));
	}

	public int getSize()
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c);
	//@ ensures BlockchainInv(h, hx, s, c) &*& result == s &*& result == len(c);
	{
		return this.size;
	}


	public boolean isNextSummary()
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c);
	//@ ensures BlockchainInv(h, hx, s, c) &*& result ? (s % (BlockChain.SUMMARY_INTERVAL + 1) == 0) : (s % (BlockChain.SUMMARY_INTERVAL + 1) != 0);
	{
		return this.size % (BlockChain.SUMMARY_INTERVAL + 1) == 0;
	}
	
	private int headHash() 
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c);
	//@ ensures BlockchainInv(h, hx, s, c) &*& result == hx;
	{
		return this.head.hash();
	}
	
	private static void aux(int[] a, int i, int v) 
	/*@ requires 0 <= i &*& i < a.length
			&*& array_slice(a, i, i+1, ?items);
	@*/
	//@ ensures array_slice(a, i, i+1, cons(v, nil));
	{
		a[i] = v;
	}
	
	private boolean validTransactions(Transaction[] ts) 
	/*@ requires BlockchainInv(?h, ?hp, ?s, ?c) &*& ValidSimple(ts, _);
	@*/
	//@ ensures BlockchainInv(h, hp, s, c) &*& ValidSimple(ts, _) &*& result ? ValidTransactions(ts) : true;
	{
		int[] balances = this.getBalances();
		
		//@ open ValidSimple(ts, _);
		for(int i = 0; i < ts.length; i++) 
		/*@ invariant 0 <= i &*& i <= ts.length
					&*& ValidSummary(balances) 
					&*& array_slice(balances,0,balances.length,_)
					&*& ts != null 
					&*& ts.length == Block.MAX_TX
				        &*& array_slice_deep(ts, 0, ts.length, TransHash, unit, ?transactions, ?hashes);
		@*/
		{
			//@ array_slice_deep_split(ts, 0, i);
			//@ array_slice_deep_split(ts, i, i+1);
			//@ array_slice_deep_open(ts, i);
			
			//@ open TransHash(?x, ts[i], ?hash);
			//@ open TransInv(ts[i], ?t_s, ?t_r, ?t_a);
			
			int amount = ts[i].getAmount();
			int sender = ts[i].getSender();
			int receiver = ts[i].getReceiver();
			
			//@ open ValidSummary(balances);
			
			//@ assert ValidID(sender) == true;
			//@ assert ValidID(receiver) == true;
			
			//@ assert sender < balances.length &*& sender >= 0;
			//@ assert receiver < balances.length &*& receiver >= 0;
			
			//balances[sender] -= amount;
			//balances[receiver] += amount;
			
			//@ assert array_slice(balances, 0, balances.length, ?items);
			//@ array_slice_split(balances, 0, sender);
			//@ array_slice_split(balances, sender, sender+1);
			//@ assert array_slice(balances, 0, sender, ?litems);
			//@ assert array_slice(balances, sender, sender+1, _);
			//@ assert array_slice(balances, sender+1, balances.length, ?ritems);
			balances[sender] -= amount;
			//@ assert array_element(balances, sender, ?v);
			// int v = balances[sender]; 
			//@ assert array_slice(balances, 0, sender, litems);
			//@ assert array_slice(balances, sender, sender+1, cons(v, nil)); // como e' que e' verdade ????
			//@ assert array_slice(balances, sender+1, balances.length, ritems);
			
			//@ append_assoc(litems, cons(v, nil), ritems);
			
			//@ array_slice_join(balances, 0);
			//@ array_slice_join(balances, 0);
			//@ assert array_slice(balances, 0, balances.length, litems);
			//@ assert true;
			
			aux(balances, receiver, balances[receiver] - amount);
			
			//@ close ValidSummary(balances);
			
			//@ close TransInv(ts[i], t_s, t_r, t_a);
			//@ close TransHash(x, ts[i], hash);
			
			int tmp = t.hash();
			//@ length_drop(i, hashes);
			//@ take_one_more(i, hashes);
			//@ assert array_slice_deep(ts,0,i,TransHash,unit,?lels,?lvls);
			//@ assert array_slice_deep(ts,i+1,ts.length,TransHash,unit,?rels,?rvls);
			//@ append_assoc(lels, cons(ts[i], nil), rels);
			//@ append_assoc(lvls, cons(tmp, nil), rvls);
			//@ array_slice_deep_close(ts, i, TransHash, unit);
			//@ array_slice_deep_join(ts, 0);
			//@ array_slice_deep_join(ts, 0);
			

			
			// array_slice_deep_close(ts, i);
			//@ close ValidSummary(balances);
		}
		
		for(int i = 0; i < balances.length; i++) 
		/*@ invariant 0 <= i &*& i <= balances.length
					&*& ValidSummary(balances) 
					&*& array_slice(balances,0,balances.length,_);
		@*/
		{
			if( balances[i] < 0 ) {
				return false;
			}
		}
		//@ close ValidTransactions(ts);
		return true;
	}

	private boolean appendSimple(int hp, int nonce, Transaction[] ts) 
	/*@ requires BlockchainInv(?h, hp, ?s, ?c) &*& ts.length == Block.MAX_TX 
				&*& array_slice_deep(ts,0,ts.length,TransHash,unit, ?els, ?vls) 
				&*& ValidNonce(nonce, hp, sum(vls)) 
				//&*& s % (BlockChain.SUMMARY_INTERVAL + 1) != 0
				&*& [_]System.out |-> ?o &*& o != null; @*/
	//@ ensures o != null &*& result ? BlockchainInv(?b, _, s+1, conc(c, b)) : (BlockchainInv(h, hp, s, c) &*& array_slice_deep(ts,0,ts.length,TransHash,unit, els, vls) );
	{ 
		if(this.head.hash() != hp)
			return false;
		
		//@ assert array_slice_deep(ts,0,ts.length,TransHash,unit, els, vls);
		
		SimpleBlock b = new SimpleBlock(this.head, nonce, ts);
		//@ assert b.BlockInv(h, hp, ?hx1, nonce);
		
		int i = 0;
		boolean valid = true;
		while( i < Block.MAX_ID && valid )
		//@ invariant i >= 0 &*& i <= Block.MAX_ID &*& b.BlockInv(h, hp, hx1, nonce);
		{
			valid = valid && b.balanceOf(i) >= 0;
			i++;
		}

		if(valid) {
			this.head = b;
			this.size++;
			//@ this.ch = conc(c, b);
			
			//@ close BlockchainInv(b, _, s+1, conc(c, b));
			
			log(this.size, "Simple");
		} else {
			//@ open b.BlockInv(h, hp, hx1, nonce);
			//@ close BlockchainInv(h, hp, s, c);
			
			//@ assert b.transactions == ts;
			//@ assert array_slice_deep(ts,0,ts.length,TransHash,unit, els, vls);
		}

		return valid;
	}
	
	private void appendSummary() 
	/*@ requires BlockchainInv(?h, ?hp, ?s, ?c) 
				&*& s % (BlockChain.SUMMARY_INTERVAL + 1) == 0
				&*& [_]System.out |-> ?o &*& o != null; @*/
	//@ ensures o != null &*& BlockchainInv(?b, _, s+1, conc(c, b));
	{
		int[] balances = this.getBalances();
		//@ open ValidSummary(balances);
			
		int hash_previous = this.headHash();
			
		int nonce = SummaryBlock.mine(hash_previous, balances);
			
		SummaryBlock b = new SummaryBlock(this.head, nonce, balances);
		this.head = b;
		this.size++;
		//@ this.ch = conc(c, b);
			
		//@ close BlockchainInv(b, _, s+1, conc(c, b));
		
		log(this.size, "Summary");
	}

	public int[] getBalances()
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c);
	//@ ensures BlockchainInv(h, hx, s, c) &*& ValidSummary(result) &*& array_slice(result,0,result.length,_); 
	{
		int[] balances = new int[Block.MAX_ID];
		for(int i = 0; i < Block.MAX_ID; i++) 
		/*@ invariant 0 <= i &*& i <= Block.MAX_ID 
				//&*& array_slice_deep(balances, 0, i, Positive, unit, ?elems, ?vls)
				&*& array_slice(balances,0,balances.length,_) 
				&*& BlockchainInv(h, hx, s, c);
		@*/
		{
			//@ open BlockchainInv(h, hx, s, c);
			balances[i] = this.head.balanceOf(i);
		
			//@ close BlockchainInv(h, hx, s, c);
		}
		//@ assert BlockchainInv(h, hx, s, c);
		
		//@ assert array_slice(balances,0,balances.length,_);
		
		//@ close ValidSummary(balances);
		return balances;
	}
	
	public boolean appendBlock(Transaction[] ts) 
	/*@ requires BlockchainInv(?h, ?hp, ?s, ?c) 
				&*& ValidSimple(ts, ?vls)
				&*& [_]System.out |-> ?o &*& o != null; @*/
	/*@ ensures o != null &*& 
			result ? 
				( (s+1) % (BlockChain.SUMMARY_INTERVAL + 1) == 0 ? 
					BlockchainInv(?b2, _, s+2, conc(conc(c, _), b2)) 
				      : BlockchainInv(?b, _, s+1, conc(c, b)) )
				: (BlockchainInv(h, hp, s, c) &*& ValidSimple(ts, vls));
	@*/
	{
		//@ open ValidSimple(ts, vls);
		
		int hash_previous = this.headHash();
		
		int nonce = SimpleBlock.mine(hash_previous, ts);
		
		boolean status = this.appendSimple(hash_previous, nonce, ts);
		
		if(status) {
			if(this.isNextSummary()) {
				//@ assert (s+1) % (BlockChain.SUMMARY_INTERVAL + 1) == 0;
				this.appendSummary();
				//@ close BlockchainInv(?b2, _, s+2, conc(conc(c, _), b2));
			} else {
				//@ assert (s+1) % (BlockChain.SUMMARY_INTERVAL + 1) != 0;
				//@ assert this.head |-> ?b;
				//@ close BlockchainInv(b, _, s+1, conc(c, b));
			}
		} else {
			// open b
			return false;
		}
		
        	return true;
	}
	
	public int balanceOf(int id)
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c) &*& ValidID(id) == true;
	//@ ensures BlockchainInv(h, hx, s, c);
	{
		return this.head.balanceOf(id);
	}
	
}
