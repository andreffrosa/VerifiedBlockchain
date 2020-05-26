import java.util.concurrent.*;
import java.util.concurrent.locks.*;

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
    
    predicate ValidTransactions(Transaction[] ts, int head_hash) = true; // Just a token
    
@*/

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

	protected boolean isNextSummary()
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c);
	//@ ensures BlockchainInv(h, hx, s, c) &*& result ? (s % (BlockChain.SUMMARY_INTERVAL + 1) == 0) : (s % (BlockChain.SUMMARY_INTERVAL + 1) != 0);
	{
		return this.size % (BlockChain.SUMMARY_INTERVAL + 1) == 0;
	}
	
	protected int headHash() 
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c);
	//@ ensures BlockchainInv(h, hx, s, c) &*& result == hx;
	{
		return this.head.hash();
	}
	
	protected boolean validTransactions(Transaction[] ts) 
	/*@ requires BlockchainInv(?h, ?hp, ?s, ?c) &*& ValidSimple(ts, ?tx, ?hx);
	@*/
	//@ ensures BlockchainInv(h, hp, s, c) &*& ValidSimple(ts, tx, hx) &*& result ? ValidTransactions(ts, hp) : true;
	{
		int[] balances = this.getBalances();
		
		//@ open ValidSimple(ts, tx, hx);
		//@ assert array_slice_deep(ts, 0, ts.length, TransHash, unit, ?transactions, ?hashes);
		for(int i = 0; i < ts.length; i++) 
		/*@ invariant 0 <= i &*& i <= ts.length
					&*& ValidSummary(balances) 
					&*& array_slice(balances,0,balances.length, ?items)
					&*& ts != null 
					&*& ts.length == Block.MAX_TX
				        &*& array_slice_deep(ts, 0, ts.length, TransHash, unit, transactions, hashes);
		@*/
		{
			// array_slice_deep_split(ts, 0, i);
			// array_slice_deep_split(ts, i, i+1);
			// array_slice_deep_open(ts, i);
			Transaction t = ts[i];
			if( t != null ) {
				//@ assert array_element(ts, i, ?t_elem);
				// open TransHash(?x, t, ?hash);
				// open TransInv(ts[i], ?t_s, ?t_r, ?t_a);
				//@ open TransInv(t, ?t_s, ?t_r, ?t_a);
			
				int amount = t.getAmount();
				int sender = t.getSender();
				int receiver = t.getReceiver();
			
			
				//@ open ValidSummary(balances);
				//@ assert ValidID(sender) == true;
				//@ assert ValidID(receiver) == true;
			
				//balances[sender] -= amount;
				//balances[receiver] += amount;
			
				//@ assert array_slice(balances, 0, balances.length, items);
				//@ array_slice_split(balances, 0, sender);
				//@ array_slice_split(balances, sender, sender+1);
				//@ assert array_slice(balances, 0, sender, ?litems);
				//@ assert array_slice(balances, sender, sender+1, _);
				//@ assert array_slice(balances, sender+1, balances.length, ?ritems);
				//balances[sender] -= amount;
				int asd = balances[sender] - amount;
				balances[sender] = asd;
				//@ assert array_element(balances, sender, ?v);
				//@ assert array_slice(balances, 0, sender, litems);
				//@ assert array_slice(balances, sender, sender+1, cons(v, nil));
				//@ assert array_slice(balances, sender+1, balances.length, ritems);
			
				//@ array_slice_join(balances, 0);
				//@ array_slice_join(balances, 0);
				//@ append_assoc(litems, cons(v, nil), ritems);
				//@ assert array_slice(balances, 0, balances.length, append(append(litems, cons(v, nil)), ritems)); 
			
				//@ array_slice_split(balances, 0, receiver);
				//@ array_slice_split(balances, receiver, receiver+1);
				//@ assert array_slice(balances, 0, receiver, ?litems2);
				//@ assert array_slice(balances, receiver, receiver+1, _);
				//@ assert array_slice(balances, receiver+1, balances.length, ?ritems2);
				asd = balances[receiver] + amount;
				balances[receiver] = asd;
				//@ assert array_element(balances, receiver, ?v2);
				//@ assert array_slice(balances, 0, receiver, litems2);
				//@ assert array_slice(balances, receiver, receiver+1, cons(v2, nil));
				//@ assert array_slice(balances, receiver+1, balances.length, ritems2);
			
				//@ array_slice_join(balances, 0);
				//@ array_slice_join(balances, 0);
				//@ append_assoc(litems2, cons(v, nil), ritems2);
				//@ assert array_slice(balances, 0, balances.length, append(append(litems2, cons(v2, nil)), ritems2)); 
			
				//@ close ValidSummary(balances);
				
				//@ close TransInv(t, t_s, t_r, t_a);
				//@ close TransHash(unit, t, tansactionHash(t_s,t_r,t_a));
			}
					
				
				int tmp = (t==null) ? 0 : t.hash(); // aux to proof
				//@ length_drop(i, hashes);
				//@ take_one_more(i, hashes);
				//@ assert array_slice_deep(ts,0,i,TransHash,unit,?lels,?lvls);
				//@ assert array_slice_deep(ts,i+1,ts.length,TransHash,unit,?rels,?rvls);
				//@ append_assoc(lels, cons(ts[i], nil), rels);
				//@ append_assoc(lvls, cons(tmp, nil), rvls);
				//@ array_slice_deep_close(ts, i, TransHash, unit);
				//@ array_slice_deep_join(ts, 0);
				//@ array_slice_deep_join(ts, 0);
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
		//@ close ValidTransactions(ts, hp);
		return true;
	}

	protected boolean appendSimple(int hp, int nonce, Transaction[] ts) 
	/*@ requires BlockchainInv(?h, hp, ?s, ?c) &*& ts.length == Block.MAX_TX 
				&*& array_slice_deep(ts,0,ts.length,TransHash,unit, ?els, ?vls) 
				&*& ValidNonce(nonce, hp, sum(vls)) 
				&*& ValidTransactions(ts, hp)
				&*& s % (BlockChain.SUMMARY_INTERVAL + 1) != 0 //
				&*& [_]System.out |-> ?o &*& o != null; @*/
	//@ ensures o != null &*& result ? BlockchainInv(?b, _, s+1, conc(c, b)) : (BlockchainInv(h, hp, s, c) &*& array_slice_deep(ts,0,ts.length,TransHash,unit, els, vls) );
	{ 
		if(this.head.hash() != hp)
			return false;
		
		//@ assert ValidTransactions(ts, hp);
		SimpleBlock b = new SimpleBlock(this.head, nonce, ts);
		//@ assert b.BlockInv(h, hp, ?hx1, nonce);
		this.head = b;
		this.size++;
		//@ this.ch = conc(c, b);
			
		//@ close BlockchainInv(b, _, s+1, conc(c, b));
			
		log(this.size, "Simple");
	
		return true;
	}
	
	protected void appendSummary() 
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
				&*& ValidSimple(ts, ?elms, ?vls)
				//&*& s % (BlockChain.SUMMARY_INTERVAL + 1) != 0
				&*& [_]System.out |-> ?o &*& o != null; @*/
	/*@ ensures o != null 
				&*& result ? 
					( (s+1) % (BlockChain.SUMMARY_INTERVAL + 1) == 0 ? 
						BlockchainInv(?b2, _, s+2, conc(conc(c, _), b2)) 
					      : BlockchainInv(?b, _, s+1, conc(c, b)) )
					: (BlockchainInv(h, hp, s, c) &*& ValidSimple(ts, elms, vls));
	@*/
	{
		if(this.isNextSummary()) { // Will never be true
			return false; 
		}
		
		//@ open ValidSimple(ts, elms, vls);
		
		boolean valid = this.validTransactions(ts);
		
		if(valid) {
			int hash_previous = this.headHash();
			//@ assert ValidTransactions(ts, hp);
			int nonce = SimpleBlock.mine(hash_previous, ts);
		
			boolean status = this.appendSimple(hash_previous, nonce, ts);
		
			if(status) {
				if(this.isNextSummary()) {
					//@ assert (s+1) % (BlockChain.SUMMARY_INTERVAL + 1) == 0;
					this.appendSummary();
					//@ assert this.head |-> ?b;
					//@ close BlockchainInv(b, _, s+2, conc(conc(c, _), b));
				} else {
					//@ assert (s+1) % (BlockChain.SUMMARY_INTERVAL + 1) != 0;
					//@ assert this.head |-> ?b;
					//@ close BlockchainInv(b, _, s+1, conc(c, b));
				}
				
				return true;
			}
		} 
		//@ close ValidSimple(ts, elms, vls);
		return false;
	}
	
	public int balanceOf(int id)
	//@ requires BlockchainInv(?h, ?hx, ?s, ?c) &*& ValidID(id) == true;
	//@ ensures BlockchainInv(h, hx, s, c);
	{
		return this.head.balanceOf(id);
	}
	
}









/*@

predicate_ctor CBlockchain_shared_state(CBlockChain cb)() = cb.b_chain |-> ?bc &*& bc != null &*& bc.BlockchainInv(?h, ?hx, ?s, ?c);

predicate_ctor CBlockchain_wait_summary(CBlockChain cb)() = cb.b_chain |-> ?bc &*& bc != null &*& bc.BlockchainInv(?h, ?hx, ?s, ?c) &*& (s % (BlockChain.SUMMARY_INTERVAL + 1) != 0);

@*/

class CBlockChain {
	
	/*@

	predicate CBlockchainInv() =
		this.mon |-> ?l
	    &*& this.wait_summary |-> ?cs
		
	    &*& l != null
	    &*& cs != null

	    &*& lck(l, 1, CBlockchain_shared_state(this))
	    &*& cond(cs, CBlockchain_shared_state(this), CBlockchain_wait_summary(this));
	    
	@*/
	
	private BlockChain b_chain;
	private ReentrantLock mon;
	private Condition wait_summary;

	public CBlockChain(int[] initial_balances)
	/*@ requires ValidSummary(initial_balances) &*& array_slice_deep(initial_balances,0,initial_balances.length,Positive,unit, ?els, ?vls) 
		&*& [_]System.out |-> ?o &*& o != null;
	@*/
	//@ ensures CBlockchainInv() &*& o != null;
	{
		b_chain = new BlockChain(initial_balances);
		//@ close CBlockchain_shared_state(this)();
		//@ close enter_lck(1, CBlockchain_shared_state(this));
		mon = new ReentrantLock();
		//@ close set_cond(CBlockchain_shared_state(this), CBlockchain_wait_summary(this));
		wait_summary = mon.newCondition();
		//@ close CBlockchainInv();
	}

	public int getSize()
	//@ requires CBlockchainInv();
	//@ ensures CBlockchainInv() &*& result > 0; // &*& result == s &*& result == len(c); ---> o que acontece a isto?
	{
		int size = 0;
		mon.lock();
    		//@ open CBlockchain_shared_state(this)();
		size = b_chain.getSize();
		//@ open b_chain.BlockchainInv(_, _, _, _);
		//@ assert size > 0;
		//@ close CBlockchain_shared_state(this)();
		mon.unlock();
		
		return size;
	}

	public int[] getBalances()
	//@ requires CBlockchainInv();
	//@ ensures CBlockchainInv() &*& ValidSummary(result) &*& array_slice(result,0,result.length,_); 
	{
		int[] balances = null;
		mon.lock();
    		//@ open CBlockchain_shared_state(this)();
    		balances = b_chain.getBalances();
    		//@ assert ValidSummary(balances);
    		//@ assert array_slice(balances,0,balances.length,_);
    		//@ close CBlockchain_shared_state(this)();
		mon.unlock();
		
		return balances;
	}
	
	public int balanceOf(int id)
	//@ requires CBlockchainInv() &*& ValidID(id) == true;
	//@ ensures CBlockchainInv();
	{
		int balance = 0;
		mon.lock();
    		//@ open CBlockchain_shared_state(this)();
    		balance = b_chain.balanceOf(id);
    		//@ close CBlockchain_shared_state(this)();
		mon.unlock();
		
		return balance;
	}
	
	public boolean appendBlock(Transaction[] ts) 
	/*@ requires CBlockchainInv() &*& ValidSimple(ts, ?elms, ?vls)
				&*& [_]System.out |-> ?o &*& o != null;
	@*/
	/*@ ensures CBlockchainInv() &*& o != null &*& result ? true : ValidSimple(ts, elms, vls);
	@*/
	{
		boolean valid = false;
		int hash_previous = -1;
		
		mon.lock();
	    	//@ open CBlockchain_shared_state(this)();
	    	while( b_chain.isNextSummary() ) 
	    	/*@ invariant b_chain |-> ?bc &*& bc != null &*& bc.BlockchainInv(?h, ?hx, ?s, ?c)
	    			&*& this.wait_summary |-> ?cs
				&*& cs != null
				&*& cond(cs, CBlockchain_shared_state(this), CBlockchain_wait_summary(this));
	    	@*/
	    	{
	    		//@ close CBlockchain_shared_state(this)();
		      	wait_summary.await();
		      	//@ open CBlockchain_wait_summary(this)();
		}
		
		valid = b_chain.validTransactions(ts);
		
		if(valid) {
			hash_previous = b_chain.headHash();
			//@ close CBlockchain_shared_state(this)();
			mon.unlock();
			
			//@ open ValidSimple(ts, elms, vls);
			int nonce = SimpleBlock.mine(hash_previous, ts);
			
			boolean status = false;
			mon.lock();
	    		//@ open CBlockchain_shared_state(this)();
	    		if(b_chain.headHash() == hash_previous && !b_chain.isNextSummary()) {
	    			//@ assert ValidTransactions(ts, hash_previous);
				status = b_chain.appendSimple(hash_previous, nonce, ts);
			}
			// @ close CBlockchain_shared_state(this)();
			//mon.unlock();
	
			if(status) {
				boolean isNextSummary = false;
				//mon.lock();
		    		// @ open CBlockchain_shared_state(this)();
		    		isNextSummary = b_chain.isNextSummary();
		    		
				if(isNextSummary) {
					//@ close CBlockchain_wait_summary(this)();
					wait_summary.signal();
				
					// @ assert (s+1) % (BlockChain.SUMMARY_INTERVAL + 1) == 0;
					b_chain.appendSummary();
					// @ assert this.head |-> ?b;
					// @ close BlockchainInv(b, _, s+2, conc(conc(c, _), b));
				} else {
					// @ assert (s+1) % (BlockChain.SUMMARY_INTERVAL + 1) != 0;
					// @ assert this.head |-> ?b;
					// @ close BlockchainInv(b, _, s+1, conc(c, b));
				}
				
				//@ close CBlockchain_shared_state(this)();
				mon.unlock();
				
				return true;
			} else {
				//@ close CBlockchain_shared_state(this)();
				mon.unlock();
				
				//@ close ValidSimple(ts, elms, vls);
			}
		} else {
			//@ close CBlockchain_shared_state(this)();
			mon.unlock();
			
			// @ assert ts != null;
			// @ assert true;
		}
		
		// @ assert ts != null;
		// @ close ValidSimple(ts, elms, vls);
		//@ assert true;
		return false;
	}
	
}

