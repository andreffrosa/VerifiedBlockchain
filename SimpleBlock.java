/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

2020 JoÃ£o Costa Seco, Eduardo Geraldo

Note: please add your names and student numbers in all files you submit.
*/


/*
   The class of blockchain simple blocks.

   It contains the definition for the instance predicate that instantiate
   the predicate defined in the interface.

   This predicate defines the representation invariant for blockchain simple blocks.

*/

/*@
	predicate ValidSimple(Transaction[] ts; list<int> hashes) = ts != null &*& ts.length == Block.MAX_TX
				      &*& array_slice_deep(ts, 0, ts.length, TransHash, unit, ?transactions, hashes);
@*/

final class SimpleBlock implements Block {

	/*@ predicate BlockInv(Block p, int hp, int h, int r) =
			this.previous |-> p
		&*& this.hashPrevious |-> hp
		&*& this.random |-> r
		&*& this.transactions |-> ?a
		&*& isBlock(p,hp)
		&*& array_slice_deep(a,0,a.length,TransHash,unit,?transactions,?hashes)
		&*& h == hashOf3(sum(hashes),hp,r)
		&*& h % 100 == 0;
	@*/

	static int hashTransactions(Transaction[] ts)
	//@requires array_slice_deep(ts, 0, ts.length, TransHash, unit, ?els, ?vls);
	//@ensures array_slice_deep(ts, 0, ts.length, TransHash, unit, els, vls) &*& result == sum(vls);
	{
		int hash = 0;
		int i = 0;
		while(i < ts.length)
		/*@ invariant
		        0 <= i &*& i <= ts.length
			&*& array_slice_deep(ts,0,ts.length,TransHash,unit,els,vls)
			&*& hash == sum(take(i,vls));
		@*/
		{
			Transaction one = ts[i];
			int tmp = one.hash();
			hash = hash + tmp;
			// Code necessary to deal with reestablishing
			// the array_slice_deep predicate.
			// This formulation is not optimal, will be improved.
			//@ length_drop(i, vls);
			//@ take_one_more(i, vls);
			//@ assert array_slice_deep(ts,0,i,TransHash,unit,?lels,?lvls);
			//@ assert array_slice_deep(ts,i+1,ts.length,TransHash,unit,?rels,?rvls);
			//@ append_assoc(lels, cons(one, nil), rels);
			//@ append_assoc(lvls, cons(tmp, nil), rvls);
			//@ array_slice_deep_close(ts, i, TransHash, unit);
			//@ array_slice_deep_join(ts, 0);
			//@ array_slice_deep_join(ts, 0);
			i++;
		}
		return hash;
	}

	private Block previous;
	private	int hashPrevious;
	private	int random;
	private	Transaction transactions[];

	public SimpleBlock(Block previous, int r, Transaction ts[])
	/*@ requires 
		    isBlock(previous, ?h) 
		&*& ValidSimple(ts, ?hashes)
		&*& ValidNonce(r, h, sum(hashes));
	@*/
	//@ ensures BlockInv(previous,h,_,r) &*& ValidNonce(r, h, sum(hashes));
	{
		//@ open ValidNonce(r, h, sum(hashes));
		//@ open isBlock(previous, h);
		this.previous = previous;
		this.hashPrevious = previous == null ? 0 : previous.hash();
		this.random = r;
		this.transactions = ts;
		//@ close isBlock(previous, h);
		//@ close ValidNonce(r, h, sum(hashes));
		
		//@ assert isBlock(previous, h);
	}

	public int balanceOf(int id)
	//@ requires BlockInv(?p, ?hp, ?h, ?r) &*& ValidID(id) == true;
	//@ ensures BlockInv(p, hp, h, r);
	{
		int delta = 0;
		int i = 0;
		//@ open BlockInv(p, hp, h, r);
		//@ assert this.transactions |-> ?ts;
		//@ assert array_slice_deep(ts, 0, ts.length, TransHash, unit, ?els, ?vls);
		while(i < transactions.length)
		/*@ invariant
				this.transactions |-> ts
			&*& array_slice_deep(ts, 0, ts.length, TransHash, unit, els, vls)
			&*& 0 <= i &*& i <= ts.length;
		@*/
		{
			Transaction t = transactions[i];
			int tmp = t.hash();
			if(t.getSender() == id) {
				delta -= t.getAmount();
			}//two ifs instead of if else allows to deal with transfers between the same ID (A -> A)
			if (t.getReceiver() == id) {
				delta += t.getAmount();
			}
			// Code necessary to deal with reestablishing
			// the array_slice_deep predicate.
			// This formulation is not optimal, will be improved.
			//@ length_drop(i, vls);
			//@ take_one_more(i, vls);
			//@ assert array_slice_deep(ts,0,i,TransHash,unit,?lels,?lvls);
			//@ assert array_slice_deep(ts,i+1,ts.length,TransHash,unit,?rels,?rvls);
			//@ append_assoc(lels, cons(t, nil), rels);
			//@ append_assoc(lvls, cons(tmp, nil), rvls);
			//@ array_slice_deep_close(ts, i, TransHash, unit);
			//@ array_slice_deep_join(ts, 0);
			//@ array_slice_deep_join(ts, 0);
			i = i + 1;
		}

			if(previous == null)
				return delta;
			else
				return previous.balanceOf(id) + delta;

	}

	public Block getPrevious()
	//@ requires BlockInv(?p, ?hp, ?h, ?r);
	//@ ensures BlockInv(p, hp, h, r) &*& result == p;
	{
		return previous;
	}

	public int getPreviousHash()
	//@ requires BlockInv(?p, ?hp, ?h, ?r);
	//@ ensures BlockInv(p, hp, h, r) &*& result == hp;
	{
		return hashPrevious;
	}

	public int hash()
	//@ requires BlockInv(?p, ?hp, ?h, ?r);
	//@ ensures BlockInv(p, hp, h, r) &*& result == h;
	{
		int txHash = hashTransactions(transactions);
		return ((txHash ^ this.hashPrevious) ^ this.random);
	}

	public int getRandom()
    	//@ requires BlockInv(?p, ?hp, ?h, ?r);
    	//@ ensures BlockInv(p, hp, h, r) &*& result == r;
	{
		return this.random;
	}

	public static int hash(int hp, int r, Transaction[] ts) 
	//@ requires ts.length == Block.MAX_TX &*& array_slice_deep(ts,0,ts.length,TransHash,unit, ?els, ?vls);
	//@ ensures array_slice_deep(ts,0,ts.length,TransHash,unit, els, vls) &*& result == hashOf3(sum(vls),hp, r);
	{
		int txHash = hashTransactions(ts);
		return ((txHash ^ hp) ^ r);
	}
	
	public static int mine(int hp, Transaction[] ts) 
	//@ requires ts.length == Block.MAX_TX &*& array_slice_deep(ts,0,ts.length,TransHash,unit, ?els, ?vls);
	//@ ensures array_slice_deep(ts,0,ts.length,TransHash,unit, els, vls) &*& ValidNonce(result, hp, sum(vls));
	{
		int r = 0;
		while( hash(hp, r, ts) % 100 != 0 ) 
		//@ invariant array_slice_deep(ts, 0, ts.length, TransHash, unit, els, vls);
		{
			r++;
		}
		//@ assert hashOf3(sum(vls), hp, r) % 100 == 0;
		//@ close ValidNonce(r, hp, sum(vls));
		return r;
	}

}

