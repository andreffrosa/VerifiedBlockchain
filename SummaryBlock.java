/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

2020 João Costa Seco, Eduardo Geraldo

Note: please add your names and student numbers in all files you submit.
*/

/*
   The class of blockchain summary blocks.

   It contains the definition for the instance predicate that instantiate
   the predicate defined in the interface.

   This predicate defines the representation invariant for blockchain summary blocks.

*/


/*@
	predicate Positive(unit a, int v; int n) = v >= 0 &*& n == v;
	
	predicate ValidSummary(int[] b; list<int> vls) = b.length == Block.MAX_ID
				      &*& array_slice_deep(b, 0, b.length, Positive, unit, ?elems, vls);
@*/

final class SummaryBlock implements Block {
	/*@
	predicate BlockInv(Block p, int hp, int h, int r) =
			this.previous |-> p
		&*& this.hashPrevious |-> hp
		&*& this.random |-> r
		&*& this.balances |-> ?b
		&*& isBlock(p,hp)
		&*& ValidSummary(b, ?vls)
		//&*& array_slice_deep(b, 0, b.length, Positive, unit, ?elems, ?items)
		&*& h == hashOf3(sum(vls),hp, r)
		&*& h % 100 == 0;
	@*/

	private Block previous;
	private int hashPrevious;
	private int random;
	private int balances[];

	public SummaryBlock(Block previous, int r, int balances[])
	/*@ requires isBlock(previous, ?h)
		 &*& ValidSummary(balances, ?vls)
		 &*& ValidNonce(r, h, sum(vls));
	@*/
	//@ ensures BlockInv(previous, h, _, r) &*& ValidNonce(r, h, sum(vls));
	{
		//@ open ValidNonce(r, h, sum(vls));
		//@ open isBlock(previous, h);
		this.previous = previous;
		this.hashPrevious = previous == null ? 0 : previous.hash();
		this.random = r;
		this.balances = balances;
		//@ close ValidNonce(r, h, sum(vls));
	}

	public int balanceOf(int id)
	//@ requires BlockInv(?p, ?hp, ?h, ?r) &*& ValidID(id) == true;
	//@ ensures BlockInv(p, hp, h, r) &*& result >= 0;
	{
		/*if(id >= balances.length || id < 0)
			return -1;
		else {*/
			//@ open BlockInv(p, hp, h, r);
			//@ assert this.balances |-> ?b;
			//@ open ValidSummary(b, ?vls);
			//@ assert id < balances.length;
			//@ assert array_slice_deep(b, 0, b.length, Positive, unit, ?elems, vls);
			int bal = balances[id];
			//@ assert array_slice_deep(b, 0, b.length, Positive, unit, elems, vls);
			
			// assert array_slice (b, 0, b.length, ?elems); 
			// bal == nth(id, elems);
			// assert array_slice_deep(b, 0, b.length, Positive, unit, elems, vls);
			//@ bal == nth(id, elems);
			//@ assert bal >= 0;
			//@ close ValidSummary(b, vls);
			//@ close BlockInv(p, hp, h, r);
			return bal;
		//}
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
		int balHash = 0;
		int i = 0;

		//@ open BlockInv(p, hp, h, r);
		//@ assert this.balances |-> ?b;
		//@ assert array_slice(b, 0, b.length, ?items);
		//@ assert this.random |-> r;
		while(i < balances.length)
		/*@ invariant
				this.balances |-> b
			&*& this.previous |-> p
			&*& this.hashPrevious |-> hp
			&*& this.random |-> r
			&*& 0 <= i &*& i <= b.length
			&*& isBlock(p,hp)
			&*& array_slice(b, 0, b.length, items)
			&*& balHash == sum(take(i,items));
		@*/
		{
			int tmp = balances[i];
			balHash = balHash + tmp;
			//@ length_drop(i, items);
			//@ take_one_more(i, items);
			i++;
		}
		return ((balHash ^ this.hashPrevious) ^ this.random);
	}

	public int getRandom()
    	//@ requires BlockInv(?p, ?hp, ?h, ?r);
    	//@ ensures BlockInv(p, hp, h, r) &*& result == r;
	{
		return this.random;
	}

	public static int hash(int hp, int r, int[] balances) 
	//@ requires balances.length == Block.MAX_ID &*& array_slice(balances, 0, balances.length, ?items);
	//@ ensures array_slice(balances, 0, balances.length, items) &*& result == hashOf3(sum(items),hp, r);
	{
		int balHash = 0;
		int i = 0;

		// assert array_slice(balances, 0, balances.length, ?items);
		while(i < balances.length)
		/*@ invariant 0 <= i &*& i <= balances.length
			&*& array_slice(balances, 0, balances.length, items)
			&*& balHash == sum(take(i,items));
		@*/
		{
			int tmp = balances[i];
			balHash = balHash + tmp;
			//@ length_drop(i, items);
			//@ take_one_more(i, items);
			i++;
		}
		return ((balHash ^ hp) ^ r);
	}
	
	public static int mine(int hp, int[] balances) 
	//@ requires balances.length == Block.MAX_ID &*& array_slice(balances, 0, balances.length, ?items);
	//@ ensures array_slice(balances, 0, balances.length, items) &*& ValidNonce(result, hp, sum(items));
	{
		int r = 0;
		while( hash(hp, r, balances) % 100 != 0 ) 
		//@ invariant balances.length == Block.MAX_ID &*& array_slice(balances, 0, balances.length, items);
		{
			r++;
		}
		//@ assert hashOf3(sum(items), hp, r) % 100 == 0;
		//@ close validNonce(r, hp, sum(items));
		return r;
	}

	/*public void mine()
    	//@ requires BlockInv(?p, ?hp, ?h, ?r); // &*& cond != null;
    	//@ ensures BlockInv(p, hp, ?h2, ?r2) &*& (h2 % 100 == 0);
	{
		while( this.hash() % 100 != 0 ) 
		//@ invariant BlockInv(p, hp, _, _);
		{
			this.random++;
		}
	}*/

}
