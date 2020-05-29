/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

2020 JoÃ£o Costa Seco, Eduardo Geraldo

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
	
	predicate ValidSummary(int[] b;) = b != null &*& b.length == Block.MAX_ID;
@*/

final class SummaryBlock implements Block {
	/*@
	predicate BlockInv(Block p, int hp, int h, int r) =
			this.previous |-> p
		&*& this.hashPrevious |-> hp
		&*& this.random |-> r
		&*& this.balances |-> ?a
		&*& [_]isBlock(p,hp)
		&*& array_slice(a,0,a.length,?items)
		&*& ValidSummary(a)
		&*& h == hashOf3(sum(items),hp, r)
		&*& h % 100 == 0;
	@*/

	private Block previous;
	private int hashPrevious;
	private int random;
	private int balances[];

	public SummaryBlock(Block previous, int r, int balances[])
	/*@ requires
		    [?f]isBlock(previous, ?h)
		&*& array_slice(balances,0,balances.length,?vls)
		&*& ValidSummary(balances)
		&*& ValidNonce(r, h, sum(vls));
	@*/
	//@ ensures [1]BlockInv(previous, h, _, r) &*& ValidNonce(r, h, sum(vls));
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
	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r) &*& ValidID(id) == true;
	//@ ensures [f]BlockInv(p, hp, h, r);
	{
		if(id >= balances.length || id < 0)
			return -1;
		else {
			int bal = balances[id];
			//@ assert [f]this.balances |-> ?b;
			//@ assert [f]array_slice (b, 0, b.length, ?elems);
			//@ bal == nth(id, elems);
			return bal;
		}
	}

	public Block getPrevious()
	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r);
	//@ ensures [f]BlockInv(p, hp, h, r) &*& result == p;
	{
		return previous;
	}

	public int getPreviousHash()
	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r);
	//@ ensures [f]BlockInv(p, hp, h, r) &*& result == hp;
	{
		return hashPrevious;
	}

	public int hash()
	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r);
	//@ ensures [f]BlockInv(p, hp, h, r) &*& result == h;
	{
		int balHash = 0;
		int i = 0;

		//@ open [f]BlockInv(p, hp, h, r);
		//@ assert [f]this.balances |-> ?b;
		//@ assert [f]array_slice(b, 0, b.length, ?items);
		//@ assert [f]this.random |-> r;
		while(i < balances.length)
		/*@ invariant
				[f]this.balances |-> b
			&*& [f]this.previous |-> p
			&*& [f]this.hashPrevious |-> hp
			&*& [f]this.random |-> r
			&*& 0 <= i &*& i <= b.length
			&*& [_]isBlock(p,hp)
			&*& [f]array_slice(b, 0, b.length, items)
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
    	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r);
    	//@ ensures [f]BlockInv(p, hp, h, r) &*& result == r;
	{
		return this.random;
	}

	public static int hash(int hp, int r, int[] balances) 
	//@ requires balances.length == Block.MAX_ID &*& array_slice(balances, 0, balances.length, ?items);
	//@ ensures array_slice(balances, 0, balances.length, items) &*& result == hashOf3(sum(items),hp, r);
	{
		int balHash = 0;
		int i = 0;

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
	
	public static int mine(int hp, int[] balances, int start) 
	//@ requires balances.length == Block.MAX_ID &*& array_slice(balances, 0, balances.length, ?items);
	//@ ensures array_slice(balances, 0, balances.length, items) &*& ValidNonce(result, hp, sum(items));
	{
		int r = start;
		while( hash(hp, r, balances) % 100 != 0 ) 
		//@ invariant balances.length == Block.MAX_ID &*& array_slice(balances, 0, balances.length, items);
		{
			r++;
		}
		//@ assert hashOf3(sum(items), hp, r) % 100 == 0;
		//@ close ValidNonce(r, hp, sum(items));
		return r;
	}

}
