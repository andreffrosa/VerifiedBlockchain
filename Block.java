/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

�2020 Jo�o Costa Seco, Eduardo Geraldo

Note: please add your names and student numbers in all files you submit.
*/


/* There are auxiliary functions and lemmas to assist in the verification of the code below. */
/*@
	fixpoint int sum(list<int> vs) {
		switch(vs) {
			case nil: return 0;
			case cons(h, t): return (h + sum(t));
		}
	}

	lemma_auto(sum(append(xs, ys))) void sum_append(list<int> xs, list<int> ys)
	requires true;
	ensures sum(append(xs, ys)) == sum(xs) + sum(ys);
	{
		switch(xs) {
			case nil:
			case cons(h, t): sum_append(t, ys);
		}
	}

	fixpoint int hashOf2(int h1, int h2) {
		return (h1^h2);
	}

	fixpoint int hashOf3(int h1, int h2, int h3) {
		return hashOf2(hashOf2(h1,h2),h3);
	}




@*/

/* These are the predicates defining representation invariants for the blockchain blocks and transactions. */

/*@

	predicate isBlock(Block b;int h) = b == null ? h == 0 : b.BlockInv(_, _, h, _);

	predicate TransHash(unit a, Transaction t; int hash) = (t == null) ? (emp &*& hash == 0) : (TransInv(t, ?s, ?r, ?v) &*& hash == tansactionHash(s,r,v));

	fixpoint boolean ValidID(int id) {
		return 0 <= id && id < Block.MAX_ID;
	}
	
	predicate ValidNonce(int n, int hp, int body) = hashOf3(body, hp, n) % 100 == 0;

@*/

/*
   The interface of the blockchain blocks.

   It contains an instance predicate that is then defined in
   two subclasses that define a summary block and a simple block.

   This predicate defines the representation invariant for blockchain blocks.

*/

interface Block {
	//@ predicate BlockInv(Block p, int hp, int h, int r);

	static final int MAX_ID = 100;
	static final int MAX_TX = 100;

	int balanceOf(int id);
	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r) &*& ValidID(id) == true;
	//@ ensures [f]BlockInv(p, hp, h, r);

	Block getPrevious();
	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r);
	//@ ensures [f]BlockInv(p, hp, h, r) &*& result == p;

	int getPreviousHash();
	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r);
	//@ ensures [f]BlockInv(p, hp, h, r) &*& result == hp;

	int hash();
	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r);
	//@ ensures [f]BlockInv(p, hp, h, r) &*& result == h;

    	int getRandom();
    	//@ requires [?f]BlockInv(?p, ?hp, ?h, ?r);
    	//@ ensures [f]BlockInv(p, hp, h, r) &*& result == r;
    
}
