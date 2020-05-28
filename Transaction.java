/*
Construction and Verification of Software 2019/20.

Project assignment to implement and verify a simplified blockchain.

2020 João Costa Seco, Eduardo Geraldo

Note: please add your names and student numbers in all files you submit.
*/

/*
   The class of transactions.

   It contains the definition for the predicate that defines the
   representation invariant for blockchain summary blocks.

*/


/*@
	predicate TransInv(Transaction t; int s, int r, int v) =
			t.send |-> s
		&*& ValidID(s) == true
		&*& t.recv |-> r
		&*& ValidID(r) == true
		&*& t.amnt |-> v &*& v > 0;

	fixpoint int tansactionHash(int s, int r, int v) {
		return ((s^r)^v);
	}
@*/
class Transaction {

    private final int send;

    private final int recv;

    private final int amnt;

    public Transaction(int send, int recv, int amount)
    //@ requires amount > 0 &*& ValidID(send) == true &*& ValidID(recv) == true;
    //@ ensures [1]TransInv(this, send, recv, amount);
    {
        this.send = send;
        this.recv = recv;
        this.amnt = amount;
    }

    public int getSender()
    //@requires [?f]TransInv(this, ?s, ?r, ?v);
    //@ensures [f]TransInv(this, s, r, v) &*& result == s;
    {
        return send;
    }

    public int getReceiver()
    //@requires [?f]TransInv(this, ?s, ?r, ?v);
    //@ensures [f]TransInv(this, s, r, v) &*& result == r;
    {
        return recv;
    }

    public int getAmount()
    //@requires [?f]TransInv(this, ?s, ?r, ?v);
    //@ensures [f]TransInv(this, s, r, v) &*& result == v;
    {
        return amnt;
    }

    public int hash()
    //@requires [?f]TransInv(this, ?s, ?r, ?v);
    //@ensures [f]TransInv(this, s, r, v) &*& result == tansactionHash(s,r,v);
    {
    	int x = send ^ recv ^ amnt;
        return x;
    }
}
