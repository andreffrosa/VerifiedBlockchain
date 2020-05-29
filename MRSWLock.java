/* For this lab, you'll have to implement and verify  a readers-writer lock,
   also known as a multiple readers single writer lock. As the name implies,
   multiple readers can acquire the lock with reading rights, however, it can
   only be held by one writer. Furthermore, it if the lock has been acquired for
   reading, it cannot be acquired for writing and vice-versa.
*/

import java.util.concurrent.*;
import java.util.concurrent.locks.*;

/*@
	predicate_ctor MRSWLock_shared_state(MRSWLock ml) () = 
			    ml.readercount |-> ?r
			&*& ml.busy |-> ?b 
			&*& r >= 0 
			&*& (b ? r == 0 : true);
			
	predicate_ctor MRSWLock_Oktoread(MRSWLock ml)() =     
			    ml.readercount |-> ?r 
			&*& ml.busy |-> ?b 
			&*& r >= 0 
			&*& b != true;
	
	predicate_ctor MRSWLock_Oktowrite(MRSWLock ml)() =     
			    ml.readercount |-> ?r
			&*& ml.busy |-> ?b 
			&*& r == 0 
			&*& b != true;

	predicate MRSWLockInv(MRSWLock ml;) =
			    ml.mon |-> ?l
			&*& ml.OKtoread |-> ?cr
			&*& ml.OKtowrite |-> ?cw
			&*& l != null
			&*& cr != null
			&*& cw != null
			&*& lck(l, 1, MRSWLock_shared_state(ml))
			&*& cond(cr, MRSWLock_shared_state(ml), MRSWLock_Oktoread(ml))
                        &*& cond(cw, MRSWLock_shared_state(ml), MRSWLock_Oktowrite(ml));
		
@*/

class MRSWLock {

	private int readercount;
	private boolean busy;
	private ReentrantLock mon;
	private Condition OKtoread;
	private Condition OKtowrite;
	
	public MRSWLock() 
	//@ requires enter_mrswlck(1,?inv);
	//@ ensures [1]MRSWLockInv(this) &*& mrswlck(this, 1, inv);
	{
		readercount = 0;
		busy = false;
	  	//@ close MRSWLock_shared_state(this)();
    		//@ close enter_lck(1, MRSWLock_shared_state(this));
    		mon = new ReentrantLock();
    		//@ close set_cond(MRSWLock_shared_state(this), MRSWLock_Oktoread(this));
		OKtoread = mon.newCondition();
		//@ close set_cond(MRSWLock_shared_state(this), MRSWLock_Oktowrite(this));
		OKtowrite = mon.newCondition();
    		//@ close MRSWLockInv(this);
    		
    		//@ close_mrswlck(this);
	}
	
	/* 
	 * Aquires this lock for reading, after successfully returned from this
	 * method, the caller has reading rights on the state protected by this
	 * lock.
	 */
	public void readLock() 
	//@ requires [?f]MRSWLockInv(this) &*& [?f2]mrswlck(this, ?p, ?inv);
	//@ ensures [f]MRSWLockInv(this) &*& [f2]mrswlck(this, -p, inv) &*& [?q]inv() &*& q < 1;
	{
		//@ open MRSWLockInv(this);
		mon.lock();
    		//@ open MRSWLock_shared_state(this)();
		
		while(busy) 
		/*@ invariant this.readercount |-> ?r
			  &*& this.busy |-> ?b 
			  &*& r >= 0 
			  &*& (b ? r == 0 : true)
		          &*& [f]this.mon |-> ?l
			  &*& [f]this.OKtoread |-> ?cr
			  &*& [f]this.OKtowrite |-> ?cw
			  &*& l != null
			  &*& cr != null
			  &*& cw != null
			  &*& [f]lck(l, -1, MRSWLock_shared_state(this))
			  &*& [f]cond(cr, MRSWLock_shared_state(this), MRSWLock_Oktoread(this))
			  &*& [f]cond(cw, MRSWLock_shared_state(this), MRSWLock_Oktowrite(this));
		@*/
		{
			//@ close MRSWLock_shared_state(this)();
	      		try {
	      			OKtoread.await();
			} catch (InterruptedException e) {}
	     		//@ open MRSWLock_Oktoread(this)();
		}
			
		readercount = readercount + 1;
		
		//@ close MRSWLock_Oktoread(this)();
		OKtoread.signal();
    		mon.unlock();
    		//@ close [f]MRSWLockInv(this);
    		
    		//@ mrswlck_lock(this, p, -p, 1/2);
	}
	
	/* 
	 * Releases the reading lock.
	 */
	void readUnlock() 
	//@ requires [?f]MRSWLockInv(this) &*& [?f2]mrswlck(this, ?p, ?inv) &*& [?q]inv();
	//@ ensures [f]MRSWLockInv(this) &*& [f2]mrswlck(this, -p, inv);
	{
		//@ open MRSWLockInv(this);
		mon.lock();
    		//@ open MRSWLock_shared_state(this)();
    		
    		//@ assume(readercount > 0);
		readercount = readercount - 1;
		
		if(readercount == 0) {
			 //@ close MRSWLock_Oktowrite(this)();
			OKtowrite.signal();
			//@ open MRSWLock_shared_state(this)();
		} 
	
		//@ close MRSWLock_shared_state(this)();
		mon.unlock();
    		//@ close [f]MRSWLockInv(this);
    		
    		//@ mrswlck_unlock(this, p, -p, q);
	}
	
	/*
	 * Acquires this lock for writing, after successfully returned from this
	 * method, the caller has writing rights on the state protected by this
	 * lock.
	 */
	void writeLock() 
	//@ requires [?f]MRSWLockInv(this) &*& [?f2]mrswlck(this, 1, ?inv);
	//@ ensures [f]MRSWLockInv(this) &*& [f2]mrswlck(this, 0, inv) &*& [1]inv();
	{
		//@ open MRSWLockInv(this);
		mon.lock();
    		//@ open MRSWLock_shared_state(this)();
    		
		while((readercount > 0) || busy) 
		/*@ invariant this.readercount |-> ?r
			  &*& this.busy |-> ?b 
			  &*& r >= 0 
			  &*& (b ? r == 0 : true)
		          &*& [f]this.mon |-> ?l
			  &*& [f]this.OKtoread |-> ?cr
			  &*& [f]this.OKtowrite |-> ?cw
			  &*& l != null
			  &*& cr != null
			  &*& cw != null
			  &*& [f]lck(l, -1, MRSWLock_shared_state(this))
			  &*& [f]cond(cr, MRSWLock_shared_state(this), MRSWLock_Oktoread(this))
			  &*& [f]cond(cw, MRSWLock_shared_state(this), MRSWLock_Oktowrite(this));
		@*/
		{
			//@ close MRSWLock_shared_state(this)();
			try {
				OKtowrite.await();
			} catch (InterruptedException e) {}
	     		//@ open MRSWLock_Oktowrite(this)();
		}
		
		busy = true;
		
		//@ close MRSWLock_shared_state(this)();
		mon.unlock();
    		//@ close [f]MRSWLockInv(this);
    		
    		//@ mrswlck_lock(this, 1, 0, 1);
	}

	/*
	 * Releases the writing lock.
	 */
	void writeUnlock()
	//@ requires [?f]MRSWLockInv(this) &*& [?f2]mrswlck(this, 0, ?inv) &*& inv();
	//@ ensures [f]MRSWLockInv(this) &*& [f2]mrswlck(this, 1, inv);
	{
		//@ open MRSWLockInv(this);
		mon.lock();
    		//@ open MRSWLock_shared_state(this)();
    		
		busy = false;
		
		//@ close MRSWLock_Oktoread(this)();
		OKtoread.signal();
		
		mon.unlock();
    		//@ close [f]MRSWLockInv(this);
    		
    		//@ mrswlck_lock(this, 0, 1, 1);
	}
}
