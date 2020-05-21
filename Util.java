import java.time.format.*;
import java.time.LocalDateTime;

//import verifast.internal.*;
import java.util.*;

public class Util {

    public static String time() 
    //@ requires true;
    //@ ensures true;
    {
        //return DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm:ss").format(LocalDateTime.now());
        return "";
    }
    
    /*private static double dummyRandom() 
    //@ requires true;
    //@ ensures 0 <= result &*& result < 1;
    {
    	double r = Math.random();
    	return r < 0.0 ? 0.0 : r >= 1.0 ? 0.9999999 : r;
    	
    	return 
    }*/
    
    public static int randomInt(int min, int max) 
    //@ requires min <= max;
    //@ ensures min <= result &*& result <= max;
    {
    	int delta = max - min + 1;
    	//@ assert (max - min) + 1 > 0;
    	int r = (int) (Math.random() * delta);
    	int r2 = r % delta;
    	//@ assert (max - min) + 1 > 0;
    	//@ assert r2 <= delta;
    	
    	// assert 0 <= r &*& r <= max - min + 1;
    	return r + min;
    	//return min + (max - min + 1)/15; 
    }

}
