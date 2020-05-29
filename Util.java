import java.time.format.*;
import java.time.LocalDateTime;

import java.util.*;

public class Util {

    public static String time() 
    //@ requires true;
    //@ ensures result != null;
    {
        LocalDateTime t = LocalDateTime.now();
        DateTimeFormatter f = DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm:ss");
        
        if( f!=null ) {
            String s = f.format(t);
            return s != null ? s : "";
        } else
            return "";
    }

	
    public static int randomInt(int min, int max) 
    //@ requires min <= max;
    //@ ensures min <= result &*& result <= max;
    {
	Random rand = new Random();
	return min + rand.nextInt(max-min+1);
    }
    
    public static int randomInt() 
    //@ requires true; 
    //@ ensures true;
    {
	Random rand = new Random();
	return rand.nextInt();
    }

}
