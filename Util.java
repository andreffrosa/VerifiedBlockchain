import java.time.format.*;
import java.time.LocalDateTime;

//import java.util.Random;

//import verifast.internal.*;
import java.util.*;

public class Util {

    public static String time() 
    //@ requires true;
    //@ ensures true;
    {
        LocalDateTime t = LocalDateTime.now();
        DateTimeFormatter f = DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm:ss");
        if(f!=null)
            return f.format(t);
        else
            return "";
    }

	
    public static int randomInt(int min, int max) 
    //@ requires 0 <= min &*& min <= max;
    //@ ensures min <= result &*& result <= max;
    {
	Random rand = new Random();
	return min + rand.nextInt(max-min+1);
    }

}
