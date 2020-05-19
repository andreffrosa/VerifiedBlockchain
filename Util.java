import java.time.format.DateTimeFormatter;
import java.time.LocalDateTime;

public class Util {

    public static String time() 
    //@ requires true;
    //@ ensures true;
    {
        return DateTimeFormatter.ofPattern("dd/MM/yyyy HH:mm:ss").format(LocalDateTime.now());
    }

}
