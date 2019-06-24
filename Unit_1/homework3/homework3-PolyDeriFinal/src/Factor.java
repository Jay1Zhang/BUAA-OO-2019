import java.math.BigInteger;

public abstract class Factor {
    //public Factor();

    public abstract BigInteger getIndex();

    public abstract Term diff();

    public abstract String toString();

}
