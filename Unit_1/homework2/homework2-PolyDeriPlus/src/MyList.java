import java.math.BigInteger;

public class MyList {
    private BigInteger aaa;
    private BigInteger bbb;
    private BigInteger ccc;

    public MyList(BigInteger a, BigInteger b, BigInteger c) {
        this.aaa = a;
        this.bbb = b;
        this.ccc = c;
    }

    public int hashCode() {
        return aaa.hashCode() + bbb.hashCode() + ccc.hashCode();
    }

    public boolean equals(Object o) {
        MyList mylist = (MyList) o;
        boolean temp = this.aaa.equals(mylist.aaa)
                & this.bbb.equals(mylist.bbb) & this.ccc.equals(mylist.ccc);
        return temp;
    }

}
