import java.io.File;
import java.io.FileNotFoundException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Random;

public class RandInstr {
    private static final int MAX_INSTR = 300;
    private static final int MAX_PATH_LEN = 75;
    private static final int MIN_PATH_LEN = 2;
    private static final int MAX_DISTINCT_NODE_NUM = 100;
    private static final int MAX_CHANGE_CHANCE = 50;
    private static final int MAX_LINER_QUERY = 500;

    private static final Random random = new Random();
    private static final ArrayList<String> func = new ArrayList<String>() {
        {
            add("PATH_ADD");
            // add("PATH_REMOVE");
            // add("PATH_REMOVE_BY_ID");
            add("LEAST_TICKET_PRICE");
            add("LEAST_UNPLEASANT_VALUE");
            add("PATH_GET_ID");
            add("PATH_GET_BY_ID");
            add("CONTAINS_PATH");
            add("COMPARE_PATHS");
            add("PATH_COUNT");
            add("PATH_SIZE");
            add("PATH_DISTINCT_NODE_COUNT");
            add("DISTINCT_NODE_COUNT");
            add("PATH_CONTAINS_NODE");
            add("CONTAINS_NODE");
            add("CONTAINS_EDGE");
            add("IS_NODE_CONNECTED");
            add("SHORTEST_PATH_LENGTH");

            add("CONNECTED_BLOCK_COUNT");
            add("LEAST_TICKET_PRICE");
            add("LEAST_TRANSFER_COUNT");
            add("LEAST_UNPLEASANT_VALUE");
        }
    };

    private static HashMap<Integer, ArrayList<Integer>> plist
            = new HashMap<>(MAX_CHANGE_CHANCE);
    private static int pid = 0;

    public static void main(String[] args) throws FileNotFoundException {
        PrintStream printStream = new PrintStream(new File("instr.txt"));
        System.setOut(printStream);
        int countChange = 0;
        int countLine = 0;
        int countNotChange = 0;
        while (countChange + countNotChange < MAX_INSTR) {
            int randFunc = random.nextInt(func.size());
            if (plist.isEmpty()) {
                randFunc = 0;
            }
            if (randFunc < 3 && countChange < MAX_CHANGE_CHANCE) {
                System.out.print(func.get(randFunc));
                if (randFunc == 0) {
                    addPath();
                    countLine++;
                    countChange++;
                } else if (randFunc == 1 && !plist.isEmpty()) {
                    countLine++;
                    makeTwoNode();
                } else if (randFunc == 2 && !plist.isEmpty()) {
                    countLine++;
                    makeTwoNode();
                }
                // else if (randFunc == 1 && !plist.isEmpty()) {
                //     randPath();
                //     countChange++;
                // } else if (randFunc == 2 && !plist.isEmpty()) {
                //     makeID();
                //     countChange++;
                // }
                System.out.println();
            } else if (randFunc < 7 && countLine < MAX_LINER_QUERY) {
                System.out.print(func.get(randFunc));
                countLine++;
                countNotChange++;
                switch (randFunc) {
                    case 3:
                        randPath();
                        break;
                    case 4:
                        makeID();
                        break;
                    case 5:
                        randPath();
                        break;
                    case 6:
                        makeTwoID();
                        break;
                }
                System.out.println();
            } else {
                System.out.print(func.get(randFunc));
                countNotChange++;
                switch (randFunc) {
                    case 7:
                        // do nothing
                        break;
                    case 8:
                        makeID();
                        break;
                    case 9:
                        makeID();
                        break;
                    case 10:
                        // do nothing
                        break;
                    case 11:
                        makeIdAndNode();
                        break;
                    case 12:
                        makeNode();
                        break;
                    case 13:
                        makeTwoNode();
                        break;
                    case 14:
                        makeTwoNode();
                        break;
                    case 15:
                        makeTwoNode();
                        break;
                    case 16:
                        // do nothing
                        break;
                    case 17:
                    case 18:
                    case 19:
                        makeTwoNode();
                        break;
                }
                System.out.println();
            }
        }

    }

    private static int randId() {
        int index = random.nextInt(plist.size());
        int k = 0;
        for (Integer id : plist.keySet()) {
            if (k == index) {
                return id;
            }
            k++;
        }
        return random.nextInt(MAX_CHANGE_CHANCE);
    }

    private static int addNode() {
        return random.nextInt(MAX_DISTINCT_NODE_NUM);
    }

    private static int randNode() {
        ArrayList<Integer> tmp = plist.get(randId());
        return tmp.get(random.nextInt(tmp.size()));
    }

    private static void addPath() {
        int length;
        do {
            length = random.nextInt(MAX_PATH_LEN) + MIN_PATH_LEN;
        } while (length <= 0);
        ArrayList<Integer> tmp = new ArrayList<>(length);
        StringBuffer str = new StringBuffer();
        for (int i = 0; i < length; i++) {
            int nodeId = addNode();
            tmp.add(nodeId);
            str.append(" ").append(nodeId);
        }
        ++pid;
        plist.put(pid, tmp);
        System.out.print(str);
    }

    private static void randPath() {
        ArrayList<Integer> tmp;
        do {
            tmp = plist.get(randId());
        } while (tmp == null);
        StringBuffer str = new StringBuffer();
        for (Integer integer : tmp) {
            str.append(" ").append(integer);
        }
        System.out.print(str);
    }

    private static void makeID() {
        System.out.print(" " + randId());
    }

    private static void makeTwoID() {
        System.out.print(" " + randId() + " " + randId());
    }

    private static void makeIdAndNode() {
        System.out.print(" " + randId() + " " + randNode());
    }

    private static void makeNode() {
        System.out.print(" " + randNode());
    }

    private static void makeTwoNode() {
        System.out.print(" " + randId() + " " + randId());
    }
}