package leidenuniv.symbolicai;

import java.io.File;
import java.util.HashMap;
import java.util.Scanner;
import java.util.Vector;

import leidenuniv.symbolicai.environment.Maze;
import leidenuniv.symbolicai.logic.Predicate;
import leidenuniv.symbolicai.logic.Sentence;

public class RunMe {
    // This is our main program class
    // It loads a world, makes an agent and then keeps the agent alive by allowing
    // it to complete it's sense think act cycle
    public static void main(String[] args) {
        // testSubstitute();
        // testUnifiesWith();
        // testFindAllSubstitutions();
        // return;
        // Load a world    	
    	
        Maze w = new Maze(new File("data/prison.txt"));
        // Create an agent
        Agent a = new MyAgent();
        a.DEBUG = true;
        a.HUMAN_DECISION = true;
        a.VERBOSE = true;
        // Load the rules and static knowledge for the different steps in the agent
        // cycle
        a.loadKnowledgeBase("percepts", new File("data/percepts.txt"));
        a.loadKnowledgeBase("program", new File("data/program.txt"));
        a.loadKnowledgeBase("actions", new File("data/actions.txt"));

        // If you need to test on a simpler file, you may use this one and comment out
        // all the other KBs:
        // a.loadKnowledgeBase("program", new File("data/family.txt"));

        Scanner io = new Scanner(System.in);

        while (true) {
            // have the agent run the sense-think-act loop.
            a.cycle(w);

            // wait for an enter
            System.out.println("Press <enter> in the java console to continue next cycle");
            String input = io.nextLine();

        }
    }

    public static void testFindAllSubstitutions() {
        Vector<Predicate> conditions = new Vector();
        conditions.add(new Predicate("beer(X)"));
        conditions.add(new Predicate("person(Y)"));
        conditions.add(new Predicate("drinking(X,Y)"));

        Vector<Predicate> facts = createTestFacts();

        // now we convert the vector of facts to a hashmap where the strings are the
        // toString representations of the predicates
        HashMap<String, Predicate> hashFacts = new HashMap<String, Predicate>();
        for (Predicate fact : facts) {
            hashFacts.put(fact.toString(), fact);
        }

        // creating a new agent to test this on
        Agent my = new MyAgent();
        my.VERBOSE = true;
        Vector<HashMap<String, String>> collectedSubstitutions = new Vector();
        boolean validSubstitution = my.findAllSubstitions(collectedSubstitutions, null, conditions, hashFacts);

        System.out.println(validSubstitution);
        for (HashMap<String, String> sub : collectedSubstitutions) {
            System.out.printf("Found substitution: %s\n", sub);
        }
    }

    public static Vector<Predicate> createTestFacts() {
        Vector<Predicate> facts = new Vector();
        facts.add(new Predicate("beer(heineken)"));
        facts.add(new Predicate("beer(budweiser)"));
        facts.add(new Predicate("juice(appelsap)"));
        facts.add(new Predicate("person(joost)"));
        facts.add(new Predicate("person(piet)"));
        facts.add(new Predicate("drinking(heineken,joost)"));
        facts.add(new Predicate("drinking(budweiser,piet)"));
        facts.add(new Predicate("drinking(appelsap,piet)"));

        return facts;
    }

    public static void testUnifiesWith() {
        Agent my = new MyAgent();
        my.VERBOSE = true;

        HashMap<String, String> expectedResultOne = new HashMap();
        expectedResultOne.put("X", "heineken");
        runUnifiesWithTest(1, "beer(X)", "beer(heineken)", expectedResultOne, my);
        runUnifiesWithTest(2, "beer(X)", "person(heineken)", null, my);

        HashMap<String, String> expectedResultThree = new HashMap();
        expectedResultThree.put("X", "heineken");
        expectedResultThree.put("Y", "joost");
        runUnifiesWithTest(3, "drinks(X,Y)", "drinks(heineken,joost)", expectedResultThree, my);

        HashMap<String, String> expectedResultFour = new HashMap();
        expectedResultFour.put("X", "heineken");
        runUnifiesWithTest(4, "drinks(X,joost)", "drinks(heineken,joost)", expectedResultFour, my);

        runUnifiesWithTest(5, "drinks(heineken,Y)", "drinks(budweiser,joost)", null, my);
        runUnifiesWithTest(6, "father(X,X)", "father(joost,piet)", null, my);
    }

    public static void runUnifiesWithTest(int numberOfTest, String predicate, String fact, Object expectedResult,
            Agent my) {
        Predicate predicateObj = new Predicate(predicate);
        Predicate factObj = new Predicate(fact);

        HashMap<String, String> result = my.unifiesWith(predicateObj, factObj);

        String successMessage = String.format("Successfully ran unifiesWith test %d\n", numberOfTest);
        String errorMessage = String.format(
                "Unexpected unifiesWith test %d\npredicateObj: %s\nfactObj: %s\nresult: %s\nexpected: %s\n",
                numberOfTest, predicateObj, factObj, result, expectedResult);
        if (expectedResult == null) {
            assertCustom(result == expectedResult, successMessage, errorMessage);
            return;
        }
        assertCustom(expectedResult.equals(result), successMessage, errorMessage);
    }

    public static void testSubstitute() {
        Agent my = new MyAgent();
        my.VERBOSE = true;

        HashMap<String, String> vars = new HashMap();
        vars.put("X", "heineken");
        vars.put("Y", "joost");

        HashMap<String, String> incompleteVars = new HashMap();
        incompleteVars.put("X", "budweiser");

        runSubstituteTest(1, "beer(X)", vars, "beer(heineken)", my);
        runSubstituteTest(2, "beer(Y)", incompleteVars, "beer(Y)", my); // will fail to substitute anything so will
                                                                        // return the same predicate
        runSubstituteTest(3, "drinks(X,Y)", vars, "drinks(heineken,joost)", my);
        runSubstituteTest(4, "drinks(X,joost)", incompleteVars, "drinks(budweiser,joost)", my);
        runSubstituteTest(5, "drinks(heineken,Y)", incompleteVars, "drinks(heineken,Y)", my);
    }

    public static void runSubstituteTest(int numberOfTest, String predicate, HashMap<String, String> variables,
            String expectedPredicateResult, Agent my) {
        Predicate old = new Predicate(predicate);
        Predicate expected = new Predicate(expectedPredicateResult);

        Predicate newP = my.substitute(old, variables);
        String successMessage = String.format("Successfully ran substitute test %d\n", numberOfTest);
        String errorMessage = String.format("Unexpected substitution test %d, old: %s\nnew: %s\nexpected: %s\n",
                numberOfTest, old, newP, expected);
        assertCustom(newP.toString().equals(expected.toString()), successMessage, errorMessage);
    }

    public static void assertCustom(boolean condition, String successMessage, String errorMessage) {
        if (condition) {
            System.out.println(successMessage);
            return;
        }
        System.out.println(errorMessage);
    }

}
