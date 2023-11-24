package leidenuniv.symbolicai;

import java.io.File;
import java.util.Collection;
import java.util.HashMap;
import java.util.Scanner;
import java.util.Vector;

import leidenuniv.symbolicai.environment.*;
import leidenuniv.symbolicai.logic.*;

public class UnitTestPublic {
	static Maze m;
	static Agent b;
	static KB family1,family2,family3,test,facts;
	static HashMap<String, String> s;
	
	//This is our main program class
	// It loads a world, makes an agent and then keeps the agent alive by allowing it to complete it's sense think act cycle 
	public static void main(String[] args) {
		//Load a world
		b=new MyAgent();
		
		family1=new KB(new File("data/family1.txt"));
		family2=new KB(new File("data/family2.txt"));
		family3=new KB(new File("data/family3.txt"));
		test=new KB(new File("data/testfacts.txt"));
		
		String allTests[]= {"1","2a","2b","3a","3b","3c","3d","3e","3f","4a","4b","4c","4d","4e","4f","4g","5a","5b","5c"};
		
		for (String t: allTests) {
			try {
				if (doTest(t))
					System.out.println("Success");
				else
					System.out.println("Failed");
			} catch (Exception e) {
				// TODO Auto-generated catch block
				System.out.println("Exception "+e+"...Failed");
			} catch (Error e) {
				// TODO Auto-generated catch block
				System.out.println("Error "+e+"...Failed");
			}

		}
		
	}
	static boolean doTest(String testnr) {
		switch(testnr) {
			case "1":
				System.out.print("Test 1: rules run with default agent?....not implemented, no unit test. ");
				return false;

			case "2a":
				System.out.print("Test 2a: substitute X and Y in parent(X,Y,sacha)?....");
				s=new HashMap<String, String>();
				s.put("X", "joost");
				s.put("Y", "leon");
				return (b.substitute(new Predicate("parent(X,Y,sacha)"), s).toString().equals("parent(joost,leon,sacha)"));

			case "2b":
				System.out.print("Test 2b: substitute X and Y in +parent(X,Y)?....");
				s=new HashMap<String, String>();
				s.put("X", "joost");
				s.put("Y", "leon");
				return (b.substitute(new Predicate("+parent(X,Y)"), s).toString().equals("+parent(joost,leon)"));
				
			case "3a":
				System.out.print("Test 3a:  unifiesWith returns empty substitution for parent(joost,leon)?....");
				s=b.unifiesWith(new Predicate("parent(joost,leon)"), new Predicate("parent(joost,leon)"));
				return (s.isEmpty());

			case "3b":
				System.out.print("Test 3b:  unifiesWith returns null for non-existent substitution for parent(joost,leon)?....");
				s=b.unifiesWith(new Predicate("parent(X,peter)"), new Predicate("parent(joost,leon)"));
				return (s==null);
				
			case "3c":
				System.out.print("Test 3c:  unifiesWith returns null for non-existent substitution for different name predicate?....");
				s=b.unifiesWith(new Predicate("parents(X,peter)"), new Predicate("parent(joost,peter)"));
				return (s==null);

			case "3d":
				System.out.print("Test 3d: unifiesWith returns correct substitution for parent(X,Y)?....");
				s=b.unifiesWith(new Predicate("parent(X,Y)"), new Predicate("parent(joost,leon)"));
				return (s.containsKey("X") && s.get("X").equals("joost") && s.containsKey("Y") && s.get("Y").equals("leon"));

			case "3e":
				System.out.print("Test 3e: unifiesWith assumes negated predicate unifies with positive predicate?....");
				s=b.unifiesWith(new Predicate("!parent(X,Y)"), new Predicate("parent(joost,leon)"));
				return (s.containsKey("X") && s.get("X").equals("joost") && s.containsKey("Y") && s.get("Y").equals("leon"));

			case "3f":
				System.out.print("Test 3f: unifiesWith correctly deals with vars and constants in one predicate and returns the correct substitution ?....");
				s=b.unifiesWith(new Predicate("parent(X,leon)"), new Predicate("parent(joost,leon)"));
				return (s.containsKey("X") && s.get("X").equals("joost"));

			case "4a":
				System.out.print("Test 4a: findAllSubst correctly finds 1 subst for male(X)>human(X)");
				return (findAllSubstitionsTest(b, "male(X)>human(X)", test)==1);

			case "4b":
				System.out.print("Test 4b: findAllSubst correctly finds 3 subst for parent(X,Y)>child(Y)");
				return (findAllSubstitionsTest(b, "parent(X,Y)>child(Y,X)", test)==3);

			case "4c":
				System.out.print("Test 4c: findAllSubst correctly finds 1 subst for parent(joost,X)&male(X)>son(X)");
				return (findAllSubstitionsTest(b, "parent(joost,X)&male(X)>son(X,joost)", test)==1);

			case "4d":
				System.out.print("Test 4d: findAllSubst correctly finds 2 subst for parent(X,Y)&!male(Y)>daughter(Y)");
				return (findAllSubstitionsTest(b, "parent(X,Y)&!male(Y)>daughter(Y)", test)==2);

			case "4e":
				System.out.print("Test 4e: findAllSubst correctly finds 2 subst for !male(Y)&parent(X,Y)>daughter(Y)");
				return (findAllSubstitionsTest(b, "!male(Y)&parent(X,Y)>daughter(Y)", test)==2);
				
			case "4f":
				System.out.print("Test 4f: findAllSubst correctly finds 2 subst for parent(Z,X)&parent(Z,Y)&!=(X,Y)>sibling(X,Y)");
				return (findAllSubstitionsTest(b, "parent(Z,X)&parent(Z,Y)&!=(X,Y)>sibling(X,Y)", test)==2);
				
			case "4g":
				System.out.print("Test 4g: findAllSubst correctly finds 2 subst for !=(X,Y)&parent(Z,X)&parent(Z,Y)>sibling(X,Y)");
				return (findAllSubstitionsTest(b, "!=(X,Y)&parent(Z,X)&parent(Z,Y)>sibling(X,Y)", test)==2);
				
			case "5a":
				System.out.print("Test 5a: basic production test, inference correctly proofs grandparent(peter,leon) and grandparent(peter,sacha)");
				facts=b.forwardChain(family1);
				return (facts.contains(new Predicate("grandparent(peter,leon)")) && facts.contains(new Predicate("grandparent(peter,sacha)")));

			case "5b":
				System.out.print("Test 5b: inference correctly proofs recursive predicate ancestor(peter,leon)");
				facts=b.forwardChain(family2);
				return (facts.contains(new Predicate("ancestor(peter,leon)")));
					
			case "5c":
				System.out.print("Test 5c: negation test, inference correctly proofs brother(leon) but not brother(sacha)");
				facts=b.forwardChain(family3);
				return (facts.contains(new Predicate("brother(leon)")) && !facts.contains(new Predicate("brother(sacha)")));
		}
		return false;
	}
	static int findAllSubstitionsTest(Agent a, String rule, KB f){
		HashMap<String,Predicate> facts=new HashMap<String,Predicate>();
		for (Sentence s:f.rules())
			facts.put(s.toString(), new Predicate(s.toString()));
		
		Collection<HashMap<String,String>> substitutions=new Vector<HashMap<String,String>>();
		a.findAllSubstitions(substitutions, new HashMap<String,String>(), new Sentence(rule).conditions, facts);
		return substitutions.size();
	}
}
