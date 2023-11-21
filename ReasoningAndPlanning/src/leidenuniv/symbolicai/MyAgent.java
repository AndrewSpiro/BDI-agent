package leidenuniv.symbolicai;

import java.util.Collection;
import java.util.HashMap;
import java.util.Vector;

import leidenuniv.symbolicai.logic.KB;
import leidenuniv.symbolicai.logic.Predicate;
import leidenuniv.symbolicai.logic.Sentence;
import leidenuniv.symbolicai.logic.Term;

public class MyAgent extends Agent {
	
	@Override
	public KB forwardChain(KB kb) {
		//This method should perform a forward chaining on the kb given as argument, until no new facts are added to the KB.
		//It starts with an empty list of facts. When ready, it returns a new KB of ground facts (bounded).
		//The resulting KB includes all deduced predicates, actions, additions and deletions, and goals.
		//These are then processed by processFacts() (which is already implemented for you)
		//HINT: You should assume that forwardChain only allows *bound* predicates to be added to the facts list for now.
		
		return null;
	}

	@Override
	public boolean findAllSubstitions(Collection<HashMap<String, String>> allSubstitutions,
			HashMap<String, String> substitution, Vector<Predicate> conditions, HashMap<String, Predicate> facts) {
		//Recursive method to find *all* valid substitutions for a vector of conditions, given a set of facts
		//The recursion is over Vector<Predicate> conditions (so this vector gets shorter and shorter, the farther you are with finding substitutions)
		//It returns true if at least one substitution is found (can be the empty substitution, if nothing needs to be substituted to unify the conditions with the facts)
		//allSubstitutions is a list of all substitutions that are found, which was passed by reference (so you use it build the list of substitutions)
		//substitution is the one we are currently building recursively.
		//conditions is the list of conditions you  still need to find a subst for (this list shrinks the further you get in the recursion).
		//facts is the list of predicates you need to match against (find substitutions so that a predicate form the conditions unifies with a fact)
		
		//the facts hashmap is updated with the predicate.toString as the key and the predicate as the value
		for (Predicate p : conditions) {
			Predicate newFact = substitute(p, substitution);
			if (facts.containsKey(newFact.toString())) {
				continue;
				//if the key already exists, don't update the facts
			}
			facts.put(newFact.toString(), newFact);
		
			//returns the first valid substitution for which cond unifies with a fact
			for (HashMap.Entry<String, Predicate> fact : facts.entrySet()) {
				substitution = unifiesWith(p, fact.getValue());
				// add any substitution that unifies a cond with a fact to a hashmap
				allSubstitutions.add(substitution);
			}
		}
		findAllSubstitions(allSubstitutions, substitution, conditions, facts);
		return false;
	}

	@Override
	public HashMap<String, String> unifiesWith(Predicate p, Predicate f) {
		//Returns the valid substitution for which p predicate unifies with f
		//You may assume that Predicate f is fully bound (i.e., it has no variables anymore)
		//The result can be an empty substitution, if no subst is needed to unify p with f (e.g., if p an f contain the same constants or do not have any terms)
		//Please note because f is bound and p potentially contains the variables, unifiesWith is NOT symmetrical
		//So: unifiesWith("human(X)","human(joost)") returns X=joost, while unifiesWith("human(joost)","human(X)") returns null 
		//If no subst is found it returns null
		
		boolean namesAreNotTheSame = f.getName()!= p.getName();
        boolean numberOfTermsAreNotTheSame = f.getTerms().size() != p.getTerms().size();
        boolean fIsNotBound = !f.bound();
        if (namesAreNotTheSame || numberOfTermsAreNotTheSame || fIsNotBound) {
        	return null;
        }
		
        HashMap<String, String> result = new HashMap<String, String>();
        
        // test case: unifiesWith("father(X, joost)", "father(piet, joost)") -> true
        // test case: unifiesWith("brother(X, X)", "brother(joost, piet)") -> false
        for (int i = 0; i < p.getTerms().size(); i++) {
            Term pTerm = p.getTerm(i);
            Term fTerm = f.getTerm(i);

            // check if pTerm is a variable or a constant, if it is a variable, try
            // substitution, otherwise check if both constants at that position are the same
            // in the given predicates
            if (pTerm.var) {
                String key = p.getTerm(i).toString();
                String value = f.getTerm(i).toString();

                // here we check if we already found a substitution for this variable earlier in
                // the predicate,
                // if so we check if it can be unified such that it has the same value as the
                // first substituted instance.
                // this is for example handy for the case:
                // unifiesWith("brother(X, X)", "brother(joost, piet)") which would otherwise
                // return a valid hashmap and not null.
                if (result.containsKey(key) && result.get(key) != value) {
                    return null;
                }

                result.putIfAbsent(key, value);
            } else if (pTerm.toString() != fTerm.toString()) {
                return null;
            }
        }

        return result;
        // Returns the valid substitution for which p predicate unifies with f
        // You may assume that Predicate f is fully bound (i.e., it has no variables
        // anymore)
        // The result can be an empty substitution, if no subst is needed to unify p
        // with f (e.g., if p an f contain the same constants or do not have any terms)
        // Please note because f is bound and p potentially contains the variables,
        // unifiesWith is NOT symmetrical
        // So: unifiesWith("human(X)","human(joost)") returns X=joost, while
        // unifiesWith("human(joost)","human(X)") returns null
        // If no subst is found it returns null
    }

    @Override
    public Predicate substitute(Predicate old, HashMap<String, String> s) {
        // TODO: ask if all terms need to be substituted by this method or that certain
        // terms can be left as their variable name if they were not found as keys in
        // the hashmap
        // substitute all possible terms

        // first we create a copy of the old predicate
        Predicate newPredicate = new Predicate(old.toString());

        // then we substitute all variables in the new predicates with key/value pairs
        // in the hashmap
        for (Term t : newPredicate.getTerms()) {
            t.substitute(s);
        }

        return newPredicate;

        // Substitutes all variable terms in predicate <old> for values in substitution
        // <s>
        // (only if a key is present in s matching the variable name of course)
        // Use Term.substitute(s)
    }

	@Override
	public Plan idSearch(int maxDepth, KB kb, Predicate goal) {
		//The main iterative deepening loop
		//Returns a plan, when the depthFirst call returns a plan for depth d.
		//Ends at maxDepth
		//Predicate goal is the goal predicate to find a plan for.
		//Return null if no plan is found.
		return null;
	}

	@Override
	public Plan depthFirst(int maxDepth, int depth, KB state, Predicate goal, Plan partialPlan) {
		//Performs a depthFirst search for a plan to get to Predicate goal
		//Is a recursive function, with each call a deeper action in the plan, building up the partialPlan
		//Caps when maxDepth=depth
		//Returns (bubbles back through recursion) the plan when the state entails the goal predicate
		//Returns null if capped or if there are no (more) actions to perform in one node (state)
		//HINT: make use of think() and act() using the local state for the node in the search you are in.
		return null;
	}
}
