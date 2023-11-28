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
        // This method should perform a forward chaining on the kb given as argument,
        // until no new facts are added to the KB.
        // It starts with an empty list of facts. When ready, it returns a new KB of
        // ground facts (bounded).
        // The resulting KB includes all deduced predicates, actions, additions and
        // deletions, and goals.
        // These are then processed by processFacts() (which is already implemented for
        // you)
        // HINT: You should assume that forwardChain only allows *bound* predicates to
        // be added to the facts list for now.

        // TODO: remove the if statement whenever this is finished
        if (false) {
            KB mergeKB = new KB();
            boolean rulesAreBeingAdded = true;
            while (rulesAreBeingAdded) {
                int currentRuleCount = mergeKB.rules().size();
                // TODO: derive any new rules from the given 'kb' parameter
                // TODO: merge these rules to 'mergeKB'
                int newRuleCount = mergeKB.rules().size();
                rulesAreBeingAdded = newRuleCount > currentRuleCount;
            }
            return mergeKB;
        }

        return null;
    }

    @Override
    public boolean findAllSubstitions(Collection<HashMap<String, String>> allSubstitutions,
            HashMap<String, String> substitution, Vector<Predicate> conditions, HashMap<String, Predicate> facts) {

        // the base case is that all the conditions were processed
        // if there was one substitution found then we return true, otherewise we return
        // false
        if (conditions.size() == 0) {
            // if we reach size 0 in the conditions we can return true since all conditions
            // are correctly substituted
            allSubstitutions.add(substitution);
            return true;
        }
        
        //Dealing with reserved predicates
        if (conditions.size()==1) {
        	// If conditions include =(x,y)
        	if (conditions.firstElement().eql()) {
        		Term x = conditions.firstElement().getTerm(0);
        		Term y = conditions.firstElement().getTerm(1);
        		if (!substitution.get(x.toString()).equals(substitution.get(y.toString()))){
        				// if x and y are different keys that map to different values, remove the y-value pair.
        			substitution.remove(y.toString());
        		}
        	}
        	// If conditions include !=(x,y)
        	if (conditions.firstElement().not()) {
        		// Requirement is that different keys map to different values
            	Term x = conditions.firstElement().getTerm(0);
            	Term y = conditions.firstElement().getTerm(1);
            	if (!x.equals(y) && substitution.get(x.toString()).equals(substitution.get(y.toString()))){
            		// if x and y are different keys that map to the same value, remove the y-value pair
            		substitution.remove(y.toString());
            		}
        	}
        }

        // How do we know when to quit the conditions if we need the return value of
        // findAllSubstitutions in this method as well?

        // getting the first condition and creating a new deepcopied vector with the
        // condition removed
        	
        // If the conditions is a reserved predicate, add it to the end and remove it from its current position 
        if (conditions.firstElement().eql() || conditions.firstElement().not) {
        	conditions.add(conditions.firstElement());
        	conditions.remove(0);
        }
        Predicate firstCondition = conditions.firstElement();
        Vector<Predicate> newConditions = (Vector<Predicate>) conditions.clone();
        newConditions.remove(0);
 
        // there is a substitution already, we need to check this agains the rest of the
        // conditions to see if the variables unify in the other predicates as well
        // first we unify our first condition with any variables that have been found
        // already
        Predicate substitutedCondition = firstCondition;
        substitutedCondition = this.substitute(firstCondition, substitution);

        // if the substituted condition is bound and is not found in our facts base it
        // means that there is no valid substitution for this condition with the given
        // variables, thus we return false
        if (substitutedCondition.bound()) {
            // return false if there is no fact that unifies with this condition, go to the
            // next condition if it does have a fact that it can unify with.
            return facts.get(substitutedCondition.toString()) == null ? false
                    : this.findAllSubstitions(allSubstitutions, substitution, newConditions, facts);
        }

        // if no substitution was built yet, this means we are at the top level and we
        // need to loop through all the facts to find a substition to try out for all
        // the other conditions
        for (Predicate fact : facts.values()) {
            HashMap<String, String> unifyingVars = unifiesWith(substitutedCondition, fact);
            // the condition doesn't unify with the fact
            if (unifyingVars == null) {
                continue;
            }

            // we will make it so unifyingVars now contains all the right substitions that
            // we had in substition as well if this is not empty
            if (substitution != null) {
                unifyingVars.putAll(substitution);
            }

            // we continue with the next condition and the newly found substituted variable
            findAllSubstitions(allSubstitutions, unifyingVars, newConditions, facts);
        }

        // we return true if we found at least one valid substitution, otherwise we
        // return false
        return allSubstitutions.size() > 0;

        // Recursive method to find *all* valid substitutions for a vector of
        // conditions, given a set of facts
        // The recursion is over Vector<Predicate> conditions (so this vector gets
        // shorter and shorter, the farther you are with finding substitutions)
        // It returns true if at least one substitution is found (can be the empty
        // substitution, if nothing needs to be substituted to unify the conditions with
        // the facts)
        // allSubstitutions is a list of all substitutions that are found, which was
        // passed by reference (so you use it build the list of substitutions)
        // substitution is the one we are currently building recursively.
        // conditions is the list of conditions you still need to find a subst for (this
        // list shrinks the further you get in the recursion).
        // facts is the list of predicates you need to match against (find substitutions
        // so that a predicate form the conditions unifies with a fact)
    }

    @Override
    public HashMap<String, String> unifiesWith(Predicate p, Predicate f) {
        boolean namesAreNotTheSame = !f.getName().equals(p.getName());
        boolean numberOfTermsAreNotTheSame = f.getTerms().size() != p.getTerms().size();
        boolean fIsNotBound = !f.bound();
        if (namesAreNotTheSame || numberOfTermsAreNotTheSame || fIsNotBound) {
            // returns null because either if the predicates can't be unified with each
            // other
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
            } else if (!pTerm.toString().equals(fTerm.toString())) {
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

        if (s == null) {
            // don't do anything if the given hashmap is null
            return old;
        }

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
        // The main iterative deepening loop
        // Returns a plan, when the depthFirst call returns a plan for depth d.
        // Ends at maxDepth
        // Predicate goal is the goal predicate to find a plan for.
        // Return null if no plan is found.
        return null;
    }

    @Override
    public Plan depthFirst(int maxDepth, int depth, KB state, Predicate goal, Plan partialPlan) {
        // Performs a depthFirst search for a plan to get to Predicate goal
        // Is a recursive function, with each call a deeper action in the plan, building
        // up the partialPlan
        // Caps when maxDepth=depth
        // Returns (bubbles back through recursion) the plan when the state entails the
        // goal predicate
        // Returns null if capped or if there are no (more) actions to perform in one
        // node (state)
        // HINT: make use of think() and act() using the local state for the node in the
        // search you are in.
        return null;
    }
}
