package leidenuniv.symbolicai;

import java.util.Collection;
import java.util.HashMap;
import java.util.Vector;
import java.util.stream.Stream;

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

        KB mergeKB = new KB();
        Vector<Sentence> nonFacts = new Vector();
        // add all the facts to the mergeKB and get all non-facts from the kb
        for (Sentence rule : kb.rules()) {
            if (rule.conditions.size() == 0) {
                mergeKB.add(rule);
            } else {
                nonFacts.add(rule);
            }
        }

        boolean rulesAreBeingAdded = true;
        while (rulesAreBeingAdded) {
            int oldRuleCount = mergeKB.rules().size();

            // create the facts
            HashMap<String, Predicate> facts = new HashMap<String, Predicate>();
            for (Sentence rule : mergeKB.rules()) {
                facts.put(rule.toString(), new Predicate(rule));
            }

            // get all the rules that have a single conclusion and add them to the knowledge
            // base
            for (Sentence rule : nonFacts) {
                Vector<HashMap<String, String>> allSubstitutions = new Vector<HashMap<String, String>>();
                findAllSubstitions(allSubstitutions, null, rule.conditions, facts);

                // now go through all the conclusions in the rule and add the substituted
                // versions to the mergeKB
                // versions to the mergeKB
                for (HashMap<String, String> substitution : allSubstitutions) {
                    Predicate conclusion = rule.conclusions.firstElement();
                    Predicate substitutedPredicate = substitute(conclusion, substitution);
                    mergeKB.add(new Sentence(substitutedPredicate.toString()));
                }
            }

            int newRuleCount = mergeKB.rules().size();
            rulesAreBeingAdded = newRuleCount > oldRuleCount;
        }
        return mergeKB;

    }

    @Override
    public boolean findAllSubstitions(Collection<HashMap<String, String>> allSubstitutions,
            HashMap<String, String> substitution, Vector<Predicate> conditions, HashMap<String, Predicate> facts) {

        // the base case is that all the conditions were processed
        if (conditions.size() == 0) {
            // if we reach size 0 in the conditions we can return true since all conditions
            // are correctly substituted, therefore we can also add our final substitution
            // to allSubstitutions
            allSubstitutions.add(substitution);
            return true;
        }

        // getting the first condition and creating a new deepcopied vector with the
        // condition removed
        Predicate firstCondition = conditions.firstElement();
        Vector<Predicate> newConditions = (Vector<Predicate>) conditions.clone();
        newConditions.remove(0);

        // first we unify our first condition with any variables that have been found
        // already
        Predicate substitutedCondition = firstCondition;
        substitutedCondition = this.substitute(firstCondition, substitution);

        // if the condition is bound and a '==' or '!=' operator and the arguments
        // within the condition hold to these operators we can continue to the next
        // condition (all of this is checked within the eql() and not() methods of the
        // Predicate)
        if (substitutedCondition.eql() || substitutedCondition.not()) {
            return this.findAllSubstitions(allSubstitutions, substitution, newConditions, facts);
        }

        // if the condition is a not or an eql operator or a negation and not bound, it
        // means that the condition is not bound at this point and for these special
        // Predicates its best to delegat them to a later time when maybe all the
        // variables were found for the condition.
        if (substitutedCondition.not || substitutedCondition.eql
                || (!substitutedCondition.bound() && substitutedCondition.neg)) {

            // first we check if there are still predicates left that are not 'eql' or
            // 'not' or 'neg' predicates (because we can still find variable substitutions
            // in all other conditions that are non reserved)
            boolean thereAreStillNonReservedPredicatesLeft = newConditions.stream()
                    .anyMatch(pred -> !pred.not && !pred.eql && !pred.neg);

            // if there are still non reserved predicates left then we can push our current
            // predicate to the end of the newConditions vector and continue checking the
            // next predicate for substitution, the return statement under here makes use of
            // shortcircuiting to achieve this
            if (thereAreStillNonReservedPredicatesLeft) {
                newConditions.add(firstCondition); // push the current predicate to the end of the conditions
                return findAllSubstitions(allSubstitutions, substitution, newConditions, facts);
            }

            // return false if there are only reserved predicates left
            return false;
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

            // at this point any substitutedCondition is bound and if a unification is found
            // for the condition this automatically means the condition doesn't hold true
            // and therefore we return false.
            if (substitutedCondition.neg) {
                return false;
            }

            // we will make it so unifyingVars now contains all the right substitions that
            // we had in substition as well if this is not empty
            if (substitution != null) {
                unifyingVars.putAll(substitution);
            }

            // we continue with the next condition and the newly found substituted variable
            findAllSubstitions(allSubstitutions, unifyingVars, newConditions, facts);
        }

        // if the condition is a negation and we made it to this point in the function
        // it means that the condition is bound and it didn't find any unifications for
        // it. this means that the negation holds and we can continue to the next
        // condition.
        if (substitutedCondition.neg) {
            return findAllSubstitions(allSubstitutions, substitution, newConditions, facts);
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
