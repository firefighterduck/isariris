# Automation Concepts and Observations

## Basic Differences to Coq/IPM
* Basic conceptual difference to Coq: no named hypotheses but moving of subterms
* no proof context like in IPM but implicit duplication where possible (and explicit dropping possible)
* translate type class approach to predicates on iprops, instances to lemmata, instance search to "logic programming" by classical tableau prover/sequent style reasoning on instance lemmata

## Technicalities
* implicit steps: moving, reordering subgoals, removing emp, unfolding associativity, coercion (upred_holds/entailment by method/attribute, upred_valid/upred_pure valid by rule)
* problems: can't rewrite terms/unify with unfolding/symbolic execution, matching with subgoal fixation breaks a few nice patterns, duplication handling can be rather involved
* subgoals often with schematic variables that might connect several subgoals, important to make reasoning less user dependant, often implicitely unified by rules (e.g. splitting)

## Fundamental Observations
* most automization can be split into three steps: searching for/moving requirements, applying some reasoning principle/rule, some possible cleanup
* interactive guidance with patterns often necessary (otherwise either specialized ML methods or just failure if information from user is required, i.e. smart reasoning), patterns can be quite generic but must be unique, otherwise position dependant
* some rules migth come with more premises, they are then new subgoal and can either be handled in a unfied way if the rule is known or must be solved by the user
* separate handling of lhs and rhs rule application, because simplifications on the lhs are mostly allowed/won't break anything (due to the Iris base logic being intuitionistic), but on the rhs must be explicitly done by the user as this could break further reasoning steps
* Iris does not work well with structured Isar proofs due to the verbose context necessary to apply rules to the entailment, apply style is better

## Proof steps
* rule application for hypotheses: split to get lhs of rule, apply (in-)directly, can also be used to apply wands from other hypotheses
* handling of existential quantifiers easy, but instantiation only one term per call
* pull all pure hypotheses into context, try to solve pure goals from context/simp
* eliminate modalities after rule application with nested "logic programming"

## Moving
* by commutativity: might require checking first, works on both sides, to work for arbitrary large terms either moving bigger subterms or on-the-fly generation of comm lemmata, could be optimized with moving lemmata "from x to head", can't handle wrappers
* splitting based: can move several terms on lhs at once, can not move out of some wrappers, requires I-pattern, can be done with "logic programming", requires lots of emps, not ordered,not guaranteed to move all parts or at most one per subpattern
* framing: works only for rhs, can move out of most wrappers, based on "logic programming",very simple but powerfull
