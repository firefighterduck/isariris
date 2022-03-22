# Automation Concepts and Observations

## Basic Differences to Coq/IPM
* Basic conceptual difference to Coq: no named hypotheses but moving of subterms
* no proof context like in IPM but implicit duplication where possible (and explicit dropping possible)
* translate type class approach to predicates on iprops, instances to lemmata, instance search to "logic programming" by classical tableau prover/sequent style reasoning on instance lemmata

## Technicalities
* implicit steps: moving, reordering subgoals, removing emp, unfolding associativity, coercion (upred_holds/entailment by method/attribute, upred_valid/upred_pure valid by rule)
* problems: can't rewrite terms/unify with unfolding/symbolic execution, matching with subgoal fixation breaks a few nice patterns, duplication handling can be rather involved, instantiation of/with skolem variables
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
* splitting based: can move several terms on lhs at once, can not move out of some wrappers, requires I-pattern, can be done with "logic programming", requires lots of emps, not ordered,not guaranteed to move all parts or at most one per subpattern, O-pattern can also work but is very hacky
* framing: works only for rhs, can move out of most wrappers, based on "logic programming",very simple but powerfull


Note: I-pattern = inner pattern, e.g. pattern "P" to transform "later (P\*Q)" into "(later Q) \* (later P)"; O-pattern = outer pattern, e.g. pattern "later P" to transform "(later (P\*Q)) \* (persistent P)" into "(later Q) \* (persistent P) \* (later P)"


## About further automation
* Diaframe approach: syntax directed (by symbolic execution with preconditions), possibly under modalities/quantifiers
* Diaframe hints based on bi-abduction (single hypothesis + goal as keys), allows to consume hypothesis and exchange goal for antiframe+frame with modalities and quantifiers, lhs abduction hints (all the rest in antiframe, no frame)
* Hints for several classes of rules: ghost state updates, combination of predicates, ghost state allocations, invariant allocation, framing, etc., higher order hints
* In general first hints that match a specific hypothesis/goal pair, then those that only match a goal (e.g. allocation)
* Proof search basic idea: rewrite to a pseudo normal form, then use hint search to find out what to do next
* Proof search procedure by case distinction on goal (no backtracking, only one case applicable):
    * introduce id modality if goal has no top level modality
    * split modalities if two and top is not introducible (e.g. needs to do view-shift or close an invariant)
    * otherwise combine into single or introduce right away
    * lift universal quantifier
    * ...
* case distinction essentially parsing a formal language on top of Iris base logic that consists of the same terms but separates them into different classes that guide the case distinction (e.g. a modality on top of a later is different than the same modality on top of a pure), this aims at normalizing into a form that has a modality on top, a quantifier below that and then an actual goal to match against (this is the format that the hints expect)
* Hint search: needs to traverse all known hints + apply recursive rules to find new ones on demand, actual strategy: first use all hypotheses related hints (e.i. that oly require a certain structure of the hypotheses and doesn't require any goal structure), and only afterwards use goal related rules (until user defined hint is found), does backtrack to find a suitable hint (but doesn't backtrack if proof search step fails), whether a hint is suitable might depend on orthogonal properties
* Top level tactics do chunks of steps, repeat until stuck/solved
* Diaframe does not use the IPM environment approach to represent goals but has an own format that is more suitable for automation and single steps
* Brute force approach: can actually do most rewriting steps/normalizing, only invariant opening/closing, allocation, etc. explicitly necessary
