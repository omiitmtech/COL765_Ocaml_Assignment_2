# COL765_Ocaml_Assignment_2
In this programming assignment, you will take the data type of propositions defined in class and write simple programs to manipulate them.
# Assignment Details
Propositions, valuations, truth, and normal forms.
In this programming assignment, you will take the data type of propositions defined in class and write simple programs to manipulate them.

type prop = Letter of string | T | F

    | Not of prop | And of prop * prop

    | Or of prop * prop | Impl of prop * prop  | Iff of prop * prop ;;


The functions you need to implement are:

ht: prop -> int, which returns the height of a proposition (syntax tree).
size: prop -> int, which returns the number of nodes in a proposition (syntax tree)
truth: prop -> (string -> bool) -> bool, which evaluates a proposition with respect to a given truth assignment to propositional letters.
nnf: prop -> prop, which converts a proposition into negation normal form.
subst: prop -> (string -> prop) -> prop, which applies a substitution to a prop.
kleisli:  (string -> prop) -> (string -> prop) -> prop -> prop, which composes two propositions.
In light of the Relevance Lemma, you may wish to choose a compact representation of valuations, instead of simply string -> bool.

Syntactic :
vars: prop -> string set, which returns the set of propositional letters that appear in a proposition.
cnf: prop -> prop set set, which converts a proposition into conjunctive normal form (POS) as a set of clauses, each of which is a set of literals (a special subset of prop, comprising only letters and negations of letters).
dnf: prop -> prop set set,  which converts a proposition into disjunctive normal form (SOP) as a set of terms, each of which is a set of literals.

Semantic :

entails: prop set -> prop -> bool, which checks if a given proposition is a logical consequence of a given 

isTautology: prop -> bool, which checks if a proposition is a tautology.
isSatisfiable: prop -> bool, which checks if a proposition is satisfiable, 
isContradiction: prop -> bool, which checks if a proposition is a tautology.

isEquivalent: prop -> prop -> bool, which checks if two propositions are logically equivalent.
isFalsifiable: prop -> bool, which checks if a proposition is satisfiable
set of propositions.


satisfier: prop -> valuation, which returns a satisfying truth assignment if it exists.
falsifier: prop -> valuation, which returns a falsifying truth assignment if it exists.

models: prop -> valuation set, which returns the set of ``all valuations'' that satisfy a given prop.

For each of your functions, indicate the TIME and SPACE complexity in terms of the size of the proposition and number of distinct letters.

