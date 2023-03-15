# Lambda Calculus Type Inference

This project in the final assignment (5) provides a type inference for any valid term of the lambda calculus. 

Some code was given for the assignment and some was taken from previously completed lab-sheets. 

### Assignment 1 
occurs: returns true/false if the provided atom occurs in the given type.

findAtoms: returns an ordered list of all atoms in a term.

### Assignment 2
sub: applies a valid substitution to a given type.

subs: applies a list of substitutions to a given type. With the tail of the list applied first. 

### Assignment 3 
sub_u: applies a substitution to a list of unification pairs.

step: performs a single transition in the unification algorithm.

unify: compute the unification algorithm.

### Assignment 4
conclusion: extracts the concluding judgement from a derivation.

subs_ctx/jdg/der: applies a list of substitions to every type in context/judgement/derivation respectively. Similar to subs above.

### Assignment 5 
Completes a full type derivation of a given lambda calculus term 
