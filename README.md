# Group Meeting Minimization Problem

## Content

This repository presents a solution to the group meeting minimization problem (GMM problem).

You can find:
- a .pdf file presenting the GMM problem, giving solutions of that problem and proving (in natural language) their correctness
- a .v file containing a rocq proof of the same result (technically, the function `f_6` is not exactly the one of the paper, but the three last step are reversed, so it is quite equivalent)

An implementation of these functions can be found [here](https://benjamin.freecluster.eu/solver_GMM/index.html) (I'm deeply sorry, it's JavaScript...).

## The GMM problem

Let N be a positive integer. Imagine we have N workshops and 2N groups. We have N time slots. We want to assign a workshop for any group at each time step such that:
- every group visit each workshop exactly once
- every workshops hosts exactly two groups at each time step
- the number of "recurring encounter" (ie the number of time two groups that already met meet again at the same workshop

We can find an equivalent formulation exploiting graphs (it is presented in the paper, not in the rocq file).

Note: To the author's knowledge, this result is novel. However, the possibility of a prior solution cannot be entirely excluded due to the limitations of the literature search. This problem may already have been introduced, maybe with another name and a different formulation.

## Warning

Before you start reading the rocq proof, I have to apologize. I know that the proofs are ~~a bit~~ ugly. I could have used more rocq features, my way of representing Z/NZ is far from optimal. Please be indulgent, this is my first "big rocq project". I know that proofs contain many copy and paste. I know many lemma don't have inspired names. I know my proofs are really laborious. I know my definitions are low-level. But at least the proofs are correct...

If you see any error (in the definitions of my rocq file, or in the paper), please let me know.
