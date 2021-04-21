# cs91r

## Project Overview

This project automates ethical reasoning using Carmo and Jones' Dyadic Deontic Logic, Benzmueller and Parent's 
Isabelle framework, and Kant's ethical theory. From a bird's eye view, the strategy is to formalized ethics using 
deontic logic, implement the deontic logic in the Isabelle theorem prover, and use Isabelle's automated reasoning 
tools to prove facts about the logic, thus automating ethical reasoning. The completed version of the project will include
three implemented formalizations of the categorical imperative, a variety of tests evaluating these formalizations, examples
of concrete ethical reasoning performed using these formalizations, and exploration of Kant's thesis that all three of his
formalizations of the categorical imperative are equivalent. All reasoning will be automated using Isabelle and a meta-goal
of the project is to demonstrate the power of automated theorem provers in performing ethical reasoning and helping 
philosophers evaluate ethical theories.

## Quick Links

For fancy rendered output, go to [output/document.pdf](https://github.com/lsingh123/cs91r/blob/main/output/document.pdf)

For a draft of the report I'm writing as part of my CS91r, go to [paper/output/document.pdf](https://github.com/lsingh123/cs91r/blob/main/paper/output/document.pdf)
This report is intended to be accessible to computer scientists with little background in Kantian ethics.

The root directory contains development versions of my Isabelle theories, in files ending in `*.thy`. The directory `paper/` 
contains cleaned up versions of these theories, compiled to produce the report in `paper/output/document.pdf`

## Goals
* Implement DDL ![#c5f015](https://via.placeholder.com/15/c5f015/000000?text=+)
* Test DDL and derive useful theorems ![#c5f015](https://via.placeholder.com/15/c5f015/000000?text=+) 
* Implement the naive formalization ![#c5f015](https://via.placeholder.com/15/c5f015/000000?text=+) 
* Test the naive formalization ![#c5f015](https://via.placeholder.com/15/c5f015/000000?text=+)
* Implement Kroy's formalization of FUL ![#c5f015](https://via.placeholder.com/15/c5f015/000000?text=+) 
    * Include analysis of the differences between Kroy's logic and DDL ![#c5f015](https://via.placeholder.com/15/c5f015/000000?text=+) 
* Test Kroy's formalization of FUL
* Implement Kroy's formalization of FUH
* Test Kroy's formalization of FUH
* Implement my own formalization of the categorical imperative
* Test my own formalization of the categorical imperative
* Write examples of ethical reasoning in Isabelle
    * Figure out what level of model specification is necessary for each formalization
    * Try working with classical ethical dilemmas, like the Nazi example
* Analyze Kant's argument for the equivalence of the three formulations of the categorical imperative 
 
