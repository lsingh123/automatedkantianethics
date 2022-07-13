# Automated Kantian Ethics

## Project Overview

This project automates ethical reasoning using Carmo and Jones' Dyadic Deontic Logic, Benzmueller, Farjami, and Parent's 
Isabelle framework, and Kant's ethical theory. From a bird's eye view, the strategy is to formalize ethics using 
deontic logic, implement the deontic logic in the Isabelle theorem prover, and use Isabelle's automated reasoning 
tools to prove facts about the logic, thus automating ethical reasoning. The completed version of the project includes
an implemented formalization of the categorical imperative, a variety of tests evaluating these formalizations, and examples
of concrete ethical reasoning performed using these formalizations. All reasoning is automated using Isabelle and a meta-goal
of the project is to demonstrate the power of automated theorem provers in performing ethical reasoning and helping 
philosophers evaluate ethical theories.

## Quick Links

The root directory contains development versions of my Isabelle theories, in files ending in `*.thy`. The directory `paper/` 
contains cleaned up versions of these theories, which can be compiled. The compiled version 
of my senior thesis is [here](https://github.com/lsingh123/cs91r/blob/main/paper/output/Automated_Kantian_Ethics_LS_Thesis.pdf). 
Files beginning in `thesis_` are included in the final draft of my senior thesis. Everything else is developement work.

To get started, check out my recreation of Benzmueller, Farjami, and Parent's [implementation]() of DDL in Isabelle in 
`thesis_2_methods.thy'. Necessarily logical background and my formalization of the FUL are in `thesis_3_methods.thy'. 
In `thesis_4_applications.thy', I present examples of extended ethical reasoning (e.g., teling jokes is permissible) and 
my testing framework.
