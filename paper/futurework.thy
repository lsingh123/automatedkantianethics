(*<*) theory futurework imports Main

begin
(*>*)


section "Future Work"

text \<open>I intend to continue this research for the next year as part of my senior thesis. To make that process
easier, I will sketch some goals for the rest of the project. In Section 3.2, I present a young and unfinished 
implementation of Kroy's formalization of the categorical imperative. The finished version of my project will 
ideally include an implementation of Kroy's formalization of the second formulation of the categorical imperative as well.
I also hope to write robust tests for both of these implementations to explore their limitations. These tests
will help inform my eventual formalization of the categorical imperative.

The ultimate goal of the project is to present my own formalization of the categorical imperative that escapes
the limitations of the naive formalization and Kroy's formalization. This formalization
will likely require some additional logical machinery to handle the complete notion of a maxim, including 
an agent, action, and end. My formalization will also patch up some of the holes in DDL itself that have been
problematic for my project so far, such as the existence of contradictory obligations. I intend to formalize and implement
all three formulations of the categorical imperative.

I will then test my formalization of the categorical imperative. I will create two kinds of tests. First,
I will create metaethical tests that show logical properties independent of any model specification, as I did
for the first two formalizations. Second, I will create tests that specify models and apply my formalization
to real, concrete ethical dilemmas. This part of the project will seek to demonstrate the power and limitations of
automated ethical reasoning. Questions to be explored here include: How much model specification is necessary to 
achieve ethical results? How should models be represented and specified? Does the automation of ethical reasoning
provide anything, or is all the ethical work hidden in the model specification itself? 

This final question is both technical and philosophical, and will be interesting to explore in the written
component of my thesis. This question is related to Kant's distinction between analytic and synthetic reasoning @{cite groundwork}. 
Analytic statements are true simply by virtue of their meaning, such as ``All bachelors are unmarried." Synthetic 
reasoning involves some contribution by the reasoner, in the form of new insight or facts about the world.
Kant presents the statements ``All bachelors are alone" and ``7+5=12" as examples of synthetic propositions. 
The analytic/synthetic distinction is hotly debated and has been refined significantly since Kant, and this 
area will require further research.
 
Kant believes that ethics is synthetic a priori reasoning, but it is unclear if automated theorem provers 
like Isabelle are capable of anything more than analytic reasoning. Many of the basic proof solving 
tools like \texttt{simp} or \texttt{blast} simply unfold definitions and apply axioms, and they appear to 
perform analytic reasoning. SMT solvers like \texttt{Nitpick} and \texttt{z3} (bundled with Isabelle) are 
candidates for synthetic reasoning. Model finding seems more sophisticated than the simple unfolding
of definitions, but this requires further exploration.

Lastly, I hope to explore Kant's argument that the three formulations of the categorical imperative are 
equivalent. This hypothesis has been the subject of controversy, but many neo-Kantians believe that his 
claim is plausible, if not true. Armed with formalizations of each formulation, I will have all the tools 
necessary to test this hypothesis. I would like to either prove or disprove this hypothesis
for my formalization, and analyze the philosophical implications of my result.

\<close>

(*<*)
end
(*>*)