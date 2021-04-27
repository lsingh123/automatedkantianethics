(*<*) theory relatedwork imports Main

begin
(*>*)

section "Related Work"

text \<open>In 1685, Leibniz dreamed of a universal calculator that could be used to resolve philosophical 
and theological disputes. At the time, the logical and computational resources necessary to make his 
dream a reality did not exist. Today, automated ethics is a growing field, spurred in part by the need for
ethically intelligent AI agents. 

Tolmeijer et al. @{cite mesurvey} develop a taxonomy of implementation of machine ethics. An implementation is characterized
by (1) the choice of ethical theory, (2) implementation design decisions like testing, and (3) implementation
details like choice of logic.

In this paper, I formalize Kant's ethical theory. There is a long line of work formalizing other 
kinds of ethical theories, like consequentialism \cite{util1, util2} or particularism \cite{particularism1, particularism2}. 
Kantian ethics is a deontological, or rule based ethic, and there is also prior work formalizing deontology \cite{dde, deon1, deon2} more broadly. 
Kantian ethics specifically appears to be an intuitive candidate for formalization. In 2006, 
Powers @{cite powers} argued that a formalization of Kantian ethics presented technical challenges,
 such as automation of a non-monotonic logic, and philosophical challenges, like a definition of the 
categorical imperative. There has also been prior work in formalizing Kantian metaphysics using
 I/O logic @{cite io}. Deontic logic itself is inspired by Kant's ``ought implies can" principle, 
but it does not include a robust formalization of the entire categorical imperative \cite{cresswell}.

Lindner and Bentzen @{cite BL} have presented a formalization of Kant's second formulation of the categorical 
imperative using a custom logic. They present their goal as ``not to get close to a correct interpretation
 of Kant, but to show that our interpretation of Kant’s ideas can contribute to the development of 
machine ethics." My work aims to formalize Kant's ethic as faithfully as possible. I draw on the 
centuries of work in moral philosophy, as opposed to developing my own ethical theory. I also hope to 
formalize the first and third formulation of the categorical imperative as well.

The implementation of this paper builds on Benzmueller, Parent, and Farjami's work 
on the LogiKey framework for machine ethics \cite{BFP, logikey}. The LogiKey project has done a significant 
amount of formalized metaphysics \cite{godel, metaphysics1}. Fuenmayor and Benzmueller @{cite gewirth} have 
formalized Gewirth's principle of generic consistency, which is similar to Kant's formula of universal law.
\<close>


(*<*)
end
(*>*)