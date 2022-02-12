(*<*) theory thesis_0_abstract
  imports Main

begin(*>*)

text \<open> AI agents are beginning to make decisions without human supervision in increasingly consequential 
contexts like healthcare, policing, and driving. These decisions are inevitably ethically tinged, 
but most AI agents navigating the world today are not explicitly guided by ethics.
Warnings from regulators, philosophers, and computer scientists about the 
dangers of unethical artificial intelligence, from science-fiction killer robots to criminal
sentencing algorithms prejudiced against people of color, have spurred interest in automated ethics, or the development 
of machines that can perform ethical reasoning. Much prior work in automated ethics approaches the 
problem from a computational perspective and rarely engages with philosophical literature on ethics, despite
its clear relevance to the development of AI agents that can
responsibly navigate the world. All decisions are moral decisions, including those that AI agents are actively 
making today. If automated ethics draws on sophisticated philosophical literature, the ethical reasoning
underlying such decisions will be more nuanced, precise, consistent, and trustworthy. However, faithfully translating complex ethical theories
from natural language to the rigid syntax of a computer program poses technical and philosophical 
challenges. 

In this thesis, I present an implementation of automated Kantian
ethics that is faithful to the Kantian philosophical tradition. Of the three major ethical
traditions, Kant's categorical imperative is the most natural to formalize because it is an inviolable 
formal rule that requires less context than other ethical theories. I formalize Kant's categorical imperative 
in Carmo and Jones's Dyadic Deontic Logic, implement this formalization 
in the Isabelle/HOL theorem prover, and develop a testing framework to evaluate how well 
my implementation coheres with expected properties of Kantian ethics, as established in the literature. 
I also use my system to reason about two ethical dilemmas used to criticize Kantian ethics: the difference
between lying and joking and the example of a murderer knocking on your door asking about the location of their
intended victim. Finally, I examine the philosophical implications of this system, exploring its limitations 
and its potential to help both AI agents and human beings better reason about ethics. 

Armed with relatively uncontroversial facts about the world, my system is able to correctly
resolve complex moral dilemmas because it is grounded in philosophical literature.
Moreover, because I automate an explicit ethical theory, the ethical reasoning underlying my system's judgements
is interpretable by a human being. I implement this ethical theory using the Isabelle/HOL interactive theorem prover, which can 
list the axioms and theorems used in a proof, so my system is explainable. This work serves as an early 
proof-of-concept for philosophically mature AI agents and is one step towards the development of 
responsible, trustworthy artificial intelligence.
\<close>

(*<*)
end
(*>*)
