(*<*) theory thesis_0_abstract
  imports "paper41"

begin(*>*)

text \<open> AI agents are beginning to make decisions without human supervision in increasingly consequential 
contexts like healthcare, policing, and driving. These decisions are inevitably ethically tinged, 
but most AI agents navigating the world today have no notion of ethics.
Warnings from regulators, philosophers, and computer scientists about the 
dangers of unethical artificial intelligence, from science-fiction killer robots to criminal
sentencing algorithms prejudiced against people of color, have spurred interest automated ethics, or the development 
of machines that can perform ethical reasoning. Previous work in automated ethics rarely
engages with existing philosophical literature. Given that ethics is the study of how to navigate the world,
automated ethics should look to philosophical literature to guide the development of AI agents that can
responsibly navigate the world. All decisions are moral decisions, including the ones that AI agents are actively 
making today. Automated ethics that draws on sophisticated philosophical literature makes the ethical reasoning
underlying such decisions nuanced, precise and reliable, but faithfully translating complex ethical theories
from natural language to the rigid syntax of a computer program poses technical and philosophical 
challenges. 

In this thesis, I present an implementation of automated Kantian
ethics that is faithful to the Kantian philosophical tradition. Of the three major ethical
traditions, Kant's categorical imperative is the most natural to formalize because it is an inviolable 
formal rule that requires less context than other ethical theories. I formalize Kant's categorical imperative 
in Carmo and Jones's Dyadic Deontic Logic, implement this formalization 
in the Isabelle/HOL theorem prover, and develop a testing framework to evaluate how well 
my implementation coheres with expected properties of Kantian ethics, as established in the literature. 
I also use my system to reason about two ethical dilemmas used to criticize Kantian ethics: the case of 
joking and the example of a murderer knocking on someone's door asking about the location of their
intended victim. Armed with relatively uncontroversial facts about the world, my system correctly 
resolves these moral dilemmas.

My system is able to resolve complex ethical dilemmas because it is grounded in philosophical literature.
Moreover, because I automate an explicit ethical theory, the ethical reasoning underlying my system's judgements
is interpretable by a human being. I implement this ethical theory using the Isabelle/HOL interactive theorem prover, which can 
list the axioms and theorems used in a proof, so my system is explainable. This work serves as an early 
proof-of-concept for philosophically mature AI agents and is one step towards the development of 
responsible, trustworthy artificial intelligence.
\<close>

(*<*)
end
(*>*)
