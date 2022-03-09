(*<*) theory thesis_0_abstract
  imports Main

begin(*>*)

text \<open> AI agents are beginning to make decisions without human supervision in increasingly consequential 
contexts like healthcare, policing, and driving. These decisions are inevitably ethically tinged, 
but most AI agents navigating the world today are not explicitly guided by ethics.
Regulators, philosophers, and computer scientists are raising the alarm about the 
dangers of unethical artificial intelligence, from lethal autonomous weapons to criminal
sentencing algorithms prejudiced against people of color. This is spurring interest in automated ethics, or the development 
of machines that can perform ethical reasoning. Prior work in automated ethics rarely engages with
philosophical literature on ethics, despite its relevance to the development of AI agents that can
responsibly navigate the world. If automated ethics draws on sophisticated philosophical literature, the ethical reasoning
underlying its decisions will be more nuanced, precise, and trustworthy because it will
take advantage of philosophical progress in developing consistent, mature ethical theories. However, 
faithfully translating complex ethical theories from natural language to the rigid syntax of a computer
program poses technical and philosophical challenges. 

In this thesis, I present an implementation of automated Kantian
ethics that is faithful to the Kantian philosophical tradition. Given an appropriately represented 
action and minimal factual background, my system can judge the action as morally obligatory, permissible, or prohibited.
To accomplish this, I formalize Kant's categorical imperative, or moral rule,
in Carmo and Jones's Dyadic Deontic Logic, implement this formalization 
in the Isabelle/HOL theorem prover, and develop a testing framework to evaluate how well 
my implementation coheres with expected properties of Kantian ethics, as established in the literature. 
I also use my system to derive philosophically sophisticated and nuanced solutions to two central ethical 
dilemmas in Kantian ethical literature: the difference
between lying and joking and the example of a murderer knocking on your door asking about the location of their
intended victim. Finally, I examine the philosophical implications of my system, exploring its limitations 
and its potential to help AI agents, academic philosophers, and ordinary human beings better reason about ethics. This work serves 
as an early proof-of-concept for philosophically mature AI agents and is one step towards the development 
of responsible, trustworthy artificial intelligence.
\<close>

(*<*)
end
(*>*)
