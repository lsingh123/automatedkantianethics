(*<*) theory thesis_0_abstract
  imports Main

begin(*>*)

text \<open>AI agents are beginning to make decisions without human supervision in increasingly consequential 
contexts like healthcare, policing, and driving. These decisions are inevitably ethically tinged, 
but most AI agents navigating the world today are not explicitly guided by ethics.
Regulators, philosophers, and computer scientists are raising the alarm about the 
dangers of unethical artificial intelligence, from lethal autonomous weapons to criminal
sentencing algorithms prejudiced against people of color. These warnings are spurring interest in 
automated ethics, or the development of machines that can perform ethical reasoning. Prior work in 
automated ethics rarely engages with philosophical literature, despite its relevance to the 
development of responsible AI agents. If automated ethics draws on sophisticated philosophical
literature, its decisions will be more nuanced, precise, and consistent, but automating ethical theories is 
difficult in practice. Faithfully translating a complex ethical theory from natural language to the 
rigid syntax of a computer program is technically and philosophically challenging.

In this thesis, I present an implementation of automated Kantian
ethics that is faithful to the Kantian philosophical tradition. Given minimal factual background, my 
system can judge an agent's potential action as morally obligatory, permissible, or prohibited.
To accomplish this, I formalize Kant's categorical imperative, or moral rule,
in deontic logic, implement this formalization 
in the Isabelle/HOL theorem prover, and develop a testing framework to evaluate how well 
my implementation coheres with expected properties of Kantian ethics, as established in the literature. 
This testing framework demonstrates that my system outperforms two other potential implementations of 
automated Kantian ethics. I also use my system to derive philosophically sophisticated and nuanced 
solutions to two central controversies in Kantian literature: the permissibility of lying in the 
context of a joke and to a murderer asking about the location of their intended victim. Finally, I 
examine my system's philosophical implications, demonstrating that it can not only guide AI agents, but it can
also help academic philosophers make philosophical progress and augment the everyday ethical reasoning
that we all perform as we navigate the world. I contribute a working proof-of-concept implementation
of automated Kantian ethics capable of performing philosophical reasoning more mature than anything previously
automated. My work serves as one step towards the development of responsible, trustworthy artifical intelligence.
\<close>

(*<*)
end
(*>*)
