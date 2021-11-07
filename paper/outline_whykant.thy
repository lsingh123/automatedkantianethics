(*<*) theory outline_whykant
  imports paper41 paper224

begin(*>*)

section "Introduction"

text \<open>In this section, I justify my choice to automate Kantian ethics, as opposed to virtue ethics or
consequentialism. Kantian ethics is easy to formalize for three reasons. First, evaluating a maxim requires little 
data about the world. Second, a maxim is relatively easy to represent to a computer. Third, while 
any ethical theory has debates that automated ethics would need to take a stance on, these debates are 
less frequent and less controversial for Kantian ethics. 

I do not argue that consequentialism and virtue ethics are tractable to automate, but 
rather that Kantian ethics is easier. I do not present a comprehensive comparision
of ethical theories, but instead sketch basic principles of consequentialist and virtue 
ethical theories. \<close>

section "Kantian Ethics"

subsection "Kant Crash Course"

text \<open>First, I explain the concepts of 
practical reason, the will, and maxims. I then present Kant's argument that because the will is autonomous,
only the will has authority over itself \cite{sources}. Finally, I argue that a will is definitionally only 
bound by those imperatives that are implied by practical reason itself \cite{velleman}. From there, I present 
the three formulations of the categorical imperative, focusing on the Formula of Universal Law (FUL) \cite{groundwork}. 
\<close>

subsection "Kant is Easy to Formalize"

text \<open>The FUL is easy to formalize because it only evaluates the 
form of the maxim that an agent acts on. No other information is relevant to the test, so moral 
judgement can proceed with a relatively small amount of data.\<close>

subsection "Common Debates"

text \<open>I acknowledge the debates\footnote{I have a separate piece of writing that provides a literature 
review of these debates and justifies my stances. Would that fit here or somewhere else?} in Kantian 
ethics that my project takes a stance on: the correct way to interpret the FUL and the definition of a 
maxim. The stances I take are generally accepted by most Kantians \cite{ebelsduggan, KorsgaardFUL}.\<close>

section "Consequentialism"

subsection "Consequentialism Crash Course"

text \<open>I define a consequentialist theory as one that evaluates the consequences of an action, acknowledging 
that this definition itself is controversial \cite{consequentialismsep}. I then present the debates 
over theories of the good, which consequences to evaluate, and the aggregation of consequences.\<close>

subsection "Consequentialism is Hard to Formalize"

subsubsection "Requires Lots of Data About States of Affairs"

text \<open>Making a consequentialist moral judgement requires data about the entire state of affairs following
an action, posing many challenges. First, collecting this data is difficult. Second, in order to trust 
the system's judgements, we have to trust the ethical theory, its theory of the good, and the many
judgements required to assign each state of affairs a goodness measurement \cite{utilsep}. \<close>

subsubsection "Tradeoff Between Aggregation vs Wholistic Evaluation"

text \<open>Consequentialism also faces the further problem of aggregating goodness across people. 
Consequentialists who abandon aggregation must instead find some wholistic evaluation function
for a state of affairs. There is a tradeoff between the difficulty of aggregation
and the complexity of making judgements about an entire state of affairs, as opposed to about a single person.
\<close>

subsubsection "Prior Work"

text \<open>I briefly survey some prior work in formalizing consequentialism and argue that this work either
implicitly or explicitly takes stances on the debates above, resulting in oversimplification or 
punting the problem \cite{util1, util2}. \<close>

section "Virtue Ethics"

subsection "Virtue Ethics Crash Course"

text \<open>I understand the concept of virtue as those traits that are good for the posessor \cite{vesep}. 
I briefly explain Aristotle's eudaimonistic conception of virtue and present some examples of virtues 
(courage, temperance, equanimity).\<close>

subsection "Virtue Ethics is Hard to Formalize"

subsubsection "What is Virtue?"

text "Automated virtue ethics will need to plant a flag in the messy, controversial debate over the 
exact list of virtues. While most Kantians agree on one interpretation of the FUL, most virtue ethicists 
have their own interpretations of what the virtues are."

subsubsection "Representing Moral Character is Difficult"

text "Automated virtue ethics has to evaluate moral character, which is much more challenging than 
evaluating a maxim. Moral character is a complex concept to precisely represent to a computer."

subsubsection "Prior Work: Machine Learning and Virtue Ethics"

text \<open>One argument for formalizing virtue ethics is the connection between cultivating habit
and machine learning, which learns patterns in datasets. There's been some work using machine learning 
to learn moral behavior from a dataset of actions tagged as ethical, but this approach takes an
implicit stance on the debate above \cite{delphi}. Moreover, machine learning algorithms have trouble
explaining why they made the judgements they made \cite{puiutta}. In contrast, my system can explain 
exactly which axioms resulted in a maxim being obligated and can even present human-reconstructable proofs.
I argue that explanability is particularly important for ethical judgements because these judgements 
are often controversial and high stakes.\footnote{There also seems to be something about Kantian ethics
that requires the will have a reason for adopting a maxim, for otherwise it would cede its autonomy
to the computer. I will flesh this out in a separate section that asks whether it's even a good idea 
to automate ethics.} \<close>

(*<*)
end
(*>*)
