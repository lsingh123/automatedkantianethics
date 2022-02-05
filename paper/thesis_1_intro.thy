(*<*) theory thesis_1_intro
  imports "paper41"

begin(*>*)

section "Introduction"

text \<open> As AI agents become more sophisticated and less dependent on humans, interest begins to mount
in the development of computers that can perform ethical reasoning, also known as automated moral agents. 
AI agents are making decisions in increasingly 
consequential contexts, such as healthcare, driving, and criminal sentencing, and therefore 
must perform ethical reasoning in order to navigate moral dilemmas. For example, self-driving
cars may face less extreme versions of the following moral dilemma: an autonomous vehicle approaching 
an intersection fails to notice pedestrians in the crosswalk until it is too late to brake. The car 
can either continue on its course, running over and killing three pedestrians, or it can swerve to 
hit the car in the next lane, killing the single passenger inside it. While this example is (hopefully) 
not typical of the operation of a self-driving car, every decision that such an AI agent makes, from 
avoiding congested freeways to carpooling, is morally tinged. AI agents routinely make decisions with 
ethical implications without explicitly performing ethical
reasoning and, in many cases, without human supervision. For example, the Alleghany Family Screening 
tool can automatically trigger an investigation into a potential case of child neglect, a decision that 
can uproot entire families and is known to be biased against poor people of color \citep{eubanks}. 
Not only are machines making moral decisions without actually performing ethical reasoning, they're 
doing so without human involvement. This motivates the need for machine ethics (also called automated ethics), 
or the study of how to develop machines that can perform robust, sophisticated ethical reasoning. 

Machine ethicists recognize the need for automated ethics and have made both theoretical 
(\citep{moralmachineonline}, \citep{davenport}, \citep{moralmachine}, \citep{gabriel}) and practical progress 
(\citep{logicprogramming}, \citep{biology}, \citep{delphi}, \citep{winfield}) towards automating ethics. 
However, prior work in machine ethics using popular ethical theories like deontology (\citep{deon2}, \citep{deon1}), 
consequentialism (\citep{util1}, \citep{util2}, \citep{cloos}), and virtue ethics \citep{berberich} rarely 
engages with philosophical literature and thus misses philosophers' insights. Even the above example of 
the malfunctioning self-driving car is an instance of Phillipa Foot's trolley problem, 
in which a bystander watching a runaway trolley can pull a lever to kill one instead of three \citep{foot}. 
Decades of philosophical debate have developed ethical theories that can offer nuanced and 
consistent answers to the trolley problem. The trolley problem demonstrates that the moral dilemmas 
that artifical agents face are not entirely new, so solutions to these problems should take advantage of philosophical 
progress. The more faithful that automated ethics is to philosophical literature, the more reliable and 
nuanced it will be.

A lack of engagement with prior philosophical literature also makes automated moral agents less 
explainable, or interpretable by human observers. One example of this is Delphi, a language model that uses deep 
learning to make moral judgements based on a training dataset of ethical decisions made by humans \citep{delphi}. 
Early versions of Delphi gave unexpected results, such as declaring that the user should commit 
genocide if it makes everyone happy \citep{verge}. Moreover, because no explicit ethical theory underpins 
Delphi's judgements, human beings cannot analytically determine why Delphi thinks genocide is obligatory
or where its reasoning may have gone wrong. 
Machine learning approaches like Delphi often cannot explain their decisions to a human being and, 
in the extreme case, are black box algorithms. This reduces human trust in a machine's controversial 
ethical judgements. If a machine prescribes killing one person to save three without justifying this 
decision, it is difficult to trust this judgement enough to act on it or endorse a machine acting on it. 
The high stakes of automated ethics require explainability to build trust and catch mistakes. 

While automated ethics should draw on philosophical literature, in practice, automating an ethical 
theory is a technical and philosophical challenge. Intuitive computational approaches explored 
previously, such as representing ethics as a constraint satisfaction problem \citep{csp} or reinforcement 
learning algorithm \citep{util1}, fail to capture philosophically plausible ethical theories. For 
example, encoding ethics as a Markov Decision Process assumes that ethical reward can be aggregated 
according to some discounted sum, but many philosophers reject this notion of aggregation \citep{consequentialismsep}. 
Approaches that begin with an ethical theory, instead of a computational tool, must contend with the 
fact that ethical theories are almost always described in natural language and must be made
precise enough to represent to a computer. Even once ethics is translated from natural 
language to program syntax, the factual background given to the machine, such as the description of 
an ethical dilemma, is equally as important in determining the machine's decisions. Another complication
is that philosophers do not agree that on a single choice of ethical theory. Even philosophers who
agree that a specific ethical theory, like Kantian ethics, is true, debate the theory's 
details.\footnote{For examples of these debates in the case of Kantian ethics, see Section Joking
and Section Murderer.} Even once reasoning within a 
particular ethical theory is automated, those who disagree with that theory will disagree with the 
system's judgements.

This thesis presents a proof-of-concept implementation of philosophically faithful automated Kantian ethics. 
I formalize Kant's categorical imperative, or moral rule, as an axiom 
in Carmo and Jones' Dyadic Deontic Logic (DDL), a modal logic designed to reason about 
obligation \citep{CJDDL}. I implement my formalization in Isabelle/HOL, an interactive theorem prover 
that can automatically verify and generate proofs in user-defined logics \citep{isabelle}. Finally, 
I use Isabelle to automatically prove theorems (such as, ``murder is wrong'') in my new logic, 
generating results derived from the categorical imperative. Because my system automates reasoning in 
a logic that represents Kantian ethics, it automates Kantian ethical reasoning. Once equipped with 
minimal factual background, it can classify actions as prohibited, permissible or obligatory. I 
make the following contributions:\<close>

text \<open>
\begin{enumerate}
\item In Section ??, I make a philosophical argument for why Kantian ethics is the most natural of the three major
ethical traditions (deontology, virtue ethics, utilitarianism) to formalize.

\item In Section ??, I present a formalization of the practical contradiction interpretation of Kant's 
Formula of Universal Law in Dyadic Deontic Logic. I implement this formalization in the Isabelle/HOL
theorem prover. My implementation includes axioms and definitions such that my system, when given an appropriately
represented input, can prove that the input is permissible, obligatory, or prohibited. It can also return
a list of facts used in the proof and, in some cases, an Isar-style human readable proof. 

\item In Sections ?? and ??, I demonstrate my system's power and flexibility by 
using it to produce nuanced answers to two well-known Kantian ethical dilemmas. I show that, because 
my system draws on definitions of Kantian ethics presented in philosophical literature, it is able 
to perform sophisticated moral reasoning. 

\item In Section ??, I present a testing framework that can evaluate how faithful an implementation 
of automated Kantian ethics is. My framework includes meta-ethical tests and application tests inspired by philosophical
literature. This testing framework shows that my formalization substantially improves on prior work and can 
be generalized to evaluate any implementation of automated Kantian ethics.

\item In Section ??, I present new ethical insights discovered using my system and argue that
computational methods like the one presented in this paper can help philosophers address ethical problems.
Not only can my system help machines reason about ethics, but it can also help philosophers make philosophical
progress.
\end{enumerate}\<close>

text \<open>

I choose to formalize Kant's moral rule in Carmo and Jones' Dyadic Deontic Logic (DDL) \citep{CJDDL}. Deontic 
logic is a modal logic that can express obligation, or morally binding requirements. Traditional modal 
logics include the necessitation operator, denoted as $\Box$. In modal logic using the Kripke semantics, 
$\Box p$ is true at world $w$ if $p$ is true at all worlds that neighbor $w$ \citep{cresswell}. Modal 
logics  also contain the possibility operator $\diamond$, where $\diamond \, p \iff \neg (\Box (\neg p))$ 
and operators of propositional logic like $\neg, \wedge, \vee, \rightarrow$. I use DDL, in which
the dyadic obligation operator $O\{A \vert B\}$ represents the sentence ``A is obligated in the context B.'' 
The introduction of context allows DDL to express more nuanced reasoning. DDL is both deontic and modal, 
so sentences like $O\{A \vert B\}$ are terms that can be true or false at a world. For example, the 
sentence $O \{ \text{steal} \vert \text{when rich}\}$ is true at a world if stealing when rich is 
obligated at that particular world. 

I automate Kantian ethics because it is the most natural to formalize, as I argue in Section WhyKant. 
Kant presents three versions of a single moral rule, known as the categorical imperative, from which 
all moral judgements can be derived. I implement a version of this rule called the Formula of Universal 
Law (FUL), which states that people should only act on those principles that can be acted on by all 
people without contradiction. For example, in a world where everyone falsely promises to repay a loan, 
lenders will no longer believe these promises and will stop offering loans. Therefore, not everyone 
can simultaneously falsely promise to repay a loan, so the FUL thus prohibits this act.

Prior work by Benzmüller, Farjami, and Parent \citep{logikey, BFP} implements DDL in Isabelle/HOL and 
I add the Formula of Universal Law as an axiom on top of their library. The resulting Isabelle theory 
can automatically or semi-automatically generate proofs in a new logic that has the categorical 
imperative as an axiom. Because proofs in this logic are derived from the categorical imperative, 
they judge actions as obligated, prohibited, or permissible. Moreover, because interactive 
theorem provers are designed to be interpretable, my system is explainable. Isabelle can list 
the axioms and facts it used to generate an ethical judgement, and, in some cases, construct 
human-readable proofs. In Sections Joking and Murderer, I use my system to arrive at 
sophisticated solutions to two ethical dilemmas often used in critiques of Kantian ethics. Because 
my system is faithful to philosophical literature, it is able to provide nuanced answers to these paradoxes. 

In addition to presenting the above logic and implementation, I also contribute a testing framework 
that evaluates how well my formalization coheres with philosophical literature. I formalize expected 
properties of Kantian ethics as sentences in my logic, such as the property that obligations cannot 
contradict each other. I represent each of these properties as a sentence in my logic that my system 
should be able to prove or refute. I run the tests by using Isabelle to automatically find proofs or 
countermodels for the test statements. For example, my implementation passes the contradictory 
obligations test because it is able to prove the sentence $\neg (O\{A|B\} \wedge O\{\neg A | B\})$. 
I find that my system outperforms the control group of raw DDL, without any moral axioms added, and 
Moshe Kroy's prior attempt at formalizing Kantian ethics in deontic logic \citep{kroy}.

As it stands, my implementation can evaluate the moral status of sentences represented in my logic. 
Given an appropriate input, my project returns a value indicating if the action is obligatory 
(its negation violates the FUL), permissible (consistent with the FUL), or prohibited (violates the FUL) 
by proving or refuting a theorem in my logic. 

A machine that can evaluate the moral status of a maxim can not only help machines better reason about ethics, 
but it can also help philosophers 
better study philosophy. I argue for ``computational ethics," or the use of computational tools to 
make philosophical progress. I demonstrate the potential of computational ethics by presenting a 
philosophical insight about which kinds of maxims are appropriate for ethical consideration that I 
discovered using my system. The process of building and interacting with a computer that can reason 
about ethics helped me, a human philosopher, arrive at a philosophical conclusion that has implications for practical
reason and philosophy of doubt. Thus, my system can be used in two distinct ways. First, to help
automated agents navigate the world, which I will refer to as automated ethics or machine ethics interchangeably. Second, 
to help human philosophers reason about philosophy, which I call computational ethics.
\<close>

(*<*)
end
(*>*)
