(*<*) theory thesis_1_intro
  imports Main

begin(*>*)

section \<open>Introduction\label{intro}\<close>

text \<open>As AI becomes more sophisticated and less dependent on humans, interest begins to mount
in the development of automated moral agents, or computers that can perform ethical reasoning. 
AI is making decisions in increasingly 
consequential contexts, such as healthcare, driving, and criminal sentencing, and therefore 
must perform ethical reasoning in order to navigate moral dilemmas. For example, self-driving
cars may face less extreme versions of the following moral dilemma: an autonomous vehicle approaching 
an intersection fails to notice pedestrians in the crosswalk until it is too late to brake. The car 
can either continue on its course, running over and killing three pedestrians, or it can swerve to 
hit the car in the next lane, killing the single passenger inside it. While this example is (hopefully) 
not typical of the operation of a self-driving car, every decision that such an AI system makes, from 
avoiding congested freeways to carpooling, is morally tinged. Not only does AI routinely make decisions with 
ethical implications without explicitly performing ethical
reasoning, it often does so without human supervision. For example, the Allegheny Family Screening 
Tool can automatically trigger an investigation into a potential case of child neglect, a decision that 
can uproot entire families and is known to be biased against poor people of color \citep{eubanks}. 
This motivates the need for automated ethics (also called machine ethics), 
or the development of machines that can perform robust, sophisticated ethical reasoning. 

Machine ethicists recognize the need for automated ethics and have made both theoretical 
(\citep{moralmachine}, \citep{davenport}, \citep{moralmachineonline}, \citep{gabriel}) and practical progress 
(\citep{logicprogramming}, \citep{biology}, \citep{winfield}, \citep{delphi}) towards automating ethics. 
However, prior work in machine ethics using popular ethical theories like deontology (\citep{deon1}, \citep{deon2}), 
consequentialism (\citep{util2}, \citep{cloos}, \citep{util1}), and virtue ethics \citep{virtue2} rarely 
engages with philosophical literature and thus often misses philosophers' insights. Even the above example of 
the malfunctioning self-driving car is an instance of Phillipa Foot's trolley problem, 
in which a bystander watching a runaway trolley can pull a lever to kill one instead of three \citep{foot}. 
Decades of philosophical debate have developed ethical theories that can offer nuanced and 
consistent answers to the trolley problem. Like the trolley problem, the moral dilemmas 
that artifical agents face are not entirely new, so solutions to these problems should take advantage of philosophical 
progress. Moral philosophers are devoted to the creation of better ethical theories, so the 
more faithful that automated ethics is to philosophical literature, the more nuanced, precise, consistent, and
therefore trustworthy it will be.

A lack of engagement with prior philosophical literature also makes automated ethics less 
explainable, or interpretable by human observers. One example of this is Delphi, an implementation of automated ethics that uses deep 
learning to make moral judgements based on a training dataset of ethical decisions made by humans \citep{delphi}. 
Early versions of Delphi gave unexpected results, such as declaring that the user should commit 
genocide if it makes everyone happy \citep{verge}. Moreover, because no explicit ethical theory underpins 
Delphi's judgements, human beings cannot analytically determine why Delphi thinks genocide is obligatory
or where its reasoning may have gone wrong. 
Machine learning approaches like Delphi often cannot explain their decisions to a human being, reducing
human trust in a machine's controversial ethical judgements. If a machine prescribes killing one person 
to save three without rigorously justifying this decision, it is difficult to trust this judgement. 
The high stakes of automated ethics require explainability to build trust and catch mistakes, which
motivates philosophically faithful automated ethics.

While automated ethics should draw on philosophical literature, in practice, automating an ethical 
theory is a technical and philosophical challenge. Intuitive computational approaches explored 
previously, such as representing ethics as a constraint satisfaction problem \citep{csp} or reinforcement 
learning algorithm \citep{util1}, fail to capture philosophically plausible ethical theories. For 
example, encoding ethics as a Markov Decision Process assumes that ethical reward can be aggregated 
according to some discounted sum\footnote{Markov Decision Processes usually assume that the total
reward of a system is the discounted sum of the reward at each state, given by $r_i$. Formally, total
reward $R=\sum_0^{\infty}\gamma^ir_i$ for some $\gamma \leq 1$.}, but many philosophers reject 
this notion of aggregation \citep{consequentialismsep}. 
On the other hand, approaches that begin with an ethical theory, instead of a computational method, must contend with the 
fact that ethical theories are almost always described in natural language too
imprecise to represent to a computer. Even once ethics is translated from natural 
language to program syntax, the factual background given to the machine, such as the description of 
an ethical dilemma, plays a great role in the machine's decisions. Another complication
is that philosophers do not agree on a single choice of ethical theory. Even philosophers who
subscribe to a specific ethical theory still debate the theory's 
details.\footnote{I give examples of such debates within Kantian ethics in Sections \ref{whatisamaxim}, 
\ref{praccon}, \ref{joking}, and \ref{murderer}.} Moreover, even once reasoning within a 
particular ethical theory is automated, those who disagree with that theory will disagree with the 
system's judgements.

\medskip 

\noindent \textbf{Contributions}

\medskip 

This thesis presents a proof-of-concept implementation of philosophically faithful automated Kantian ethics. 
I formalize Kant's categorical imperative, or moral rule, as an axiom 
in Dyadic Deontic Logic (DDL), a modal logic designed to reason about 
obligation \citep{CJDDL}. I implement my formalization in Isabelle/HOL, an interactive theorem prover 
that can automatically verify and generate proofs in user-defined logics \citep{isabelle}. Finally, 
I use Isabelle to automatically prove theorems (such as, ``murder is wrong'') in my new logic, 
generating results derived from the categorical imperative. Because my system automates reasoning in 
a logic that represents Kantian ethics, it automates Kantian ethical reasoning. Once equipped with 
minimal factual background, it can classify actions as prohibited, permissible or obligatory. I 
make the following contributions:\<close>

text \<open>
\begin{enumerate}
\item In Section \ref{whykant}, I make a philosophical argument for why Kantian ethics is the most natural of the three major
ethical traditions (deontology, virtue ethics, utilitarianism) to formalize.

\item In Section \ref{implementation31}, I present a formalization of the practical contradiction interpretation of Kant's 
Formula of Universal Law in Dyadic Deontic Logic. I implement this formalization in the Isabelle/HOL
theorem prover. My implementation includes axioms and definitions such that my system, when given an appropriately
represented input, can prove that the input action is permissible, obligatory, or prohibited. It can also return
a list of facts used in the proof and, in some cases, a human readable proof. 

\item In Section \ref{testing}, I present a testing framework that can evaluate how faithful an implementation 
of automated Kantian ethics is to philosophical literature. This testing framework shows that 
my formalization substantially improves on prior attempts to formalize Kantian ethics. 

\item In Sections \ref{joking} and \ref{murderer}, I demonstrate my system's power and flexibility by 
using it to produce nuanced answers to two well-known Kantian ethical dilemmas. I show that, because 
my system draws on interpretations of Kantian ethics presented in philosophical literature, it is able 
to perform sophisticated moral reasoning with minimal factual or situational context. 

\item In Section \ref{computationalethics}, I present ethical insights discovered using my system and argue that
computational methods like the one presented in this thesis can help philosophers resolve debates about ethics.
Not only can my system help machines reason about ethics, but it can also help philosophers make philosophical
progress, just as computational tools unlock discoveries in fields like protein folding and drug discovery.
In Section \ref{ordinarypeople}, I extend this argument to the everyday ethical reasoning that we all
perform as we navigate the world and explore how automated ethics can improve our decision-making. 
\end{enumerate}\<close>

text \<open>
\noindent \textbf{Automated Kantian Ethics: An Overview}

\medskip 

My implementation of automated Kantian ethics formalizes Kant's moral rule
in deontic logic, a modal logic that can express obligation, or morally binding requirements. Most modal 
logics include a necessitation operator, denoted as $\Box$, where
$\Box p$ is true at world $w$ if $p$ is true at all worlds that neighbor $w$ \citep{cresswell}. Intuitively, 
$\Box p$ indicates that $p$ is a necessary truth, like $p$ or $\neg p$. Such 
logics also contain the $\diamond$ operator, which represents possible truths, and operators of 
propositional logic like $\neg, \wedge, \vee, \rightarrow$. Deontic logics
replace $\Box$ with the obligation operator $O$, where $O \, p$ is true at $w$ 
if $p$ is true at all morally perfect versions of $w$ \citep{sep-logic-deontic}. A necessary 
proposition must be true, while an obligatory proposition must be true in order for a world to be morally good.
For example, in order for a world to be morally perfect, if giving to charity is morally obligatory, then
the statement ``Sara gives to charity'' must be true at that world. I use a sophisticated deontic logic 
called Dyadic Deontic Logic, in which the dyadic obligation operator $O\{A \vert B\}$ represents the 
sentence ``A is obligated in the context B.'' This operator expresses the nuanced idea
that certain acts are morally required in certain situations, but not in others.

I automate Kantian ethics because it is the most natural of the major ethical traditions to formalize, as 
I argue in Section \ref{whykant}. 
Kant presents three versions of a single moral rule, known as the categorical imperative, from which 
all moral judgements can be derived. I implement a version of this rule called the Formula of Universal 
Law (FUL), which states that an act is only ethical if it can be performed by all people without contradiction. 
For example, falsely promising to repay a loan is wrong because not everyone can falsely promise to 
repay a loan, since lenders will no longer believe these promises and will stop offering loans. The FUL
prohibits actions that are not ``universalizable,'' or cannot be undertaken by everyone. It formalizes
the kind of objections and prohibitions inspired by the question, ``What if everyone did that?'' Unlike
other ethical traditions, Kantian ethics evaluates actions based on the moral value of the action itself, as opposed to
the value of the action's consequences or the actor's disposition.

Prior work by Benzmüller, Farjami, and Parent \citep{logikey, BFP} implements DDL in Isabelle/HOL, and 
I add the Formula of Universal Law as an axiom on top of their library. The resulting Isabelle theory 
can automatically or semi-automatically generate proofs in a new logic that has the categorical 
imperative as an axiom. Because proofs in this logic are derived from the categorical imperative, 
they judge actions as obligated, prohibited, or permissible. Moreover, because interactive 
theorem provers are designed to be interpretable, my system is explainable. Isabelle can list 
the axioms and facts it uses to generate an ethical judgement, and, in some cases, construct 
human-readable proofs. 

In addition to presenting the above logic and implementation, I also contribute a testing framework 
that evaluates how well my formalization coheres with philosophical literature. I formalize expected 
properties of Kantian ethics as sentences in my logic, such as the property that obligations cannot 
contradict each other. To run the tests, I use Isabelle to automatically find proofs or 
countermodels for the test statements. For example, my implementation passes the contradictory 
obligations test because it is able to prove the sentence $\neg (O\{A|B\} \wedge O\{\neg A | B\})$, 
which says that $A$ and $\neg A$ are not both obligatory. This testing framework shows that my system 
outperforms a control group (raw DDL without any moral axioms added) and 
Moshe Kroy's prior attempt at formalizing Kantian ethics in deontic logic \citep{kroy}.

In Chapter \ref{applications}, I demonstrate my system's power by using it to arrive at sophisticated
solutions to two ethical dilemmas often used in critiques of Kantian ethics. I show that because my system is 
faithful to philosophical literature, it is able to provide nuanced answers to paradoxes that require a
deep understanding of Kantian ethics. While this reasoning does require some factual and situational
context, my system derives mature judgements with relatively little and uncontroversial background.
This indicates that the challenge of automating ``common sense,'' a major hurdle for automated ethics, 
is within closer reach than previously thought. I discuss automated common sense further in
Sections \ref{AIethics} and \ref{amapossible}.

A machine that can evaluate the moral status of an action can not only help machines better reason about ethics, 
but it can also help philosophers better study philosophy. I argue for ``computational ethics,'' or the use of computational tools to 
make philosophical progress, analogous to computational biology. 
I demonstrate the potential of computational ethics by presenting a 
philosophical insight about which kinds of actions are appropriate for ethical consideration that I 
discovered using my system. The process of building and interacting with a computer that can reason 
about ethics helped me, a human philosopher, arrive at a philosophical conclusion that has implications for practical
reason and philosophy of doubt. Thus, my system can be used in three distinct ways. First, my system can help
automated agents navigate the world, which I will refer to as automated ethics or machine ethics interchangeably. Second, 
my system help human philosophers reason about philosophy, which I call computational ethics. Third, as 
I discuss in Section \ref{ordinarypeople}, computational ethics can help not only professional philosophers,
but can also augment the everyday ethical reasoning that we all perform as we navigate the world.
\<close>

(*<*)
end
(*>*)
