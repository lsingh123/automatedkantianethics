(*<*) theory thesis_2_methods
  imports Main

begin(*>*)

section \<open>System Components \label{methods}\<close>

text \<open>My system consists of three components: an ethical theory (Kantian ethics), a logic in which
I formalize this ethical theory (Dyadic Deontic Logic), and an interactive theorem prover in which I 
implement the formalized ethical theory (Isabelle/HOL). In this section, I describe these components, 
present the philosophical, logic, and computational background underlying my system, and explain
the consequences of each of the three choices I make. 

These specific components determine the features
and limitations of my implementation of automated ethics, but other choices of 
components, such as another ethical theory, a different logic, or a different theorem prover could be 
made. Flaws with these components are merely limitations of my system, but do not 
indict logic-programming-based automated ethics more generally. My thesis seeks to 
both present a specific implementation of automated ethics but also to argue for a particular approach 
to automating ethical reasoning and these choices are relevant to the former goal but not to the latter.   \<close>

subsection \<open>Choice to Automate Kantian Ethics \label{whykant}\<close>

text \<open>
In this thesis, I automate Kantian ethics. In 2006, Powers posited that deontological theories are 
attractive candidates for automation because rules are generally computationally tractable \cite[1]{powers}. 
Intuitively, algorithms are rules or procedures for problem solving and Kantian ethics (which is one kind 
of deontological theory) offers one such 
procedure for the problem of making ethical judgements. I will make this intuition precise by
arguing that Kantian ethics is natural to formalize because it prescribes moral rules that require 
little additional data about the world and are easy to represent to a computer. I argue that, compared to 
consequentialism and virtue ethics,\footnote{Technically, virtue ethics and
consequentialism are broad ethical traditions, while Kantian ethics is a specific ethical theory within
the deontological tradition, but``if any philosopher is regarded as central
to deontological moral theories, it is surely Immanuel Kant" \citep{sepdeont}. Out of the three major ethical
traditions, deontology has the most central representative in the form of Kant. Deontology's comparatively 
greater focus on Kant means that my choice of Kant as a guiding figure is less controversial for deontologists 
than, for example, the choice of Bentham as the guiding figure of consequentialism.} Kantian ethics is 
more amenable to automation.

I do not aim to show that Kantian ethics is the only tractable theory to automate or
to present a comprehensive overview of all consequentialist or virtue ethical theories. Instead, I 
present a sample of some approaches in each tradition and argue that deontology is more straightforward 
to formalize than these approaches. Insofar as my project serves 
as an early proof-of-concept, I choose to automate an ethical theory that 
poses fewer challenges than others. All ethical traditions have debates that an 
automated ethical system will need to take a stance on, but these debates are less frequent and controversial
for Kantian ethics than for consequentialism and virtue ethics.

I first present consequentialism, then virtue ethics, and finally Kantian ethics. For each 
tradition, I present a crash course for non-philosophers and then explain some obstacles to automation, 
arguing that these obstacles are weakest in the case of Kantian ethics. 
\<close>

subsubsection "Consequentialism"

text \<open>A consequentialist ethical theory is an ethical theory that evaluates an 
action by evaluating its consequences.\footnote{There is long debate about what exactly makes an ethical theory consequentialist \citep{consequentialismsep}. 
For this thesis, I focus on theories that place the moral worth of an act in its the consequences.} For example, 
utilitarianism is a form of consequentialism in which the moral action 
is the action that produces the most good \citep{utilsep}. The focus
on the consequences of action distinguishes consequentialists from deontologists, who derive the moral worth
of an action from the action itself. Some debates in the consequentialist tradition include 
which consequences matter, what constitutes a ``good" consequence, and how we can 
aggregate the consequences of an action over all the individuals involved. \<close>

text\<open>\noindent \textbf{Which Consequences Matter}\<close>

text \<open>Because consequentialism evaluates the state of affairs following an action, this kind of ethical 
reasoning requires more knowledge about the state of the world than Kantian ethics. Consequentialism
requires knowledge about some or all consequences following an action. This requires that an automated 
ethical system somehow collect a subset of the infinite consquences of following an action, a difficult, 
if not impossible, task. Moreover, compiling this database of consequences requires 
answering difficult questions about which consequences were actually caused \footnote
{David Hume argues that many straightforward accounts of causation face difficulties \citep{hume}, 
and philosophers continue to debate the possiblity of knowing an event's true cause. Kant even argued
that first causes, or noumena, are unknowable by human beings \citep{kantnoumena}.} by an action and
determining the state of the world before and after an action. As acts become
more complex and affect more people, the computational time and space required to calculate and store
their consequences increases. Kantian ethics, on the other hand, does not suffer this scaling
challenge because it evaluates the acts themselves, and acts that affect 1 person and acts that 
affect 1 million people share the same representation.

The challenge of representing the circumstances of action is not unique to consequentialism, but is particularly acute in this case. 
Kantian ethicists robustly debate which circumstances of an action are ``morally relevant'' when evaluating an action's moral worth.\footnote{ 
\citet{powers} identifies this as a challenge for automating Kantian ethics and briefly sketches 
solutions from \citet{constofreason}, \citet{silber}, and \citet{rawlsconstructivism}. For my approach to
morally relevant circumstances, see Section \ref{whatisamaxim}.} Because deontology merely evaluates a 
single action, the surface of this debate is much smaller than debates about circumstances and 
consequences in a consequentialist system. An automated consequentialist system must make such 
judgements about the act itself, the circumstances in which it is performed, and the circumstances 
following the act. All ethical theories relativize their judgements to the situation in which an act 
is performed, but consequentialism requires far more knowledge about the world than Kantian ethics.\<close>


text \<open>\noindent \textbf{Theory of the Good}\<close>

text \<open>An automated consequentialist reasoner must also take a stance on the debate over
what qualifies as a ``good consequence,'' or what the theory of the good is. For example, hedonists associate
good with the presence of pleasure and the absence of pain, while preference utiliarians believe that good is 
the satisfaction of desire. Other consequentialists, like Moore, adopt a pluralistic theory of value, under which 
many different kinds of things are good for different reasons \citep{moorepe}. 

Most theories of the good require that a moral reasoner understand complex features about
individuals' preferences, desires, or sensations in order to evaluate a moral action, making automated
consequentialist ethics difficult. Evaluating a state of affairs requires many controversial
judgements about whether a state of affairs actually satisifes the relevant criteria for goodness. 
Perfect knowledge of tens of thousands of people's pleasure or preferences or welfare or rights is 
difficult, if not impossible.\footnote{Even if it were possible, collecting this kind of data poses 
privacy and surveillance risks.} Either a human being 
assigns values to states of affairs, which doesn't scale, or the machine does, 
which requires massive common-sense and increases room for doubting the system's judgements. This may be 
a tractable problem, but it is much more difficult than the equivalent Kantian task of formulating
and evaluating an action.\<close>

text \<open>\noindent \textbf{Aggregation}\<close>

text \<open>Once an automated consequentialist agent assigns a goodness measurement to each person in a state of affairs, it 
must also calculate an overall goodness measurement for the state of affairs. One approach to assigning
this value is to aggregate each person's individual goodness score into one complete score for a state. 
The more complex the theory of the good, the more difficult this aggregation becomes. For example, 
pluralistic theories struggle to explain how different kinds of value can be compared \citep{consequentialismsep}. 
How do we compare one unit of beauty to one unit of pleasure? Resolving this debate requires that an automated reasoner 
choose one specific aggregation algorithm, but those who disagree with this choice will not trust 
the reasoner's moral judgements. Moreover, for complex theories of the good, this aggregation algorithm
may be complex and may require a lot of data. 

To solve this problem, some consequentialists reject aggregation entirely and instead prefer wholistic
evaluations of a state of affairs. While this approach no longer requires that an 
aggregation algorithm, an automated ethical system still needs to calculate a goodness measurement for a state of 
affairs. Whereas before the system could restrict its analysis to a single person, the algorithm must now 
evaluate an entire state wholistically. As consequentialists modulate between aggregation 
and wholistic evaluation, they face a tradeoff between the difficulty of aggregation and the complexity 
of goodness measurements for large states of affairs.
\<close>

text \<open>\noindent \textbf{Prior Attempts to Formalize Consequentialism}\<close>

text \<open>
Because of its intuitive appeal, computer scientists have tried to formalize consequentialism in the past.
These efforts cannot escape the debates outlined above. For example, Abel et al. represent ethics as a
Markov Decision Process (MDP), with reward functions customized to particular ethical dilemmas 
\citep[3]{util1}. While this is a convenient representation, it either leaves unanswered or 
takes implicit stances on the debates above. It assumes that consequences can be aggregated just as 
reward is accumulated in an MDP.\footnote{Generally, reward for an MDP is accumulated according to a 
``discount factor'' $\gamma < 1$, such that if $r_i$ is the reward at time $i$, the total reward is $\sum_{i=0}^{\infty}\gamma^i r_i$.} 
It leaves open the question of what the reward function is and thus 
leaves the theory of the good, arguably the defining trait of consequentialism, 
undefined. Similarly, Anderson and Anderson's proposal of a hedonistic act 
utilitarian automated reasoner chooses hedonism\footnote{Recall that hedonism views pleasure as good
and pain as bad.} as the theory of the good \citep[2]{util2}. Again, their proposal assumes that pleasure and pain can be 
given numeric values and that these values can be aggregated with a simple sum, taking an implicit
stance on the aggregation question. Other attempts to automate consequentialist ethics will suffer 
similar problems because, at some point, a usable automated consequentialist moral agent will need 
to resolve the above debates. 
\<close>

subsubsection \<open>Virtue Ethics\label{virtueethics}\<close>

text \<open>Virtue ethics places the virtues, or traits that constitute a good moral character and make 
their possessor good, at the center \citep{vesep}. For example, Aristotle describes virtues as the 
traits that enable human flourishing. Just as consequentialists define ``good'' consequences, virtue 
ethicists present a list of virtues, such as the Buddhist virtue of equanimity \citep{mcrae}. An automated virtue 
ethical agent will need to commit to a list and definitions of the virtues, a controversial choice. 
Virtue ethicists robustly debate which traits qualify as virtues, what each virtue actually means, and 
what kinds of feelings or attitudes must accompany virtuous action. 
\<close>

text \<open>Another difficulty with automating virtue ethics is that the unit of evaluation for virtue ethics
is often a person's entire moral character. While Kantians evaluate the act itself, virtue ethicists 
evaluate the actor's moral character and their 
disposition towards the act. If states of affairs
require complex representations, an agent's ethical character and disposition are even more difficult
to represent to a computer. This is more than just a data-collecting problem; it is a conceptual problem 
about the formal nature of moral character.
Formalizing the concept of character appears to require significant philosophical and computational
progress, whereas Kantian ethics immediately presents a formal rule to implement. \<close>

text \<open>\noindent \textbf{Prior Work in Machine Learning and Virtue Ethics}\<close>

text \<open>One potential appeal of virtue ethics is that many virtue ethical theories involve some notion of 
moral habit, which seems to be amenable to a machine learning approach. Artistotle, for example, argued 
that cultivating virtuous action requires making such action habitual through moral education \citep{aristotle}. This
implies that ethical behavior can be learned from some dataset of virtuous acts, such as
those that an ideally virtuous agent would undertake. These 
theories seem to point towards a machine learning approach to automated ethics, in which ethics is 
learned from a dataset of acts tagged as virtuous or not virtuous. 

Just as prior work in consequentialism takes implicit or explicit stances on debates in consequentialist
literature, so does work in machine learning-based virtue ethics. For example, the training 
dataset with acts labelled as virtuous or not virtuous will contain an implicit view on what the virtues
are and how certain acts impact an agent's moral character. Because there is no canonical list of all virtues
that virtue ethicists accept, this implicit view will likely be controversial. Even virtue ethicists agree
that certain traits, like courage, are virtues debate the exact definitions of these traits.

Machine learning approaches like the Delphi system \citep{delphi} mentioned in Chapter \ref{intro} also may suffer explanability 
problems that my logic-programming, theorem-prover
approach does not face. Many machine learning algorithms cannot sufficiently explain their 
decisions to a human being, and often find patterns in datasets that don't 
cohere with the causes that a human being would identify \citep{puiutta}. While there is significant activity 
and progress in explainable machine learning, interactive theorem provers are designed to be explainable 
at the outset. Isabelle can show the axioms and lemmas it used in constructing a proof, 
allowing a human being to reconstruct the proof independently if they wish. This is not an 
intractable problem for machine learning approaches to computational ethics, but is one reason to 
prefer logical approaches.\footnote{This argument about explanability is in the context of virtue ethics and 
machine learning. It also applies to a broader class of work in automated ethics 
that uses a ``bottom-up" approach, in which a system learns moral judgements from prior judgements. 
I will extend this argument to general bottom-up approaches in Section Related Work.}
 \<close>

subsubsection \<open>Kantian Ethics \label{kantianethics}\<close>

text \<open>In this paper I focus on Kantian ethics. Kant's theory is centered 
on practical reason, which is the kind of reason that we 
use to decide what to do and the source of our agency. In \emph{The Groundwork of the Metaphysics of Morals}, Kant explains that 
rational beings are unique because we act ``in accordance with 
the representations of laws'' \citep[4:412]{groundwork}. In contrast, a ball thrown into the air acts 
according to the laws of physics. It cannot ask itself, ``Should I fall back to the ground?'' 
It simply falls. A rational being, on the other hand, can ask, ``Should I act on this reason?"''
As Korsgaard describes it, when choosing which desire to act on, ``it is as if there is something over 
and above all of your desires, something which is you, and which chooses which desire to act on'' \citep[100]{sources}. 
Rational beings are set apart by this reflective capacity. We are purposive and 
our actions are guided by practical reason. We have reasons for acting, even when these reasons are
opaque to us. This reflective choosing, or operation of practical reason, is what Kant calls the will. 

The will operates by adopting, or willing, maxims, which are its perceived reasons for acting. Kant defines a maxim as 
the ``subjective principle of willing,'' or the reason that the will \emph{subjectively} gives 
to itself for acting \citep[16 footnote 1]{groundwork}. Many philosophers agree that a maxim consists 
of some combination of circumstances, 
act, and goal.\footnote{For more discussion of the definition of a maxim, see Section What Is a Maxim}
One example of a maxim is ``When I am hungry, I will eat a doughnut in order to satisfy my sweet tooth.''
When an agent wills this maxim, they decide to act on it. They commit themselves to the end in the maxim 
(e.g. satisfying your sweet tooth). They represent their action, to themselves, as following the 
principle given by this maxim. Because a maxim captures an agent's principle of action, Kant evaluates
maxims as obligatory, prohibited, or permissible. He argues that the form of certain maxims 
requires any rational agent to will them, and these maxims are obligatory. 

The form of an obligatory maxim is given by the categorical imperative. 
An imperative is a command, such as ``Close the door" or ``Eat the doughnut in order to satisfy your 
sweet tooth." An imperative is categorical if it holds unconditionally for all rational agents in all 
circumstances. Kant argues that the moral law must be a categorical imperative \citep[5]{groundwork}. 
In order for an imperative to be categorical, it must be derived from the will's authority over itself. 
Our wills are autonomous, so the only thing that can have unconditional authority over a rational will is 
the will itself. No one else can tell you what to do because you can always ask why you 
should obey their authority. The only authority that you cannot question is the authority of your own 
practical reason. To question this authority is to demand a reason for acting for reasons, which 
concedes the authority of reason itself \citep[23]{velleman}. Therefore, the only possible candidates 
for the categorical imperative are those rules that are required of the will because it is a will. 

Armed with this understanding of practical reason, Kant presents the categorical 
imperative. He presents three ``formulations" or versions of the categorical imperative. In this project, 
I focus on the first formulation, the Formula of Universal Law, and I justify this choice in Section \ref{whyful}.

The Formula of Universal Law (FUL) states, ``act only according to that maxim through which you can 
at the same time will that it become a universal law'' \cite[34]{groundwork}. This formulation
generates the universalizability test, which we can use to test the moral worth of a maxim by 
imagining a world in which it becomes a universal law and attempting to will the maxim in that world.
If there is a contradiction in willing the maxim in a world in which everyone universally wills the maxim,
the maxim is prohibited. 

Velleman presents a concise argument for the FUL. He argues that reason is universally shared among reasoners. For 
example, all reasoners have equal access to the arithmetic logic that shows that ``2+2=4'' \cite[29]{velleman}. The 
reasoning that makes this statement true is not specific to any person, but is universal across people. 
Therefore, if I have sufficient reason to will a maxim, so does every other rational agent. There is 
nothing special about the operation of my practical reason. 
In adopting a maxim, I implicitly state that all reasoners
across time also have reason to adopt that maxim. Therefore, because I act on reasons, I must obey the 
FUL. Notice that this fulfills the above criterion for a categorical imperative: the FUL is derived from 
a property of practical reason itself and thus derives authority from the will's authority over itself.
\<close>

text \<open>\noindent \textbf{Ease of Automation}\<close>

text \<open>Kantian ethics is an especially attractive candidate for formalization because the categorical imperative, particularly the FUL, 
is a property of reason related to the form or structure of a maxim. It does not require any situational 
knowledge beyond the circumstances included
in the maxim itself and thus requires fewer contingent facts than other ethical theories.
While other ethical theories often rely on many facts about 
the world or the actor, a computer evaluating 
a maxim doesn't require any knowledge about the world beyond what is contained in a maxim. Automating 
Kantian ethics merely requires making the notion of a maxim precise and representing it to the computer. 
This distinguishes Kantian ethics from consequentialism and virtue ethics, which
require far more knowledge about the world or the agent to reach a moral decision.

A maxim itself is an object with a thin representation for a computer, as compared to more complex 
objects like states of affairs or moral character. Later in my project, I argue that a maxim can be 
represented simply as a tuple of circumstances, act, and goal.\footnote{For more, see Section \ref{whatisamaxim}.} 
This representation is simple and efficient, especially when compared to the representations of a causal 
chain or a state of affairs or moral character. This property not only reduces the computational complexity
(in terms of time and space) of representing a maxim, but it also makes the system easier for human reasoners
to interact with. A person crafting an input to a Kantian automated agent needs to reason about relatively
simple units of evaluation, as opposed to the more complex features that consequentialism and virtue
ethics require. 
 \<close>

text \<open>\noindent \textbf{Difficulties in Automation}\<close>

text \<open>One challenge for automating Kantian ethics is the need for ``common-sense'', or factual and 
situational background. Common-sense is needed when formulating a maxim and when determining if a maxim 
violates the Formula of Universal Law. Maxims include the circumstances in which they apply and
determining which circumstances are ``morally relevant'' to a maxim requires factual background. 
Many misunderstandings in Kantian ethics are due to badly formulated maxims, so this question is 
important for an ethical reasoner to answer. My system does not need to answer this question because I assume a properly crafted
maxim as input and apply the categorical imperative to this input. Using my system in a fully automated
moral agent will require answering this question, a challenging computational and philosophical task. I
discuss this problem in greater detail in Section \ref{whatisamaxim} and Section \ref{AIethics}. 

Common sense is also relevant when applying the universalizability test itself. Consider the example
maxim ``When broke, I will falsely promise to repay a loan
to get some quick cash.'' This maxim fails the universalizability test because in a world where everyone
falsely promises to repay loans, no one will believe promises anymore, so the maxim will no longer serve
its intended purpose (getting some quick cash). Making this judgement requires understanding enough about
the system of promising to realize that it breaks down if everyone abuses it in this manner. This is a
kind of common sense reasoning that an automated Kantian agent would need. This need is not unique to
Kantian ethics; consequentialists agents need common sense to determine the consequences of 
an action and virtue ethical agents need common sense to determine which virtues an action
reflects. For example, in the case of virtue ethics, in order to see that saving a baby from a lion 
requires courage, a reasoner must have enough background knowledge to know that lions are scary. Making any 
ethical judgement requires robust conceptions of the action at hand. Kantian ethics requires far less common sense 
than a consequentialist or virtue ethical agent.\footnote{
In Sections Lying and Murderer, I also use my system to demonstrate that Kantian ethics requires relatively thin conceptions 
of concepts like falsely promising.} All
moral theories evaluating falsely promising will a robust definition of promising, 
but consequentialism and virtue ethics will require additional information
that Kantian ethics will not. Thus, although the need for common sense poses a challenge to automated
Kantian ethics, this challenge is more acute for consequentialism or virtue ethics. \<close>

subsubsection \<open>The Formula of Universal Law \label{whyful}\<close>

text \<open>
Earlier I mentioned that Kant presents three formulations, or versions, 
of what he calls the ``supreme law of morality," but that I focus on the first of these three. In this section, 
I argue that the Formula of Universal Law, specifically, is the easiest part of Kantian ethics to automate
and the most generalizable.

The first formulation of the categorical imperative is the
formula of universal law (FUL), which reads, ``act only according to that maxim through which you can 
at the same time will that it become a universal law'' \citep[34]{groundwork}. The 
second formulation of the categorical imperative is the formula of humanity (FUH): ``So act that you use humanity, 
in your own person, as well as in the person of any other, always at the same time as an end, never merely 
as a means.'' \cite[41]{groundwork}. This formulation is often understood as requiring us to 
acknowledge and respect the dignity of every other person. The third formulation of the categorical 
imperative is the formula of autonomy (FOA), which Korsgaard describes
as, ``we should so act that we may think of ourselves as legislating universal laws through our 
maxims'' \cite[28]{korsgaardintro}. While closely related to the FUL, the FOA presents morality as the activity of 
perfectly rational agents in an ideal ``kingdom of ends,'' guided by what Kant calls the ``laws of freedom.''

I choose to focus on the FUL\footnote{The FUL is often seen as emblematic of Kantian constructivism \cite[173]{ebelsduggan}. 
My project is not committed to Kantian constructivism.}, because it is the most formal and thus the 
easiest to formalize and implement. Onora O'Neill explains that the formalism of the FUL allows 
for greater precision in philosophical arguments analyzing its implications and power \cite[33]{actingonprinciple}. This precision 
is particularly useful in a computational context because any formalism necessarily makes its content 
precise. The FUL's precision reduces ambiguity, allowing me to remain faithful to philosophical
literature on Kant. Precision reduces the need to make choices to resolve debates 
and ambiguities. Minimizing these choices minimizes 
arbitrariness in my formalization and puts it on solid philosophical footing.

Though Kantians study all formulations of the categorical imperative, Kant argues in \emph{Groundwork} 
that the three formulations of the categorical imperative are equivalent \citep{groundwork}. While this 
argument is disputed \cite{sepkant}, for those who believe it, the
stakes for my choice of the FUL are greatly reduced. If all formulations are equivalent, then a formalization of the FUL
lends the exact same power as a formalization of the second or third formulation of the categorical 
imperative. 

Those who do not believe that all three formulations of the categorical imperative are equivalent
understand the FUL as the strongest or most foundational, and thus an appropriate initial choice for 
formalizations. Korsgaard characterizes the three formulations of the categorical
imperative according to Rawls' general and special conception of justice. The general conception applies
universally and can never be violated, while the special conception represents an ideal for us to
live towards. For example, the special conception may require that we prefer some job applicants
over others in order to remedy historical injustice, and the general conception may require that such
inequalities always operate in the service of the least privileged \citep[19]{KorsgaardRTL}. Korsgaard
argues that the Formula of Universal Law represents Kant's general conception of justice, and the Formula of 
Humanity represents his special conception. The FUL's prescriptions can never be violated, even in the most
non-ideal circumstances imaginable, but the FUH is merely a standard to live towards that might not be 
achieved. Thus, the FUL generates stronger requirements than the other two formulations and reflects 
the bare minimum standard of Kant's ethics. Because the FUL's prescriptions outweigh those of the other two formulations,
automating it creates a functional, minimum ethical theory that can serve as a foundation for implementations
of other aspects of Kant's ethics. \<close>

subsection \<open>Dyadic Deontic Logic \label{ddl}\<close>

text "I formalize Kantian ethics by representing it as an axiom on top of a base logic. In this section, 
I present the logical background necessary to understand my work and my choice of Dyadic Deontic Logic (DDL)."

text \<open>
Traditional modal logics include the necessitation operator, denoted as $\Box$. In simple modal logic
using the Kripke semantics, $\Box p$ is true at a world $w$ if $p$ is true at all of $w$'s neighbors, 
and it represents the concept of necessary truth \citep{cresswell}. 
These logics usually also contain the possibility operator $\diamond$, where
 $\diamond p \iff \sim \Box \sim p$. $\diamond p$ means that the statement $p$ is possibly true, or true
at at least one of $w$'s neighbors. 
Additionally, modal logics include standard operators of propositional logic like $\sim, \wedge, \vee, \rightarrow$.

A deontic logic is a special kind of modal logic designed to reason about moral obligation. Standard deontic
logic replaces $\Box$ with the obligation operator
$O$, and $\diamond$ with the permissibility operator $P$ \citep{cresswell}. Using the Kripke semantics for $O$, $O p$ 
is true at $w$ if $p$ is true at all  ideal deontic alternatives to $w$, and thus represents the 
concept of moral necessity or necessary requirements. The $O$ operator in SDL
takes a single argument (the formula that is obligatory), and is thus called a monadic deontic operator.

 While SDL is appreciable for its simplicity, it suffers a variety of well-documented paradoxes, 
including contrary-to-duty paradoxes. \footnote{The paradigm case of a contrary-to-duty paradox is the 
Chisholm paradox. Consider the following statements: \begin{enumerate}
\item It ought to be that Tom helps his neighbors
\item It ought to be that if Tom helps his neighbors, he tells them he is coming
\item If Tom does not help his neighbors, he ought not tell them that he is coming
\item Tom does not help his neighbors
\end{enumerate} 
These premises contradict themselves, because items (2)-(4) imply that Tom ought not help his neighbors. The 
contradiction results because the logic cannot handle violations of duty mixed with
conditionals. \citep{chisholm, ctd}
} In situations where duty is violated, the logic breaks down 
and produces paradoxical results. Thus, I use an improved deontic logic instead of SDL for this work.\<close>

text \<open>I use as my base logic Carmo and Jones's Dyadic Deontic Logic (DDL), which improves on SDL \citep{CJDDL}. 
It introduces a dyadic obligation operator $O\{A \vert B\}$ 
to represent the sentence ``A is obligated in the context B". The introduction of context allows DDL to
gracefully handle contrary-to-duty conditionals by modifying the context. The obligation operator uses 
a neighborhood semantics, instead of the Kripke semantics \citep{neighborhood1, neighborhood2}. While Kripke
semantics requires that an obligated proposition hold at all worlds, the neighborhood semantics defines
a different set of neighbors, or morally relevant alternatives, for each world. To represent this,
Carmo and Jones define a function $ob$ that maps a given context (or world) to the propositions 
that are obligatory at this world, where a proposition $p$ is defined as 
the worlds at which the $p$ is true. DDL is thus both modal and deontic; statements about obligations are
true or false at a world according to the neighbordhood 
semantics, and different obligations may hold at different worlds. This property is particularly relevant to my work because the universalizability test
requires reasoning about alternative worlds, such as the world of the universalized maxim.

DDL also includes modal operators. In addition to $\Box$ and $\diamond$, DDL also has a notion
of actual obligation and possible obligation, represented by operators $O_a$ and $O_p$ respectively. 
These notions are accompanied by the corresponding modal operators $\Box_a, \diamond_a, \Box_p, \diamond_p$. 
These operators use a Kripke semantics, with the functions $av$ and $pv$ mapping a world $w$ to the set 
of corresponding actual or possible versions of $w$. These operators are not relevant to the work in 
this thesis, but this additional expressivity could be used to extend my project to incorporate 
more sophisticated ethical concepts like counterfactuals.

For more of fine-grained properties of DDL see \citet{CJDDL} or this project's source code. DDL is a heavy logic and contains modal operators 
that aren't necessary for my analysis. While this expressivity is powerful, it may also cause performance
issues. DDL has a large set of axioms involving quantification over complex higher-order
logical expressions. Proofs involving these axioms will be computationally expensive. I do not run 
into performance issues in my system, but future work may choose to embed a less complicated logic.
\<close>

subsection \<open>Isabelle/HOL \label{isabelle}\<close>

text \<open>The final component of my project is the automated theorem prover I use to automate my formalization.
Isabelle/HOL is an interactive proof assistant built on Haskell and Scala \citep{isabelle}. It 
allows the user to define types, functions, definitions, and axiom systems. It has built-in support for both
automatic and interactive/manual theorem proving. To demonstrate the power and usage of Isabelle and 
make DDL more precise, I walk through my \color{red}reimplementation
of Benzmueller, Farjami, and Parent's implementation of DDL in Isabelle/HOL \citep{BFP, logikey}\color{black}. 
\<close>

subsubsection "System Definition"

text \<open>The first step in embedding a logic in Isabelle is defining the relevant terms and types. Commands
to do this include \texttt{typedecl}, which declares a new type, \texttt{type\_synonym}, which defines
an abbreviation for a complex type, and \texttt{consts}, which defines a constant. \<close>

typedecl i \<comment> \<open>This is an Isabelle comment. i is the type for a set of worlds.\<close>
\<comment>\<open>This is a line of actual code used in my implementation. For the rest of the thesis, text typeset 
like this represents Isabelle code.\<close>

type_synonym t = "(i \<Rightarrow> bool)" \<comment> \<open>t represents a set of DDL formulae. \<close>
\<comment> \<open>A set of formulae is defined by its truth value at a set of worlds. For example, the set \{\emph{True}\}
is true at any set of worlds.\<close>

(*<*)
\<comment> \<open> accessibility relations map a set of worlds to: \<close>
consts av::"i \<Rightarrow> t" \<comment> \<open>actual versions of that world set\<close>
  \<comment> \<open>these worlds represent what is "open to the agent"\<close>
  \<comment> \<open>for example, the agent eating pizza or pasta for dinner might constitute two different actual worlds\<close>

consts pv::"i \<Rightarrow> t" \<comment> \<open>possible versions of that world set\<close>
  \<comment> \<open>these worlds represent was was "potentially open to the agent"\<close>
 \<comment> \<open>for example, what someone across the world eats for dinner might constitute a possible world, 
 \<comment> \<open>since the agent has no control over this\<close>\<close>
(*>*)

text \<open>The $ob$ function described in Section \ref{ddl} is used to determine which propositions are obligatory
in which contexts. I implement it as a constant. This constant has no meaning (I merely specify the type), 
but future proofs will specify models for this constant.\<close>

consts ob::"t \<Rightarrow> (t \<Rightarrow> bool)"  \<comment> \<open>set of propositions obligatory in this context\<close>
 \<comment> \<open>$ob\, (context)\, (term)$ is \emph{True} if the term is obligatory in this context\<close>

(*<*)consts cw::i  \<comment> \<open>current world\<close>(*>*)

text \<open>In a semantic embedding, axioms are modelled as restrictions on models of the system. In this case,
a model is specificied by the relevant accessibility relations (such as $ob$), so it suffices to place conditions on 
the accessibility relations. Isabelle allows users to create new axiomatizations on top of its base
logic (HOL) and use these axioms in proofs. Here's an example of an axiom:\<close>

axiomatization where

(*<*)
ax_3a: "\<forall>w.\<exists>x. av(w)(x)" 
 \<comment> \<open>every world has some actual version\<close>

and ax_4a: "\<forall>w x. av(w)(x) \<longrightarrow> pv(w)(x)" 
\<comment> \<open>all actual versions of a world are also possible versions of it\<close>

and ax_4b: "\<forall>w. pv(w)(w)"
\<comment> \<open>every world is a possible version of itself\<close>

and ax_5a: "\<forall>X.\<not>ob(X)(\<lambda>w. False)" 
\<comment> \<open>in any arbitrary context X, something will be obligatory\<close>

and ax_5b: "\<forall>X Y Z. (\<forall>w. ((X(w) \<and> Y(w)) \<longleftrightarrow> (X(w) \<and> Z(w)))) \<longrightarrow> (ob(X)(Y) \<longleftrightarrow> ob(X)(Z))" \<comment> \<open>note that X(w) denotes w is a member of X\<close>
\<comment> \<open>X, Y, and Z are sets of formulas\<close>
\<comment> \<open>If X $\cap$ Y = X $\cap$ Z then the context X obliges Y iff it obliges Z\<close>

\<comment> \<open>ob(X)($\lambda$ w. Fw) can be read as F $\in$ ob(X)\<close>

and ax_5c2: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and> ob(X)(Y) \<and> ob(X)(Z))) \<longrightarrow> ob(X)(\<lambda>w. Y(w) \<and> Z(w))"


and (*>*) ax_5d: "\<forall>X Y Z. ((\<forall>w. Y(w)\<longrightarrow>X(w)) \<and> ob(X)(Y) \<and> (\<forall>w. X(w)\<longrightarrow>Z(w))) 
  \<longrightarrow>ob(Z)(\<lambda>w.(Z(w) \<and> \<not>X(w)) \<or> Y(w))"
\<comment> \<open>If some subset $Y$ of $X$ is obligatory in the context $X$, then in a larger context $Z$,
 any obligatory proposition must either be in $Y$ or in $Z \setminus X$. Intuitively, expanding the context can't 
cause something unobligatory to become obligatory, so the obligation operator is monotonically increasing
with respect to changing contexts.\<close>

(*<*)
and ax_5e: "\<forall>X Y Z. ((\<forall>w. Y(w)\<longrightarrow>X(w)) \<and> ob(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> ob(Y)(Z)"
\<comment> \<open>If Z is obligatory in context X, then Z is obligatory in a subset of X called Y, if Z shares some elements with Y\<close>
(*>*)

subsubsection Syntax

text \<open>The axiomatization above defines the semantics of DDL and, as demonstrated by the example axiom,
is unwieldly. In my work, I mostly perform syntactic proofs, so I must define the syntax of the logic.
Isabelle already knows the semantics of the axioms of this logic, so I can define the syntax as abbreviations for different
formulas involving the axioms above. Each DDL operator is represented
as a HOL formula. Isabelle automatically unfolds formulae defined with the @{verbatim abbreviation} command 
whenever they are applied. While the shallow embedding is performant (because it uses Isabelle's original 
syntax tree), my heavy use of abbreviations may impact the performance of long proofs. \<close>

(*<*)
\<comment> \<open>propositional logic symbols\<close>
abbreviation ddlneg::"t\<Rightarrow>t" ("\<^bold>\<not>") 
  where "\<^bold>\<not>A \<equiv> \<lambda>w. \<not>A(w)" 
abbreviation ddlor::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<or>_") 
  where "A \<^bold>\<or> B \<equiv> \<lambda>w. (A(w) \<or> B(w))"
abbreviation ddland::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<and>_")
  where "A\<^bold>\<and> B \<equiv> \<lambda>w. (A(w) \<and> B(w))"
abbreviation ddlif::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<rightarrow>_")
  where "A\<^bold>\<rightarrow>B \<equiv> (\<lambda>w. A(w)\<longrightarrow>B(w))"
abbreviation ddlequiv::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<equiv>_")
  where "(A\<^bold>\<equiv>B) \<equiv> ((A\<^bold>\<rightarrow>B) \<^bold>\<and> ( B\<^bold>\<rightarrow>A))"
(*>*)

text \<open>Modal operators will be useful for my purposes, implemented below.\<close>
abbreviation ddlbox::"t\<Rightarrow>t" ("\<box>") 
  where "\<box> A \<equiv> \<lambda>w.\<forall>y. A(y)" 
\<comment>\<open>Notice that the necessity operator is an abbreviation, or syntactic sugar for, the higher order
logic formula that the proposition holds at all worlds.\<close>
abbreviation ddldiamond::"t \<Rightarrow> t" ("\<diamond>")
  where "\<diamond>A \<equiv> \<^bold>\<not>(\<box>(\<^bold>\<not>A))"
\<comment>\<open>Possibility is similarly an abbreviation for a higher order logic formula involving the defined semantics.\<close>

text \<open>The most important operator for my project is the obligation operator, implemented below.\<close>
abbreviation ddlob::"t\<Rightarrow>t\<Rightarrow>t" ("O{_|_}")
  where "O{B|A} \<equiv> \<lambda> w. ob(A)(B)"
\<comment> \<open>O$\{B \vert A\}$ can be read as ``B is obligatory in the context A"\<close>

(*<*)
\<comment> \<open>modal symbols over the actual and possible worlds relations\<close>
abbreviation ddlboxa::"t\<Rightarrow>t" ("\<box>\<^sub>a")
  where "\<box>\<^sub>aA \<equiv> \<lambda>x.\<forall>y. (\<not> av(x)(y) \<or> A(y))"
abbreviation ddldiamonda::"t\<Rightarrow>t" ("\<diamond>\<^sub>a")
  where "\<diamond>\<^sub>aA \<equiv> \<^bold>\<not>(\<box>\<^sub>a(\<^bold>\<not>A))"
abbreviation ddlboxp::"t\<Rightarrow>t" ("\<box>\<^sub>p")
  where "\<box>\<^sub>pA \<equiv> \<lambda>x.\<forall>y. (\<not> pv(x)(y) \<or> A(y))"
abbreviation ddldiamondp::"t\<Rightarrow>t" ("\<diamond>\<^sub>p")
  where "\<diamond>\<^sub>pA \<equiv> \<^bold>\<not>(\<box>\<^sub>a(\<^bold>\<not>A))"

\<comment> \<open>obligation symbols over the actual and possible worlds\<close>
abbreviation ddloba::"t\<Rightarrow>t" ("O\<^sub>a")
  where "O\<^sub>a A \<equiv> \<lambda>x. ob(av(x))(A) \<and> (\<exists>y.(av(x)(y) \<and> \<not>A(y)))"
abbreviation ddlobp::"t\<Rightarrow>t" ("O\<^sub>p")
  where "O\<^sub>p A \<equiv> \<lambda>x. ob(pv(x))(A) \<and> (\<exists>y.(pv(x)(y) \<and> \<not>A(y)))"
(*>*)

text \<open>While DDL is powerful because of its support for a dyadic obligation operator, in many cases, 
I only need a monadic obligation operator. Below is some syntactic sugar for a monadic obligation operator.\<close>
abbreviation ddltrue::"t" ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation ddlfalse::"t" ("\<^bold>\<bottom>")
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation ddlob_normal::"t\<Rightarrow>t" ("O {_}")
  where "(O {A}) \<equiv> (O{A|\<^bold>\<top>}) "
\<comment>\<open>Intuitively, the context $True$ is the widest context possible because $True$ holds at all worlds.
Therefore, the monadic obligation operator requires that $A$ is obligated at all worlds.\<close>

text \<open>Finally, validity will be useful when discussing metalogical/ethical properties.\<close>
abbreviation ddlvalid::"t\<Rightarrow>bool" ("\<Turnstile>_")
  where "\<Turnstile>A \<equiv> \<forall>w. A w"
\<comment>\<open>A proposition is valid if it is true at all worlds.\<close>

(*<*)
abbreviation ddlvalidcw::"t\<Rightarrow>bool" ("\<Turnstile>\<^sub>c_")
  where "\<Turnstile>\<^sub>cA \<equiv> A cw"
(*>*)


text \<open>Benemueller, Farjami, and Parent provide a proof of the completeness of the above embedding \citep{BFP}.
Isabelle allows us to check consistency immediately using Nitpick, a model checker \citep{nitpick}.
Nitpick can find satisfying models for a particular lemma using the \texttt{satisfy} option and it can 
find counterexamples using the \texttt{falsify} option, both of which I use heavily in this project. 
\<close>

lemma True nitpick [satisfy,user_axioms,format=2] by simp
\<comment> \<open>This an example of a typical Nitpick output. In this case, Nitpick successfully found a model 
satisfying these axioms so the system is consistent.\<close>
\<comment>\<open> \color{blue} Nitpick found a model for card i = 1:

  Empty assignment \color{black}\<close>

text \<open>In the proof above, {\color{red} by simp} indicates the use of the Simplification proof method, 
which involves unfolding definitions and applying theorems directly. HOL has $True$ as a theorem,
which is why this theorem was so easy to prove.\<close>


(*<*)
end
(*>*)
