(*<*) theory whykant
  imports Main

begin(*>*)

section "Why Kantian Ethics"
text \<open>
In this thesis, I formalize Kantian ethics. Deontological theories are attractive candidates for formalization
because, as Powers argues, rules are generally computationally tractable. Intuitively, algorithms are 
rules or procedures for problem solving and Kantian ethics, particularly the Formula of Universal Law
appears to be one such procedure. While computers are generally successful at applying rules, I will 
argue that Kantian ethics is within reach for automation because of its formalism specifically. Due to 
this formalism, reasoning about Kantian ethics requires far less knowledge of the world than alternative
theories. Like all ethical reasoning, reasoning with Kantian ethics requires some judgements about what 
circumstances and facts are morally relevant, but I argue that it requires fewer such judgements than 
consequentialism or virtue ethics. I will present Kantian ethics and describe its formal nature, then briefly
present consequentialism and virtue ethics and compare their automatability. 

I do not aim to show that Kantian ethics is the only tractable theory to automate, and I do not claim to present a comprehensive
overview of all consequentialist or virtue ethical theories. Instead, I present a sample of some theories
in each tradition and argue that Kantian ethics is more straightforward to formalize than these samples.
Insofar as my project serves as an early proof-of-concept for computational ethics, I choose to automate
the ethical theory that appears most amenable to automation.
\<close>

subsection "Kantian Ethics"

text \<open>First, I present a brief overview of Kantian ethics. Kant's theory is centered on the idea of 
practical reason, which is the kind of reason that we use practically to decide what to do. In \emph{The 
Groundwork of the Metaphysics of Morals}, Kant's most influential text on ethics, he explains that 
rational beings are unique because we can act ``in accordance with the representations of laws" \cite[4:412]{groundwork}.
A ball thrown into the air acts according to the laws of physics and lacks the ability to ask itself, 
``should I fall back to the ground?" It simply falls. A rational being on the other hand, can ask themselves
``Should I act on this reason? Is this a sufficient reason for acting?" As Korsgaard describes it, when 
choosing which desire to act on, ``it is as if there is something over and above all of your desires, 
somethig which is you, and which chooses which desire to act on" \cite[100]{sources}. Rational beings are
set apart by this reflective capacity. In other words, a rational being's behavior is purposive: their 
actions are guided by practical reason. They have reasons for acting, even when these reasons may be 
opaque to them. The operation of this practical reason is called the will. 

The will operates by willing maxims, which are its percieved reasons for acting. Kant defines a maxim as 
the ``subjective principle of willing," which is the reason that the will \emph{subjectively} gives 
to itself for acting \cite[16, footnote 1]{groundwork}. There is debate about what exactly must be 
included in a maxim, but most philosophers agree that a maxim consists of some combination of circumstances, 
act, and goal\footnote{For more discussion of the definition of a maxim, see Section What Is a Maxim?}.
One example of a maxim is ``When I am hungry, I will eat a doughnut in order to satisfy my sweet tooth." 
When a moral agent wills this maxim, they decide to act on it. They commit themselves to the end in the maxim, 
satisfying your sweet tooth in this case. They represent their action, to themselves, as following the 
principle given by this maxim. It is maxims that Kant evaluates as obligatory or prohibited. He argues that
certain maxims have a form or logical structure that requires any rational agent to will them. 

The form of an obligatory maxim is given by the categorical imperative, Kant's supreme rule of morality. 
An imperative is a command, such as ``Close the door" or "Eat the doughnut in order to satisfy your 
sweet tooth." A categorical imperative holds unconditionally for all rational agents under all 
circumstances. Kant argues that the moral law must be a categorical imperative, for otherwise it would 
not have the force that makes it a moral law \cite[5]{groundwork}. In order for an imperative to be 
categorical, it must be derived from the will's authority over itself. Our wills are free and bound to 
nothing but themselves. The only thing that can have unconditional authority over a rational will is 
the rational will itself. No one can tell me what reasons to act on because I can always ask why I 
should obey their authority. The only authority that I cannot question is the authority of my own 
practica reason. To question this authority is to demand a reason for acting for reasons, which 
concedes the authority of reason itself \cite[23]{velleman}. Therefore, the only possible candidates 
for the categorical imperative are those rules that are required of the will because it is a will. 
The categorical imperative must be a property of practical reason itself.

Armed with this understanding of practical reason, we can now examine what Kant claims is the categorical 
imperative. He presents three ``formulations" or versions of the categorical imperative and goes on to 
argue that all three formulations are equivalent. In this project, I focus on the first formulation,
the Formula of Universal Law, but will briefly present the other two as well. 

The first formulation of the categorical imperative is the
formula of universal law (FUL), which reads, ``act only according to that maxim through which you can 
at the same time will that it become a universal law." $\cite[34]{groundwork}$ This formulation
generates the universalizability test, which ``tests" the moral value of a maxim by 
imagining a world in which it becomes a universal law and attempting to will the maxim in that world.
Velleman presents a concise argument for the FUL. He argues that reason is shared among reasoners. For 
example, all reasoners have equal access to the arithmetic logic that shows that ``2+2=4"\cite[29]{velleman}. The chain of 
reasoning that makes this statement true is not specific to any person, but is universal across people. 
Therefore, if I have sufficient reasont to will a maxim, so will every other rational agent. There is 
nothing special about the operation of my practical reason that other reasoners don't have access to. 
Practical reason is by its very nature shared, so in adopting a maxim, I implicitly state that all reasoners
across time also have reason to adopt that maxim. Therefore, because I act on reasons, I must obey the 
FUL. Notice that this fulfilles the above criterion for a categorical imperative: the FUL is derived from 
a property of practical reason itself and thus derives authority from the will's authority over itself, 
as opposed to some external authority.

The second formulation of the categorical imperative is the formula of humanity (FUH): ``So act that you use humanity, 
in your own person, as well as in the person of any other, always at the same time as an end, never merely 
as a means." $\cite[41]{groundwork}$. This formulation is often understood as requiring us to 
acknowledge and respect the dignity of every other person. The third formulation of the categorical 
imperative is the formula of autonomy (FOA), which Korsgaard summarizes in her introduction to the Groundwork 
as, ``we should so act that we may think of ourselves as legislating universal laws through our 
maxims." $\cite[28]{korsgaardintro}$ While closely related to the FUL, the FOA presents morality as the activity of 
perfectly rational agents in an ideal ``kingdom of ends," guided by what Kant calls the ``laws of freedom."

The above is not meant to serve as a full defense of Kant's ethical theory, as that is outside the scope
of this thesis. Instead, I aim to briefly reconstruct an argument for Kant's ethical theory in the hopes 
of offering context for the implementation of the FUL I present later in the thesis. Additionally, understanding 
the structure of Kant's argument also reveals facts about his theory that make it an ideal candidate 
for formalization.

Kant argues that the categorical imperative, and the FUL in particular, is a formal principle of practical
reason. In other words, the FUL is a property of reason related to the form or structure of a maxim.
It has nothing to do with the circumstances of behavior (beyond those included in a maxim), the agent's
mental state, or any other contingent facts. Instead, it is purely a property of a proposed principle for
action. This formalism makes Kantian ethics an attractive candidate for formalization. While other 
ethical theories often rely on many facts about the world or the actor, Kantian ethics simply relies 
on the form of a given maxim. A computer evaluating a maxim doesn't require any knowledge about the 
world beyond what is contained in a maxim. A maxim is essentially a thin representation of all the knowledge
that a computer needs in order to make a moral judgement. Automating Kantian ethics merely requires 
making the notion of a maxim precise and representing it to the computer. This distinguishes Kantian 
ethics from utilitarianism and virtue ethics, which, as I will argue below, require far more knowledge
about the world or the agent to reach a moral decision.
 \<close>

subsection "Consequentialism"

text \<open>A consequentialist ethical theory is, broadly speaking, any ethical theory that evaluates an action by evaluating 
its consequences\footnote{There is long debate about what exactly makes an ethical theory consequentialist \cite{consequentialismsep}. 
For this paper, I will focus on theories that place the moral worth of an act in its the consequences.}. For example, 
utilitarianism is a form of consequentialism in which the moral action 
is the action that results in the best consequences or produces the most good \cite{utilsep}. Different 
consequentialists take different stances on what exactly constitutes a ``good" consequence and how 
we can aggregate or calculate the goodness of a state of affairs. For example, hedonists define 
a good action as one that produces pleasure, and the most good action as the one that produces that most
pleasure or avoids the most pain. 
Unlike consequentialists, Kantians derive the moral worth of an action
from the maxim that is acted on. This maxim is the actor's subjective reason for acting, determined 
at the time of action, not as a later consequence.

Because consequentialism evaluates the state of affairs following an action, this kind of  ethical 
reasoning requires more knowledge
about the state of the world than Kantian ethics. Under a naive version of consequentialism, evaluating 
an action requires perfect knowledge of all consequences following an action. Not only does this require 
a lot of knowledge that the implementor of an automated ethical system likely does not have, it also 
requires answering difficult questions about which consequences were actually caused by an action\footnote
{maybe cite the debate about difficulties in determining causation?}. Most consequentialists do not actually
think that agents need to calculate all the consequences of their actions; plausible consequentialist strategies include stopping 
calculation early because constant calculation paralyzes action and is clearly not a desirable state of affairs,
only evaluating consequences that the agent could reasonably forsee before acting, or the legal notion 
of ``proximate cause," in which the agent is only responsible for the immediate consequences of their 
acts but not of consequences resulting from others' voluntary acts prompted by the agent's original act \cite{consequentialismsep}.
The details of these views are not important for my project, but it is clear that they require far 
more data than Kantian ethics. Even if we cut off the chain of causal reasoning at some point, evaluating 
the consequences of an action is still data-intensive. Even evaluating the first or immediate cause of an
action requires immense knowledge about the state of the world and how it changes. Kantian ethics, on the 
other hand, requires only knowledge about the maxim, not knowledge about the state of the world when 
the maxim is adopted. Consequentialism requires knowledge about the situation in which the act is 
performed and following the act, whereas Kantian ethics merely requires knowledge about the act itself.

The fact that consequentialism requires more knowledge about the world makes it more difficult to formalize.
Automated consequentialist ethics would need to represent complex states of the world and causal chains
in an efficient manner and reason about them. This presents a difficult technical challenge and
impedes the usability of such a system. Automated consequentialist ethics would need to come equipped with 
a large enough database of knowledge about the world to extrapolate the consequences of an actions and
up-to-date information about the state of the world at the moment of action. Not only does collecting 
and representing this data pose a technical challenge, it also creates a larger ``trusted code base" for 
the automated system. Trusting a Kantian ethical reasoner merely requires trusting the logical implementation
of the categorical imperative, but trusting a consequentialist ethical reasoner requires trusting both the
logical machinery that actually evaluates the consequences of an act and the background/situational
knowledge that serves as an input to this machinery. There is much more room for debate about 
the background knowledge/state of the world than there is about the act that the agent performs.
The Kantian ethical reasoner includes room for 
disagreement about the formulation of the maxim being evaluated\footnote{For more on the parsing 
of ethical dilemmas into maxims, see Section AI Ethics}, but the surface of this debate is much smaller
than the surface of an entire database about actions and their consequences. 

Another such debate that an automated consequentialist reasoner would need to take a stance on is 
the question of what qualifies as a ``good consequence." Simple hedonists associate
good with the presence of pleasure and the lack of pain. Preference utiliarians believe that good is 
the satisfaction of desires and is thus related to individuals' preferences, as opposed to some objective
sensation of pleasure or pain. Other consequentialists adopt a pluralistic theory of value, under which 
many different kinds of things are good for different reasons. For example, Moore values beauty and truth 
and other pluralists value justice, love, and freedom (cite). Welfare utilitarians value a person's 
welfare and utilitarians of right value states of affairs in which respect for some set of crucial
rights is maximized \cite{consequentialismsep}.

Most of the above theories of good require that a moral reasoner understand complex features about
individuals' preferences, desires, or sensations in order to evaluate a moral action, making automated
consequentialist ethics difficult. Regardless of the theory of the good, a consequentialist ethical 
reasoner needs to evaluate a state of affairs, which may encompass each involved individual's pleasure, 
preferences, welfare, freedom, rights, or whatever other criteria make a state good. This not only requires
a lot of data as I argued above, it also requires judgements about whether or not a state of affairs 
actually satisifes the relevant criteria for goodness. These judgements are difficult and debateable, 
and any consequentialist decision requires many of these judgements for each individual involved. As 
systems become more complex and involve more people and more acts, making these judgements quickly becomes
difficult, posing a scaling challenge for a consequentialist ethical reasoner. Perfect knowledge of 
tens of thousands of people's pleasure or preferences or welfare or rights is impossible. Either a human being 
assigns values to states of affairs, which quickly becomes difficult to scale, or the machine does, 
which requires massive knowledge and increases room for doubting the system's judgements.

Once an automated consequentialist agent assigns a goodness measurement to each person in a state of affairs, it 
must also calculate an overall goodness measurement for this state of affairs. One approach to assigning
this value is to aggregate each person's individual goodness score into one complete score for a state. 
For example, under a simple welfare model, each person may be assigned a welfare score and the total 
score for a state of affairs may be the sum of the welfare scores for each involved person.
The more complex the theory of the good, the more difficult that aggregation becomes. For example, 
pluralistic theories struggle to explain how different kinds of value can be compared. How do we compare
one unit of beauty to one unit of pleasure? Subjective theories of the good, such as those focused on 
the sensation of pleasure or an individual's preferences, present difficulties in comparing such 
subjective measures. Resolving this debate requires that the automated reasoner make a decision about
one specific aggregation algorithm, but those who disagree with this choice will not trust the reasoner's
moral judgements. 

On the other hand, some consequentialists reject aggregation entirely and instead prefer wholistic
evaluations of a state of affairs. While this approach no longer requires that a reasoner define an 
aggregation algorithm, the reasoner still needs to calculate a goodness measurement for a state of 
affairs. Whereas before the reasoner could restrict analysis to a single person, the algorithm must now 
evaluate an entire state at once, wholistically. Evaluating the goodness of an entire state of affairs is more complicated
than evaluating the goodness of a single person. As consequentialists modulate between aggregation 
and wholistic evaluation, they face a tradeoff between the difficulty of aggregation and the complexity 
of goodness measurements for large units like states of affairs. This tradeoff translates to an automated
consequentialist moral agent. Such an agent either needs to define an aggregation function, thus opening 
the door to those who disagree with this definition, or needs to evaluate the goodness of entire states
of affairs, which is a complex and data-intensive philosophical and technical challenge.

None of the challenges described above are intractable or capture the full literature of 
all variations of consequentialism. I do not argue that consequentialism is 
impossible to automate. Instead, each of the challenges above either makes an automated consequentialist
agent more complex or requires that the developer ``plant certain flags" and take a stance on philosophical
debates. Such points of difficulty also appear in Kantian ethics, and I deal with them throughout this
project (see Section What is a Maxim). These difficulties are present in any ethical theory, but consequentialism
has more points of difficulty than Kantian ethics and is thus more difficult to formalize both computationally
and philosophically. Given that this project is a proof-of-concept and an early attempt to formalize
a philosophically rigorous ethical theory, I choose Kantian ethics because it is the easier theory to 
formalize. Future work could indeed address the challenges above and formalize consequentialism. The more
ethical theories that comptuational tools can handle, the more valuable computational philosophy becomes 
for philosophers and AI agents. My project contributes a formalization of one theory that poses fewer
challenges than others.
\<close>

subsection "Virtue Ethics"

text \<open>The virtue ethical tradition predates even consequentialism and has countless variations. Below
I explain the centrality of virtue and practical wisdom, two common tenets of most virtue ethical theories.

All virtue ethical theories place virtue, or those traits that constitute a good moral character, 
at the center. Virtue ethicists recommend actions based on the character traits that such actions
would help cultivate. A virtue is commonly accepted as a character trait that "makes its possessor
good" \cite{vesep}. For example, under Aristotlean virtue ethics, the virtues are the traits that 
enable human flourishing, or fulfilling the purpose of a human being. Many modern virtue ethicists abandon
Aristotle's notion of a ``purpose" of human beings, and instead define virtue in terms of the characteristic
activity of human beings (in ethical terms, not telelological terms) (cite from gened paper). Just as 
consequentialists must offer a view of which consequences are good, virtue ethicists must offer some 
theory of the virtues which justifies and presents a list of the virtues. Such theories are varied in
the literature, from the classical virtues of courage and temperance to the Buddhist virtue of 
equanimity to Sen's conception of the virtues as capabilites that serve as ``effective opportunities to 
undertake the actions and activities" an agent wants to engage in. An automated virtue ethical agent 
will need to commit to a particular theory of the virtues, opening itself up to criticism from those
who disagree with this theory of the virtues. Unlike Kantian ethics, who generally agree on the meaning of
the FUL, virtue ethicists robustly debate which character traits qualify as virtues.  

Another difficulty with automating virtue ethics is that the unit of evaluation for a virtue ethical
theory is often a person's entire character. While Kantians evaluate the maxim of an act and utilitarians
evaluate the consequences of an act, virtue ethicists evaluate the actor's moral character and their 
disposition towards the act. Virtues are character traits and evaluating an action as virtuous or 
not requires understanding the agent's character and disposition while acting. If states of affairs
require complex representations, an agent's ethical character and disposition is even more difficult
to represent. Consequentialism posed a data-collection problem in evaluating and representing states
of affairs, but virtue ethics poses a conceptual problem about the formal nature of moral character.
Formalizing the concept of character appears to require significant philosophical and computational
progress, whereas Kantian ethics automatically presents a formal rule to implement. Precise representations
of consequences is a central debate in consequentialism, but precise representation of moral character
is not a central debate in virtue ethics. 

One potential appeal of virtue ethics is that many virtue ethical theories involve some form of 
moral education. Artistotle, for example, argued that cultivating virtuous action requires making such
action habitual through moral education. Under the simple, popular view of virtue ethics, the virtuous
act is what the virtuous person would do. Both of these theories imply that ethical behavior can be
learned from some dataset of virtuous behavior, either those prescribed by a moral teacher or those that
a virtuous ideal agent would undertake. Indeed, these theories seem to point towards a machine learning
model for computational ethics, in which ethics is learned from a dataset of acts tagged as ethical
or not ethical. Such approaches exist in the literature and there is a solid body of work attempting 
to learn ethics from past judgements. My project present a different, top-down approach starting 
with an ethical theory and representing it in a logic. Both approaches have their merits, but one 
advantage of my logical approach is that it does not suffer many of the explainability problems that machine learning 
approaches may experience. Many machine learning algorithms cannot sufficiently explain their decisions
to a human being, and often find patterns or correlations in datasets that don't actually cohere with 
the trends and causes that a human being would identify. While there is significant activity and progress
in explainable machine learning, interactive theorem provers are designed to be explainable at the outset.
Indeed, Isabelle can even give the axioms and lemmas it used in constructing a proof, allowing a human 
being to reconstruct the proof independently if they wish. This is, again, not an intractable problem 
for machine learning approaches to computational ethics, but is one reason to prefer logical approaches.

Explainability matters more for ethics.
 \<close>


end
(*>*)
