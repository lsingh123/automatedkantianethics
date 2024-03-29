(*<*) theory whykant
  imports Main

begin(*>*)

subsection "Choice of Ethical Theory"

text \<open>
In this thesis, I automate Kantian ethics. In 2006, Powers posited that deontological theories are 
attractive candidates for automation because rules are generally computationally tractable \cite[1]{powers}. 
Intuitively, algorithms are rules or procedures for problem solving and deontology offers one such 
procedure for the problem of making ethical judgements. I will make this intuition precise by
arguing that deontological ethics is natural to formalize because rules generally require little additional
data about the world and are usually easy to represent to a computer. All ethical traditions have debates that an 
automated ethical system will need to take a stance on, but these debates are less frequent and controversial
for deontological ethics than for consequentialism and virtue ethics.

I do not aim to show that deontology is the only tractable theory to automate or
to present a comprehensive overview of all consequentialist or virtue ethical theories. Instead, I 
present a sample of some approaches in each tradition and argue that deontology is more straightforward 
to formalize than these approaches. Future work could and should address the challenges I outline in 
this section. The more ethical theories that computational tools can handle, the more valuable 
computational philosophy becomes both for philosophers and for AI agents. Insofar as my project serves 
as an early proof-of-concept for computational ethics, I choose to automate an ethical theory that 
poses fewer challenges than others.

I first present deontological ethics, then consequentialism, and finally virtue ethics. For each 
tradition, I present a crash course for non-philosophers and then explain some obstacles to automation, 
arguing that these obstacles are weakest in the case of deontology. Finally, I will present the specific 
deontological theory I am automating (Kantian ethics) and will argue that it is comparatively easier
to formalize. I will also outline the specific debates in the literature that my formalization takes
a stance on and potential challenges for formalizing deontology.
\<close>

subsubsection "Deontological Ethics"

text \<open>\textbf{Crash Course on Deontology}\<close>

text \<open>Deontological ethical theories evaluate actions as permissible, obligatory, or prohibited. The 
deontological tradition argues that an action should not be judged on its consequences, 
but rather on ``its confirmity with a moral norm" \citep{sepdeont}. In other words, deontological theories
define a set of moral norms or rules and evaluate actions based on their confirmity or lackthereof to
these rules. Deontologists do not believe that an agent should maximize the number of times that they 
conform to such rules; rather they argue that an agent should never violate any of the moral laws. A wrong
choice is wrong, regardless of its consequences. \<close>

text \<open>\textbf{Formalizing Deontology}\<close>

text \<open>Deontology is immediately an attractive candidate for formalization because computers tend to 
understand rules; programming languages are designed to teach computers algorithms. Deontological
ethical theories give inviolable rules that an automated agent can apply, without having to adjust
the rules in changing situations or contexts. Moreover, because deontological theories focus on
the action itself, they require relatively little data. A deontological moral judgement does not require
as much information about context, consequences, or moral character as the other theories presented later in this
section. All that matters is the action and some limited set of circumstances in which it is performed.
I will later argue that, in the case of the specific deontological ethic that I implement (Kantian ethics), 
the action has a very ``thin" representation that is space and memory efficient and requires little data
about the external world. 

Like all ethical traditions, deontology has debates that any implementation of automated deontological
ethics would need to resolve. Deontologists disagree about whether ethics should focus on agents and 
prescribe them action or should focus on the patients or potential victims of actions and their rights.
 Different deontological theories have different conceptions of what an action is, 
from the actual physical act to the agent's mental state at the time of acting to the principle upon
which the agent acted. 

While these debates are certainly open, ``if any philosopher is regarded as central
to deontological moral theories, it is surely Immanuel Kant" \citep{sepdeont}. Out of the three ethical
traditions considered in this section, deontology has the most central representative in the form of 
Kant. Many modern deontologists claim to interpret Kant in a particular way, and thus agree on 
his ethic as the foundation of their theory but disagree in how to interpret it. In this paper, I will 
formalize Kantian ethics. Deontology's comparatively greater focus on Kant means that the choice of 
Kant as a guiding figure will be less controversial to deontologists than, for example, the choice of Bentham
as the guiding figure of consequentialism. Moreover, at the end of this section, I also argue that 
internal debates in the part of Kantian ethics that I focus on tend to be less controversial than those
in the consequentialist or virtue ethical traditions.

I do not argue that deontology is the only tractable theory to formalize, but instead that it is 
easier to formalize because it requires less data, is easily representable to a computer, and has fewer
and less controversial open debates than consequentialism or virtue ethics. That being said, any ethical
tradition has debates that an automated agent will need to take a stance on and deontological ethics
is no exception. Those who disagree with my stances (e.g. non-Kantians) will not trust my system's
judgements. This project is not irrelevant for them because it still serves as a case study in 
the power of computational ethics, but Kantians will trust my system's moral judgements the most. \<close>


subsubsection "Consequentialism"

text \<open>A consequentialist ethical theory is, broadly speaking, any ethical theory that evaluates an action by evaluating 
its consequences.\footnote{There is long debate about what exactly makes an ethical theory consequentialist \citep{consequentialismsep}. 
For this paper, I will focus on theories that place the moral worth of an act in its the consequences.} For example, 
utilitarianism is a form of consequentialism in which the moral action 
is the action that results in the best consequences or produces the most good \citep{utilsep}. The focus
on the consequences of action distinguishes consequentialists from deontologists, who derive the moral worth
of an action from the action itself. Some debates in the consequentialist tradition include 
which consequences of an action matter, what exactly constitutes a ``good" consequence, and how we can 
aggregate the consequences of an action over all the individuals involved. \<close>

text\<open>\textbf{Which Consequences Matter}\<close>

text \<open>Because consequentialism evaluates the state of affairs following an action, this kind of ethical 
reasoning requires more knowledge
about the state of the world than deontology. Under a naive version of consequentialism, evaluating 
an action requires perfect knowledge of all consequences following an action. This requires that an 
automated ethical system somehow collect all of the infinite consquences following an action, a 
difficult, if not impossible, task. Moreover, compiling this database of consequences requires 
answering difficult questions about which consequences were actually caused by an action.\footnote
{maybe cite the debate about difficulties in determining causation?}

These challenges also apply to human reasoners, so most consequentialists do not actually adopt the naive
view that agents need to calculate all the consequences of their actions. Plausible strategies to avoid 
this problem include stopping calculation early because constant calculation paralyzes action or only 
evaluating consequences that the agent could reasonably forsee before acting. Another solution is the 
``proximate cause" approach, which only holds the agent responsible for the immediate consequences of their 
acts, but not for consequences resulting from others' voluntary responses to the agent's original act \citep{consequentialismsep}.

Even without understanding the details of these views, it is clear that they require 
more data than deontology and scale poorly with the complexity of the act being evaluated. Even 
if we cut off the chain of causal reasoning at some point based on 
one of the rules above, evaluating the consequences of an action is still data-intensive. Even evaluating
the first or immediate cause of an action requires knowledge about the state of the world before
and after an action, in addition to knowledge about the action itself. Consequentialism requires 
knowledge about 
the situation in which the act is performed and following the act, whereas deontology mostly requires 
knowledge about the act itself. For simple acts, collecting this data may not seem unreasonable, but as acts become
more complex and affect more people, the computational time and space required to calculate and store
their consequences increases. Collecting this data is theoretically possible, but is labor and resource
intensive. Deontology, on the other hand, does not suffer this scaling
challenge because acts that affect 1 person and acts that affect 1 million people share the same
representation.

The fact that consequentialism requires more knowledge about the world makes it more difficult to formalize.
Automated consequentialist ethical systems would need to represent complex states of the world and causal chains
in an efficient manner and reason about them. This both presents a difficult technical challenge and
impedes the usability of such a system. Such a system would need to come equipped with 
a large enough database of knowledge about the world to extrapolate the consequences of an actions and
up-to-date information about the state of the world at the moment of action. Not only does collecting 
and representing this data pose a technical challenge, it also creates a larger ``trusted code base" for 
the automated system. Trusting my deontological ethical reasoner merely requires trusting the logical implementation
of the categorical imperative and the formulation of a maxim. Trusting a consequentialist ethical 
reasoner, on the other hand, requires trusting both the logical machinery that actually evaluates the act and the 
background/situational knowledge that serves as an input to this machinery.

The challenge of understanding and representing the circumstances of action is not unique to consequentialism,
but is particularly acute for consequentialism. Deontologists robustly debate which circumstances 
of an action are ``morally relevant" and should be included in the formulation of the action.\footnote{ 
\cite{powers} identifies this as a challenge for automating Kantian ethics and briefly sketches 
solutions from \citet{constofreason}, \citet{silber}, and \citet{rawlsconstructivism}. }
Those using my system will need to use common-sense reasoning to determine which aspects of the circumstances
in which the action is performed are morally relevant and should thus be represented to the computer.\footnote{For more on the challenge of 
parsing of ethical dilemmas into maxims, see Section AI Ethics.} However, because deontology
merely evaluates the action itself, the surface of this debate is much smaller
than the debate about circumstances and consequences in a consequentialist system. An automated 
consequentialist system must make judgements about the act itself, the circumstances in which 
it is performed, and the circumstances following the act. The ``trusted code base" is 
smaller for deontology than for consequentialism. All ethical theories will require some set of 
circumstances and common-sense knowledge as part of the trusted code base, but this set is larger for 
consequentialism than for deontology.\<close>


text \<open>\textbf{Theory of the Good}\<close>

text \<open>Another debate that an automated consequentialist reasoner would need to take a stance on is
the question of what qualifies as a ``good consequence," or what the theory of the good is. Hedonists associate
good with the presence of pleasure and the absence of pain. Preference utiliarians believe that good is 
the satisfaction of desires and is thus derived from individuals' preferences, as opposed to some
sensation of pleasure or pain. Other consequentialists adopt a pluralistic theory of value, under which 
many different kinds of things are good for different reasons. For example, Moore values beauty and truth 
and other pluralists value justice, love, and freedom \citep{moorepe}. Welfare utilitarians value a person's 
welfare and utilitarians of right value states of affairs in which respect for some set of
rights is maximized \citep{consequentialismsep}.

Most of the above theories of good require that a moral reasoner understand complex features about
individuals' preferences, desires, or sensations in order to evaluate a moral action, making automated
consequentialist ethics difficult. Regardless of the theory of the good, a consequentialist ethical 
reasoner needs to evaluate a state of affairs, which encompass each involved individual's pleasure, 
preferences, welfare, freedom, rights, or whatever other criteria make a state good. This requires
judgements about whether or not a state of affairs actually satisifes the relevant criteria for goodness. 
These judgements are difficult and debateable, and any consequentialist decision requires many of 
these judgements for each individual involved. As systems become more complex and involve more people and 
more acts, making these judgements quickly becomes difficult, posing a scaling challenge for a 
consequentialist ethical reasoner. Perfect knowledge of tens of thousands of people's pleasure or 
preferences or welfare or rights is impossible. Either a human being 
assigns values to states of affairs, which quickly becomes difficult to scale, or the machine does, 
which requires massive common-sense, increases room for doubting the system's judgements, and simplifies
the judgements. This is a tractable problem, but it is much more difficult than the deontological task of formulating
and evaluating an action.\<close>

text \<open>\textbf{Aggregation}\<close>

text \<open>Once an automated consequentialist agent assigns a goodness measurement to each person in a state of affairs, it 
must also calculate an overall goodness measurement for the state of affairs. One approach to assigning
this value is to aggregate each person's individual goodness score into one complete score for a state. 
For example, under a simple welfare model, each person is assigned a welfare score and the total 
score for a state of affairs is the sum of the welfare scores for each involved person.
The more complex the theory of the good, the more difficult this aggregation becomes. For example, 
pluralistic theories struggle to explain how different kinds of value can be compared \citep{consequentialismsep}. 
How do we compare one unit of beauty to one unit of pleasure? Subjective theories of the good, such 
as those focused on the sensation of pleasure or an individual's preferences, present difficulties in 
comparing different people's subjective measures. Resolving this debate requires that the automated reasoner 
choose one specific aggregation algorithm, but those who disagree with this choice will not trust 
the reasoner's moral judgements. Moreover, for complex theories of the good, this aggregation algorithm
may be complex and may require a lot of data. 

To solve this problem, some consequentialists reject aggregation entirely and instead prefer wholistic
evaluations of a state of affairs. While this approach no longer requires that a reasoner define an 
aggregation algorithm, the reasoner still needs to calculate a goodness measurement for a state of 
affairs. Whereas before the reasoner could restrict analysis to a single person, the algorithm must now 
evaluate an entire state wholistically. Evaluating the goodness of an entire state of affairs is more complicated
than evaluating the goodness of a single person. As consequentialists modulate between aggregation 
and wholistic evaluation, they face a tradeoff between the difficulty of aggregation and the complexity 
of goodness measurements for large states of affairs. This tradeoff also holds for an automated
consequentialist moral agent. Such an agent either needs to define an aggregation function, thus opening 
the door to critique from those who disagree with this definition, or needs to evaluate the goodness of entire states
of affairs, which is a complex and data-intensive philosophical and technical challenge.
\<close>

text \<open>\textbf{Prior Attempts to Formalize Consequentialism}\<close>

text \<open>None of the challenges described above are intractable or capture the full literature of 
all variations of consequentialism. Instead, the challenges above require that the developer 
``plant certain flags" and take a stance on certain philosophical debates. Such debates are present in 
any ethical theory, but consequentialism has more such points of difficulty than deontology and 
is thus more difficult to automate. 

Because of its intuitive appeal, computer scientists have tried to formalize consequentialism in the past.
These efforts cannot escape the debates outlined above. For example, Abel et al. represent ethics as a
Markov Decision Process (MDP), with reward functions customized to particular ethical dilemmas 
\citep[3]{util1}. While this is a convenient representation, it either leaves unanswered or 
takes implicit stances on the debates above. It assumes that consequences can be aggregated just as 
reward is accumulated in an MDP.\footnote{Generally, reward for an MDP is accumulated according to a 
``discount factor" $\gamma < 1$, such that if $r_i$ is the reward at time $i$, the total reward is $\sum_{i=0}^{\infty}\gamma^i r_i$.} 
It leaves open the question of what the reward function is and thus 
leaves the theory of the good, arguably the defining trait of a particular consequentialist view, 
undefined. Similarly, Anderson and Anderson's proposal of a hedonistic act 
utilitarian automated reasoner chooses hedonism\footnote{Recall that hedonism views pleasure as good
and pain as bad.} as the theory of the good \citep[2]{util2}. Again, their proposal assumes that pleasure and pain can be 
given numeric values and that these values can be aggregated with a simple sum, taking an implicit
stance on the aggregation question. Other attempts to automate consequentialist ethics will suffer 
similar problems because, at some point, a useful automated consequentialist moral agent will need 
to resolve the above debates. 
\<close>

subsubsection "Virtue Ethics"

text \<open>\textbf{What Is Virtue}\<close>

text \<open>The virtue ethical tradition places the virtues, or those traits that constitute a 
good moral character, at the center. Virtue ethicists evaluate actions based on the character traits 
that such actions would help cultivate. A virtue is commonly accepted as a character trait that 
``makes its possessor good" \citep{vesep}. For example, under Aristotlean virtue ethics, virtues 
are the traits that enable human flourishing or fulfill the purpose of a human being. Many modern 
virtue ethicists abandon Aristotle's notion of a ``purpose" of human beings, and instead define virtue 
in terms of the characteristic activity of human beings (in ethical terms, not telelological terms) \citep{snow}. 
Just as consequentialists must offer a view of which consequences are good, virtue ethicists must offer some 
theory of the virtues which presents and justifies a list of the virtues. Such theories vary
from Aristotle's virtues of courage and temperance to the Buddhist virtue of 
equanimity \citep{aristotle, mcrae}. Another theory is Sen's conception of the virtues as capabilites that create
``effective opportunities to undertake the actions and activities" an agent wants to engage in \citep{robeyns}. 
An automated virtue ethical agent will need to commit to a particular theory of the virtues, opening 
itself up to criticism from those who disagree with this theory of the virtues. Any automated virtue
ethical agent will need to justify its choice of virtues. 
\<close>

text \<open>\textbf{Evaluating Moral Character}\<close>

text \<open>Another difficulty with automating virtue ethics is that the unit of evaluation for a virtue ethical
theory is often a person's entire moral character. While deontologists evaluate the act itself and utilitarians
evaluate the consequences of an act, virtue ethicists evaluate the actor's moral character and their 
disposition towards the act. Virtues are character traits and evaluating an action as virtuous or 
not requires understanding the agent's character and disposition while acting. If states of affairs
require complex representations, an agent's ethical character and disposition are even more difficult
to represent to a computer. Consequentialism posed a data-collection problem in evaluating and representing states
of affairs, but virtue ethics poses a conceptual problem about the formal nature of moral character.
Formalizing the concept of character appears to require significant philosophical and computational
progress, whereas deontology immediately presents a formal rule to implement. \<close>

text \<open>\textbf{Machine Learning and Virtue Ethics}\<close>

text \<open>One potential appeal of virtue ethics is that many virtue ethical theories involve some form of 
moral habit, which seems to be amenable to a machine learning approach. Artistotle, for example, argued 
that cultivating virtuous action requires making such action habitual through moral education \citep{aristotle}. Under 
one view of virtue ethics, the virtuous act is what the virtuous person would do. Both of these ideas
imply that ethical behavior can be learned from some dataset of virtuous acts, either those 
prescribed by a moral teacher or those that a virtuous ideal agent would undertake. Indeed, these 
theories seem to point towards a machine learning approach to computational ethics, in which ethics is 
learned from a dataset of acts tagged as virtuous or not virtuous. 

Just as prior work in consequentialism takes implicit or explicit stances on debates in consequentialist
literature, so does work in machine learning-based virtue ethics. For example, the training 
dataset with acts labelled as virtuous or not virtuous will contain an implicit view on what the virtues
are and how certain acts impact an agent's moral character. Because there is no canonical list of virtues
that virtue ethicists accept, this implicit view will likely be controversial.

Machine learning approaches also may suffer explanability problems that my logical, theorem-prover
based approach does not experience. Many machine learning algorithms cannot sufficiently explain their 
decisions to a human being, and often find patterns or correlations in datasets that don't actually 
cohere with the trends and causes that a human being would identify \citep{puiutta}. While there is significant activity 
and progress in explainable machine learning, interactive theorem provers are designed to be explainable 
at the outset. Indeed, Isabelle can show the axioms and lemmas it used in constructing a proof, 
allowing a human being to reconstruct the proof independently if they wish. This is not an 
intractable problem for machine learning approaches to computational ethics, but is one reason to 
prefer logical approaches.

Explanability is particularly important in the case of ethics because ethical judgements are often 
controversial and ethics generally requires reflection. Often, the most interesting and important
ethical judgements result from ethical dilemmas. These judgements are usually controversial 
because people's intuitions differ and different theories generate different answers. In these cases,
explainability is particularly important to convince human beings of the correctness of an ethical 
judgement. If a machine tells us to kill one person to save five without justifying this decision, 
acting on this judgement becomes difficult. Second, ethics is a reflective subject. Practical reason 
is the exercise of using reason to decide what to do. Someone who believes an automated reasoner's 
judgements without examining or understanding the reasons for these judgements doesn't seem to be 
doing ethics correctly.\footnote{I make this argument precise in Section Is CE Even Good For Us?} 
This does not preclude other uses of automated ethics, such as automated moral agents or hypothesis 
generation for philosophy, but it does make computer-assisted ethical judgement difficult. 

My arguments about theories of virtues and explanability are in the context of virtue ethics and 
machine learning. Such arguments also apply to a broader class of projects in automated ethics 
that use ``bottom-up" approaches, in which a system learns moral judgements from prior judgements, as 
opposed to a top-down ethical theory. I will extend this argument to bottom-up approaches more
generally in Section Related Work.
 \<close>

subsubsection "Kantian Ethics"

text \<open>As mentioned above, in this paper I focus on Kantian ethics, a specific branch of deontology. 
Kant is widely seen as the most popular representative of deontology, so this choice is not surprising. 
In this section, I will present a crash course on Kant's ethical theory and then explain why his particular
theory is more amenable to formalization than consequentialist or virtue ethical theories.\<close>

text \<open>\textbf{Crash Course on Kantian Ethics}\<close>

text \<open>Kant's theory is centered on practical reason, which is the kind of reason that we 
use to decide what to do. In \emph{The Groundwork of the Metaphysics of Morals}, Kant's most influential 
text on ethics, he explains that rational beings are unique because we can act ``in accordance with 
the representations of laws" \cite[4:412]{groundwork}. In contrast, a ball thrown into the air acts 
according to the laws of physics. It cannot ask itself, ``Should I fall back to the ground?" 
It simply falls. A rational being, on the other hand, can ask, ``Should I act on this reason?" 
As Korsgaard describes it, when choosing which desire to act on, ``it is as if there is something over 
and above all of your desires, something which is you, and which chooses which desire to act on" \cite[100]{sources}. 
Rational beings are set apart by this reflective capacity. A rational being's behavior is purposive and 
their actions are guided by practical reason. They have reasons for acting, even when these reasons may be 
opaque to them. This operation of practical reason is what Kant calls the will. 

The will operates by adopting, or willing, maxims, which are its perceived reasons for acting. Kant defines a maxim as 
the ``subjective principle of willing," or the reason that the will \emph{subjectively} gives 
to itself for acting \cite[16 footnote 1]{groundwork}. There is debate about what exactly must be 
included in a maxim, but many philosophers agree that a maxim consists of some combination of circumstances, 
act, and goal.\footnote{For more discussion of the definition of a maxim, see Section What Is a Maxim}
One example of a maxim is ``when I am hungry, I will eat a doughnut in order to satisfy my sweet tooth." 
When an agent wills this maxim, they decide to act on it. They commit themselves to the end in the maxim 
(e.g. satisfying your sweet tooth). They represent their action, to themselves, as following the 
principle given by this maxim. Because a maxim captures an agent's principle of action, Kant evaluates
maxims as obligatory, prohibited, or permissible. He argues that certain maxims have a form or logical structure 
that requires any rational agent to will them, and these maxims are obligatory. 

The form of an obligatory maxim is given by the categorical imperative. 
An imperative is a command, such as ``Close the door" or ``Eat the doughnut in order to satisfy your 
sweet tooth." An imperative is categorical if it holds unconditionally for all rational agents under all 
circumstances. Kant argues that the moral law must be a categorical imperative, for otherwise it would 
not have the force that makes it a moral law \cite[5]{groundwork}. In order for an imperative to be 
categorical, it must be derived from the will's authority over itself. Our wills are autonomous, so 
the only thing that can have unconditional authority over a rational will is 
the rational will itself. In Velleman's version of this argument, he claims that no one else can tell you what 
to do because you can always ask why you 
should obey their authority. The only authority that you cannot question is the authority of your own 
practical reason. To question this authority is to demand a reason for acting for reasons, which 
concedes the authority of reason itself \cite[23]{velleman}. Therefore, the only possible candidates 
for the categorical imperative are those rules that are required of the will because it is a will. 
The categorical imperative must be a property of practical reason itself.

Armed with this understanding of practical reason, Kant presents the categorical 
imperative. He presents three ``formulations" or versions of the categorical imperative and goes on to 
argue that all three formulations are equivalent. In this project, I focus on the first formulation,
the Formula of Universal Law, but will briefly present the other two as well.\footnote{For more on this 
choice, see Section Why FUL.}

The first formulation of the categorical imperative is the
Formula of Universal Law (FUL), which reads, ``act only according to that maxim through which you can 
at the same time will that it become a universal law" \cite[34]{groundwork}. This formulation
generates the universalizability test, which tests the moral value of a maxim by 
imagining a world in which it becomes a universal law and attempting to will the maxim in that world.
If there is a contradiction in willing the maxim in a world in which everyone universally wills the maxim,
the maxim is prohibited. 
Velleman presents a concise argument for the FUL. He argues that reason is universally shared among reasoners. For 
example, all reasoners have equal access to the arithmetic logic that shows that ``2+2=4" \cite[29]{velleman}. The chain of 
reasoning that makes this statement true is not specific to any person, but is universal across people. 
Therefore, if I have sufficient reason to will a maxim, so does every other rational agent. There is 
nothing special about the operation of my practical reason that other reasoners don't have access to. 
Practical reason is shared, so in adopting a maxim, I implicitly state that all reasoners
across time also have reason to adopt that maxim. Therefore, because I act on reasons, I must obey the 
FUL. Notice that this fulfills the above criterion for a categorical imperative: the FUL is derived from 
a property of practical reason itself and thus derives authority from the will's authority over itself, 
as opposed to some external authority.

The second formulation of the categorical imperative is the formula of humanity (FUH): ``So act that you use humanity, 
in your own person, as well as in the person of any other, always at the same time as an end, never merely 
as a means." \cite[41]{groundwork}. This formulation is often understood as requiring us to 
acknowledge and respect the dignity of every other person. The third formulation of the categorical 
imperative is the formula of autonomy (FOA), which Korsgaard summarizes in her introduction to the Groundwork 
as, ``we should so act that we may think of ourselves as legislating universal laws through our 
maxims" \cite[28]{korsgaardintro}. While closely related to the FUL, the FOA presents morality as the activity of 
perfectly rational agents in an ideal ``kingdom of ends," guided by what Kant calls the ``laws of freedom."

The above is not meant to serve as a full defense or articulation of Kant's ethical theory, as that is outside the scope
of this thesis. Instead, I briefly reconstruct a sketch of Kant's ethical theory in the hopes 
of offering context for the implementation of the FUL I present later in the thesis. Additionally, understanding 
the structure of Kant's theory also reveals why it is an ideal candidate 
for formalization.\<close>

text \<open>\textbf{Ease of Automation}\<close>

text \<open>Kantian ethics is an especially candidate for formalization because the categorical imperative, particularly the FUL, 
is a property of reason related to the form or structure of a maxim, or a formal principle of practical
reason. It does not require any situational knowledge or contingent beyond the circumstances included
in the maxim itself and thus requires far less contingent facts than other ethical theories.
Instead, 
it is purely a property of the proposed principle for action. This formalism makes Kantian ethics an 
attractive candidate for formalization. While other ethical theories often rely on many facts about 
the world or the actor, Kantian ethics simply relies on the form of a given maxim. A computer evaluating 
a maxim doesn't require any knowledge about the world beyond what is contained in a maxim. A maxim 
is the only input that the computer needs to make a moral judgement. Automating 
Kantian ethics merely requires making the notion of a maxim precise and representing it to the computer. 
This distinguishes Kantian ethics from consequentialism and virtue ethics, which, as I argued above, 
require far more knowledge about the world or the agent to reach a moral decision.

Not only does evaluating Kantian ethics focus on a maxim, a maxim itself is an object
with a thin representation for a computer, as compares to more complex objects like states of 
affairs or moral character. Later in my project, I argue that a maxim can be represented simply as 
a tuple of circumstances, act, and goal.\footnote{For more, see Section What is a Maxim?} This representation
is simple and efficient, especially when compared to the representation of a causal chain or a state of 
affairs or moral character. A maxim is a principle with a well-defined form, so representing a maxim
to the computer merely requires capturing this form. This property not only reduces the computational complexity
(in terms of time and space) of representing a maxim, it also make the system easier for human reasoners
to interact with. A person crafting an input to a Kantian automated agent needs to reason about relatively
simple units of evaluation, as opposed to the more complex features that consequentialism and virtue
ethics require. I will make the comparision to consequentialism and virtue ethics explicit below.

 \<close>

text \<open>\textbf{Difficulties in Automation}\<close>

text \<open>My choices to interpret maxims and the Formula of Universal Law in a particular way represent debates
in Kantian ethics over the meanings of these terms that I take a stance on. Another debate in Kantian 
ethics is the role of ``common-sense" reasoning. Kantian ethics requires common-sense reasoning to 
determine which circumstances are ``morally relevant" in the formulation of a maxim. Many misunderstandings
in Kantian ethics are due to badly formulated maxims, so this question is important for an ethical 
reasoner to answer. My system does not need to answer this question because I assume a well-formed
maxim as input and apply the categorical imperative to this input, but if my system were ever to be used
in a faully automated agent, answering this question would require significant computational and philosophical
work. For more, see Section AI Ethics.

Common-sense reasoning is also relevant in applying the universalizability test itself. Consider an example
maxim tested using the Formula of Universal Law: ``When broke, I will falsely promise to repay a loan
to get some quick cash." This maxim fails the universalizability test because in a world where everyone
falsely promises to repay loans, no one will believe promises anymore, so the maxim will no longer serve
its intended purpose (getting some quick cash). Making this judgement requires understanding enough about
the system of promising to realize that it breaks down if everyone abuses it in this manner. This is a
kind of common sense reasoning that an automated Kantian agent would need. This need is not unique to 
Kantian ethics; consequentialists agents need this kind of common sense to determine the consequences of 
an action and virtue ethical agents need this kind of common sense to determine which virtues an action
reflects. Making any ethical judgement requires relatively robust conceptions of the action or situation
at hand, falsely promising in this case. The advantage of Kantian ethics is that this is all the common 
sense that it requires, whereas a consequentialist or virtue ethical agent will require much more. All
moral theories evaluating falsely promising will a robust definition of the convention of promising, 
but consequentialism and virtue ethics will also require additional information about consequences or character
that Kantian ethics will not. Thus, although the need for common sense poses a challenge to automated
Kantian ethics, this challenge is more acute for consequentialism or virtue ethics so Kantian ethics remains
 within the closest reach of automation. \<close>


(*<*)
end
(*>*)
