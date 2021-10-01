(*<*) theory paper41
  imports  paper22 paper224

begin(*>*)

section "Novel Formalization of the Categorical Imperative"

text "In this section, I present a custom formalization of the categorical imperative, as inspired by 
the goals from the previous chapter."

subsection "Logical Background"

text \<open>The previous attempts to model the categorical imperative in Chapter 2 partially failed due to 
lack of expressivity about the complexity of a maxim. Specifically, they treated actions as a single, 
monolithic unit of evaluation, whereas most Kantians consider the unit of evaluation for the FUL to the more
complex notion of a maxim. In this section, I will present some logical background necessarily to more fully 
capture the spirit of a maxim. I will begin by borrowing some machinery to handle ``subjects" who perform 
actions from Chapter 2.\<close>

typedecl s \<comment>\<open>s is the type for a ``subject," i.e. the subject of a sentence\<close>
type_synonym os = "(s \<Rightarrow> t)" \<comment>\<open>Recall that an open sentence maps a subject to a term to model substitution.\<close>

type_synonym maxim = "(t * os * t)" \<comment>\<open>I define a maxim as a circumstance, act, goal pair (C, A, G), read 
as ``In circumstances C, do act A for goal G."  A circumstance is represented as a set of worlds 
$t$ where that circumstance holds. A goal is a term because it can be true or false at a world if it 
is realized. An act is an open sentence because, once we substitute an agent in, an act can be true or 
false at a world if it is actually performed by that subject.\<close>

text \<open>My definition of a maxim is inspired by Onora O'Neill's work on maxims, and I will defend my representation
below and consider an additional component that Patricia Kitcher @{cite whatisamaxim} argues for.

$\textbf{O'Niell's Original Schematic and The Role of Practical Judgement}$

O'Neill$\footnote{p. 37}$ @{cite "actingonprinciple"} presents what Kitcher calls the widely accepted view that a maxim is a circumstance, 
act, goal tuple as I represented above. She views a maxim as a particular, subjective instantiation of a 
practical principle, which people may choose to act on or live by. Like a practical principle, a maxim 
is a kind of action-guiding rule and thus naturally includes an action and the circumstances under which 
it should be performed, which are often referred to as ``morally relevant circumstances." 

She also includes the notion of a maxim's purpose or end (which I call goal) because Kant includes this in many of his 
example maxims and because Kant argues that human activity, because it is guided by a rational will, 
is inherently purposive. People do not act randomly, but instead in the pursuit of ends which they 
deem valuable @{cite sources}$\footnote{where in sources is this discussed}$. This inclusion is also essential 
for the version of the universalizability test that I will implement, explained in Section ??, so is 
ultimately uncontroversial.

O'Niell's inclusion of circumstances, on the other hand, is interesting because it leaves open the question of what qualifies as a 
relevant circumstance for a particular maxim. This is gives rise to ``the tailoring objection" @{cite whatisamaxim}$\footnote{Kitcher
on p.217 cites Wood p. 102 @{cite kantsethicalthought} as offering an example of a false positive due to this objection.}$, 
under which maxims are arbitrarily specified to pass the FUL. For example, the maxim ``When my name is Lavanya Singh,
I will lie to get some easy money," is universalizable, but is clearly a false positive. One solution to 
this problem is to argue that the circumstance ``When my name is Lavanya Singh" is not relevant 
to the rest of the maxim. This solution requires some discussion of what qualifies as a relevant circumstance.

O'Niell seems to adopt some version of this view when she concedes that a maxim cannot include ALL 
the infinitely many circumstances in which the agent may perform the action$\footnote{p. 37}$. She argues that this is 
an artifact of the fact that maxims are closely related to practical principles. Like any practical rule, 
maxims require an exercise of judgement to determine in which circumstances they should be applied. 
This judgement, applied in both choosing to exercise the maxim and in the formulation of the maxim 
itself, is what determines what qualifies as a ``morally relevant circumstance."

The implication for my project is that the computer cannot perform all ethical activity alone. 
Human judgement or the exercise of practical reason is essential to both formulate kinds maxims and 
determine when the actual conditions of life coincide with the circumstances in which the maxim is relevant. 
The second concern is less relevant to my project because analyzing a formal representation of the FUL requires 
making the circumstances in a given scenario precise. The first concern, on the other hand, demonstrates 
the important fact that ethics as presented here is not a solely computational activity. A
human being must create a representation for the dilemma they wish to test, effectively translating 
a complex, real situation into a flat logical structure. Not only will some of the situation's complexity
inevitably be lost, the outcome of the test will determine greatly on how the human formulates the maxim
and whether or not this formulation does indeed include morally relevant circumstances. If the human puts 
garbage into the test, the test will surely return garbage out.

While this may appear to be a weakness of my system, I believe that it actually
allows my system to retain some of the human complexity that many philosophers agree cannot be automated away.\footnote{Powers @{cite powers} presents 
the determination of morally relevant circumstances as an obstacle to the automation of Kantian ethics.}
Ethics is a fundamentally human activity. As Korsgaard argues, the categorical imperative is a statement 
about the properties of rational wills, i.e. our human wills. If ethics is meant to guide human behavior, 
the role of the computer becomes clear as not a replacement for our will (which is the entire focal point 
of Kantian ethics), but instead as a tool to help guide our wills and help us reason more efficiently 
and more effectively. Just as calculators don't render mathematicians obsolete, computational ethics
does not render human judgement obsolete. Chapter 4 Section ??  will be devoted to a more complete discussion 
of this issue.

$\textbf{Motive}$

Kitcher @{cite whatisamaxim} begins with O'Niell's (C, A, G) view and expands it to include the motivation 
behind performing the maxim. This additional component is read 
as ``In circumstance C, I will do A in order to G because of M." where M may be ``duty" or ``self-love."
This captures Kant's idea that an action derives its moral worth from being done for the sake of duty itself.
Given that, under the Kantian constituvist view, the categorical
imperative completely defines duty, Kitcher argues that the FUL would obligate maxims of the form 
``In circumstance C, I will do A in order to G because I would will that I and everyone else simultaneously
will do A in order to G in circumstance C." In other words, the affirmative result of the FUL becomes 
the motivation for a moral action.

While Kitcher's conception of a maxim captures Kant's idea of acting for duty's own sake, I will not implement it 
because it is not necessary for putting maxims through the FUL. Indeed, Kitcher acknowledges that 
O'Niell's formulation suffices for the universalizability test, but is not the general notion of a maxim.
Notice that in order to pass the maxim through the FUL, it suffices to know C, A and G. The FUL
derives the purpose that Kitcher bundles into the maxim, so automating the FUL does not require 
including some notion of a purpose. The ``input" to the FUL is the (C, A, G) pair. My project takes 
this input and returns the motivation that the dutiful, moral agent would adopt. Additionally, doing
justice to the rich notion of motivation requires modelling the operation of practical reason itself, 
which it outside the scope of this project. My work focuses on the FUL test itself, but future work that 
models the process of practical reason may use my implementation of the FUL as a ``library." Combined 
with a logic of practical reason, an implementation of the FUL can move from evaluating a maxim to 
evaluating an agent's behavior, since that's where ``acting from duty" starts to matter.\<close>

fun will :: "maxim \<Rightarrow> s\<Rightarrow>  t" ("A _ _")
  where "will (c, a, g) s = (c \<^bold>\<rightarrow> (a s))"

text \<open>Korsgaard claims that ``To will an end, rather than just
wishing for it or wanting it, is to set yourself to be its cause" @{cite "sources"}. To will a maxim, then, 
is to set yourself to, in the relevant circumstances, be the cause of its goal by taking the means 
specified in the maxim. This coheres with 
Kitcher's and Korsgaard's understanding of a maxim as a principle or rule to live by. At worlds 
where the circumstances do not hold, a maxim is vacuously willed. If you decide to act on the rule ``I will 
do X in these cirumstances", then you are vacuously obeying it when the circumstances don't hold.  

The above discussion implies that willing a maxim is particular to the agent, justifying my choice to 
require that a particular subject will a maxim. O'Niell argues for this interpretation when she distinguishes 
between the evaluation of a principle, which is generic, and a maxim, which she views as ``individuated only 
by referring to a person"$\footnote{p. 13}$ @{cite "actingonprinciple"}. I adopt the spirit of this interpretation but modify it slightly 
by representing the general maxim as a principle that anyone could adopt, and the act of willing the maxim 
as a person-particular instantiation of the maxim.

I additionally represent a subject as willing a maxim because I use the word `will' as a verb, to mean committing oneself to living by
the principle of a maxim. This coheres with Kant's Formula of Universal Law, because it tests the willing 
of a maxim to determine if it could be a universal law that everyone committed to. Formalizing this idea,
the type of a maxim that is willed is a term, allowing me
to use DDL's obligation operator on the notion of willing a maxim. 

Worlds where the circumstances do not hold are not relevant for determining obligation. Recall that in 
our definition of the obligation operator, we define $O \{B|A\}$ to be true at all worlds iff ob(B)(A), or 
if the obligation function maps A to obligatory in context B (where the context is a set of worlds). This 
definition implies that worlds outside of B have no bearing on the obligatory-ness of A in context B, which 
coheres with intuitions about obligation in a context. Thus, the dyadic obligation operator 
disqualifies worlds where the context does not hold, so the vacuous truth of the will statement in 
these worlds does not matter. 

Given that the will function already excludes worlds where the circumstances fail (by rendering 
the statement vacuously true at them), one may conclude that the dyadic obligation operator is now useless. 
Using the dyadic obligation operator allows me to take advantage of the power of DDL to represent the bearing 
that circumstances have on obligation. DDL has powerful axioms expressing the relationship between circumstances 
and obligation, such as the fact that obligations are monotonically increasing with respect to broader 
circumstances. Using the monadic obligation operator would require me to either operate with an empty 
notion of context or to redefine these axioms. The dyadic obligation operator lets me take advantage of the full 
power of DDL in expressing contrary-to-duty obligations. This is particularly important for Kantian ethics 
and the FUL specifically because many critiques of the FUL rely on attention to circumstances (tailoring 
objection) or lack thereof (ideal theory). This is also an innovation that my custom formalization presents 
over the prior work. By formally including the notion of a circumstance or context, I am able to represent 
these objections that Kantian scholars study. Formalizing Kantian ethics in a dyadic deontic logic 
instead of a monadic deontic logic is a key contribution of this thesis.
\<close>

fun effective :: "maxim\<Rightarrow>s\<Rightarrow> t" ("E _ _")
  where "effective (c::t, a::os, g::t) s = ((will (c, a, g) s) \<^bold>\<equiv> g)"

text \<open>A maxim is effective for a subject when, if the subject wills it then the goal is achieved, and
when the subject does not act on it, the goal is not achieved.$\footnote{Thank you to Jeremy D. Zucker for helping me think through this.}$ @{cite sepcausation} 
The former direction of the implication 
is intuitive: if the act results in the goal, it was effective in causing the goal. This represents `necessary'
causality. 

The latter direction represents `sufficient' causality, or the idea that, counterfactually,
if the maxim were not willed, then the goal is not achieved @{cite "lewiscausality"}. Note that nothing else changes about this
counterfactual world—the circumstances are identical and we neither added additional theorems nor 
specified the model any further. This represents Lewis's idea of "comparative similarity," @{cite lewiscounterfactuals} where 
a counterfactual is true if it holds at the most similar world. In our case, this is just the world 
where everything is the same except the maxim is not acted on.

Combining these ideas, this definition of effective states that a maxim is effective if the 
maxim being acted on by a subject is the necessary and sufficient cause of the goal.\footnote{Should I wave a hand at critiques of counterfactual causality?}

If the circumstances do not hold and the goal is achieved, then the maxim is vacuously effective, since 
it is vacuously willed (as described above). While this scenario is counterintuitive, it is not very 
interesting for my purposes because, when the circumstances do not hold, a maxim is not applicable. It 
doesn't really make sense to evaluate a maxim when it's not supposed to be applied. The maxim ``When on Jupiter,
read a book to one-up your nemesis" is vacuously effective because it can never be disproven.\<close>


(*<*)
text_raw \<open>\pagebreak\<close>

text \<open>$\textbf{``Effectiveness" of a Maxim}$\<close>

text \<open>I wish to formalize the notion of an ``effective" maxim. Intuitively, a maxim (a rule to 
perform an act A for goal G) is effective if the act results in the goal. For example, studying hard 
to get good grades is (sometimes) an effective maxim because the act of studying (sometimes) results in
 the end of getting good grades. At first glance, it is tempting to represent effectiveness 
as follows: an act, goal pair ($A, G$) is effective if $A \longrightarrow G$. If $A$ then $G$ implies that 
$A$ is an effective mechanism for achieving $G$.

Trivial truth is a problem for this interpretation. If act $A$ never happens or 
is impossible, then, $\forall G$, it is trivially true that $A \longrightarrow G$ (since $\sim A$). This leads to the 
disturbing conclusion that impossible actions are effective in achieving any goal. While the messiness 
is familiar to logicians, it has troubling implications for ethics.

One such issue arises from Korsgaard's @{cite KorsgaardFUL} argument that, if an act no longer exists, then it is no 
longer an effective mechanism for achieving any ends at all. This is a critical part of her interpretation 
of the formula of universal law\footnote{Korsgaard compares two interpretations of the formula of universal law. 
Under the logical contradiction view, a maxim is prohibited if, when everyone adopts it, it is logically
impossible. Under the practical contradiction (PC) view, a maxim is prohibited if, when everyone adopt it, 
it is no longer effective (the act isn't a means to the goal or end. For cases where universalization 
renders the action impossible (like lying, since if everyone lies no one would believe each other), both 
views should prohibit the maxim. For the PC view to prohibit the maxim, the maxim's impossibility must 
also imply its ineffectiveness.}. Under Korsgaard's interpretation, if 
studying hard is no longer an existing or possible action  (maybe because of perpetual construction outside my room), 
then the maxim ``studying hard to get a good grade" is no longer effective. Trivial truth means that the
initial definition of effectiveness cannot achieve this result.

I could fix this problem by defining effectiveness as an act being existent and 
also achieving the goal. I could try to model existent as ``possible at some world," therefore using 
the power of modal logic to represent ideas like possibility. That way, a maxim is effective if (1) 
the act is possible at some world and (2) in worlds where the act is in fact realized, the goal is also
realized. 

This solution draws a distinction between the notions of possibility (which is a modal
sentence) and truth or occurrence. Drawing this distinction 
allows us to preserve the fact that trivial truth does, in some way, make sense. Specifically, in a world 
where the act is not performed, we still think that the maxim is effective. Its effectiveness hasn't been 
disproven. Just as all purple elephants can fly, hunting purple elephants is an effective way to make money\footnote{Someone not steeped in logic might not agree here.}.

This solution has two drawbacks. First, it introduces additional logical complexity into the effectiveness
predicate. This is fine, but may have performance/developer time drawbacks. Ideally, a sentence in simple propositional
logic could represent effectiveness. Second, more importantly, it doesn't address the idea of ``causality." 
It might be the case that $A \longrightarrow G$ but $A$ does not cause $G$. For example, maybe eating 
banana bread is a way to improve my grades because I eat banana bread but also happen to study hard, which 
is the real cause of my GPA. How can I represent this idea? $A \wedge G$ fails because an act doesn't have to occur to be an effective means to an end 
(the same reason that preserving trivial truth is nice). $A \longleftrightarrow G$ fails because we can imagine
there also being some other cause for $G$. I can get good grades by studying hard or by bribing my professor, but
both of those remain effective methods to achieve goal $G$. 

How do I solve this problem? Should I look into logics of causation (I'm sure such things exist)? 
Should I represent effectiveness as the implication $A \longrightarrow G$ holding at every world? That 
idea addresses the second challenge about causation vs correlation, since if  $A \longrightarrow G$ in
every possible world, then $A$ must cause $G$, since any fact noncontingent on $A$ will be false at some 
possible world. This idea introduces even more logical complexity!

\<close>


end
(*>*)
