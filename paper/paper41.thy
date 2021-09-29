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

type_synonym maxim = "(t * os * t)" \<comment>\<open>Korsgaard @{cite actingforareason} interprets Kant's idea of a maxim as being equivalent 
to Aristotle's notion of logos or principle (insert cite), which is a circumstance, act, goal pair. Read logos (C, A, G)
as ``In circumstance C, I will do A in order to G." A circumstance is represented as a set of worlds 
$t$ where that circumstance holds. A goal is a term because it can be true or false at a world if it 
is realized. An act is an open sentence because, once we substitute an agent in, an act can be true or 
false at a world if it is actually performed by that subject. 

Korsgaard interprets a maxim as being equivalent to a logos, and thus only being composed of the features
above. Kitcher @{cite whatisamaxim} argues that a maxim should also include the motivation. This additional component is read 
as ``In circumstance C, I will do A in order to G because of M." where M may be ``duty" or ``self-love."
This captures Kant's idea that an action derives its moral worth from being done for the sake of duty itself.
Given that, under the Kantian constituvist view, the categorical
imperative completely defines duty, Kitcher argues that the FUL would obligate maxims of the form 
``In circumstance C, I will do A in order to G because I would will that I and everyone else simultaneously
will do A in order to G in circumstance C." In other words, the affirmative result of the FUL becomes 
the motivation for a moral action.

While Kitcher's conception of a maxim captures Kant's idea of acting for duty's own sake, I will not implement it 
because it is not essential to putting maxims through the FUL. 
Notice that in order to pass the maxim through the FUL, it suffices to know C, A and G. The FUL
derives the purpose that Kitcher bundles into the maxim, so automating the FUL does not require 
including some notion of a purpose. The ``input" to the FUL is the (C, A, G) pair. My project takes 
this input and returns the motivation that the dutiful, moral agent would adopt. Additionally, doing
justice to the rich notion of motivation requires modelling the operation of practical reason itself, 
which it outside the scope of this project. My work focuses on the FUL test itself, but future work that 
models the process of practical reason may use my implementation of the FUL as a ``library." Combined 
with a logic of practical reason, an implementation of the FUL can move from evaluating a maxim to 
evaluating an agent's behavior, since that's where ``acting from duty" starts to matter.\<close>

fun act_on :: "maxim \<Rightarrow> s\<Rightarrow>  t" ("A _ _")
  where "act_on (c, a, g) s = (c \<^bold>\<rightarrow> (a s))"
 \<comment>\<open>This should be willed on. is there literature on this discussion?

A maxim is acted on by a subject at a world if, when the circumstances hold at that world, the
subject performs the action (denoted by the application of the action to the subject). At worlds 
where the circumstances do not hold, a maxim is trivially acted on. This coheres with Kitcher's and
 Korsgaard's understanding of a maxim as a principle or rule to live by. If your rule is ``I will 
do X in these cirumstances", then you are trivillay obeying it when the circumstances don't hold.  

The type of a maxim that is acted on is a term, allowing me
to use DDL's obligation operator on the notion of acting on a maxim. While DDL offers a dyadic obligation
operator (taking in a term and context as arguments), I will only use the monadic version (only 
taking in a term), since the act\_on function already excludes worlds where the circumstances do not hold.

Worlds where the circumstances do not hold are not relevant for determining obligation. Recall that in 
our definition of the obligation operator, we define O {B|A} to be true at all worlds iff ob(B)(A), or 
if the obligation function maps A to obligatory in context B (where the context is a set of worlds). This 
definition implies that worlds outside of B have no bearing on the obligatory-ness of A in context B, which 
coheres with intuitions about obligation in a context. Thus, the dyadic obligation operator 
disqualifies worlds where the context does not hold, so the trivial truth of the act\_on statement in 
these worlds does not matter. 

Given that the `acted\_on' function already excludes worlds where the circumstances fail (by rendering 
the statement trivially true at them), one may conclude that the dyadic obligation operator is now useless. 
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
  where "effective (c::t, a::os, g::t) s = ((act_on (c, a, g) s) \<^bold>\<rightarrow> g)"
\<comment>\<open>A maxim is effective for a subject when, if the subject acts on it then the goal is achieved. 
A maxim is trivially effective in worlds where the circumstances do not hold or where it is not 
acted on by the argument above. 
Open Q: If a maxim is effective for me, is it effective for you? Do we need the subject here?

nonexistent is ineffective, no trivial effectiveness in philosophy
write up language to signal the choices that im making
3 choice points - what version -> FUL; definition of maxim; and practical contradiction interpretation
PC view -> circumstances are that everyone does it!!!\<close>

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
(*<*)

end
(*>*)
