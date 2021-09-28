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
 \<comment>\<open>A maxim is acted on by a subject at a world if, when the circumstances hold at that world, the 
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
Open Q: If a maxim is effective for me, is it effective for you? Do we need the subject here?\<close>


(*<*)
end
(*>*)
