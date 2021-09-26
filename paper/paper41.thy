(*<*) theory paper41
  imports  paper22 paper224

begin

section "Novel Formalization of the Categorical Imperative"

text "In this section, I present a custom formalization of the categorical imperative, as inspired by 
the goals from the previous chapter."

subsection "Logical Background"

typedecl s \<comment>\<open>s is the type for a ``subject," i.e. the subject of a sentence\<close>
type_synonym os = "(s \<Rightarrow> t)"

text \<open>Borrowing subjects from Ch. 2.\<close>

typedecl act \<comment>\<open>Type representing an act such as ``Running"\<close>
typedecl goal \<comment>\<open>Type representing a goal such as ``To visit my mother"\<close>

type_synonym maxim = "(t * os * t)" \<comment>\<open>A logos or principle according to Aristotle
 is a circumstance, act, goal pair. Read logos (C, A, G)
as ``In circumstance C, S will do A in order to G." A circumstance is represented as a set of worlds 
$t$ where that circumstance holds. A goal is a term because it can be true or false at a world if it 
is realized. An act is an open sentence because, once we substitute an agent in, an act can be true or 
false at a world if it is actually performed by that subject. 

Korsgaard interprets a maxim as being equivalent to a logos, and thus only being composed of the features
above. Kitcher argues for one additional component: the motivation. This additional component is read 
as ``In circumstance C, S will do A in order to G because of M." where M may be ``duty" or ``self-love."
This captures Kant's idea that moral actions are done for the sake of duty itself. Given that the categorical
imperative captures the idea of duty, Kitcher argues that the FUL would obligate maxims of the form 
``In circumstance C, S will do A in order to G because they would will that and that simultaneously everyone
will do A in order to G in circumstance C." In other words, the motivation becomes the affirmative result
of the FUL for moral action.

While this notion richly captures Kant's idea of acting for duty's own sake, I will not implement it 
because it is not essential to the FUL and because motivation is complex to capture computationally. 
Notice that in order to pass the maxim through the FUL, it suffices to know C, S, A and G. The FUL
derives the purpose that Kitcher bundles into the maxim, so automating the FUL does not require 
including some notion of a purpose. The ``input" to the FUL is the (C, S, A, G) pair. Second, doing
justice to the rich notion of motivation requires modelling the operation of practical reason itself, 
which it outside the scope of this project. My work focuses on the FUL test itself, but future work that 
models the process of practical reason may use my implementation of the FUL as a ``library." Combined 
with a logic of practical reason, an implementation of the FUL can move from evaluating a maxim to 
evaluating an agent's behavior, since that's where ``acting from duty" starts to matter.\<close>

fun act_on :: "maxim \<Rightarrow> s\<Rightarrow>  t" ("A _ _")
  where "act_on (c, a, g) s = (c \<^bold>\<rightarrow> (a s))"
 \<comment>\<open>A maxim is acted on by a subject at a world if the circumstances hold at that world and the 
subject performs the action (denoted by the application of the action to the subject). At worlds 
where the circumstances do not hold, a maxim is trivially acted on. This coheres with Kitcher's and
 Korsgaard's understanding of a maxim as a principle or rule to live by. If your rule is ``I will 
do X in these cirumstances", then you can't violate the rule when the circumstances don't hold.  

The type of a maxim that is acted on is a term, allowing me
to use DDL's obligation operator on the notion of acting on a maxim. While DDL offers a dyadic obligation
operator (taking in a term and context as arguments), I will only use the monadic version (only 
taking in a term), since the act\_on function already excludes worlds where the circumstances do not hold.
HOW DOES THIS INTERACT WITH THE MONADIC VS DYADIC O OPERATOR AND THE OB FUNCTION? WHAT DO WE DO IN WORLDS 
WHERE THE CIRCUMSTANCES DO NOT HOLD?\<close>

fun effective :: "maxim\<Rightarrow>s\<Rightarrow> t" ("E _ _")
  where "effective (c::t, a::os, g::t) s = ((act_on (c, a, g) s) \<^bold>\<rightarrow> g)"
\<comment>\<open>A maxim is effective for a subject when, if the subject acts on it then the goal is achieved. 
A maxim is trivially effective in worlds where the circumstances do not hold or where it is not 
acted on by the argument above. 
Open Q: If a maxim is effective for me, is it effective for you?\<close>


(*<*)
end
(*>*)
