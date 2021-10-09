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

type_synonym maxim = "(t * os * t)" \<comment>\<open>I define a maxim as a circumstance, act, goal tuple (C, A, G), read 
as ``In circumstances C, act A for goal G." Isabelle's strict typing rules mean that the choice of the 
type of each member of this tuple is significant. A circumstance is represented as a set of worlds 
$t$ where that circumstance holds. A goal is also a term because it can be true or false at a world if it 
is realized or not. An act is an open sentence because an act itself is not the kind of thing that can 
be true or false (as in, an act is not truth-apt), but the combination of a subject performing an act 
can be true or false at a world depending on whether or not the act is indeed performed by that subject. 
For example, ``running" is not truth-apt, but ``Sara runs" is truth-apt.\<close>

text \<open>I define a maxim as a circumstance, act, goal tuple (C, A, G), read 
as ``In circumstances C, act A for goal G." Isabelle's strict typing rules mean that the choice of the 
type of each member of this tuple is significant. A circumstance is represented as a set of worlds 
$t$ where that circumstance holds. A goal is also a term because it can be true or false at a world if it 
is realized or not. An act is an open sentence because an act itself is not the kind of thing that can 
be true or false (as in, an act is not truth-apt), but the combination of a subject performing an act 
can be true or false at a world depending on whether or not the act is indeed performed by that subject. 
For example, ``running" is not truth-apt, but ``Sara runs" is truth-apt.

My definition of a maxim is inspired by Onora O'Neill's work on maxims. I will defend my representation
below and consider an additional component that Patricia Kitcher argues for.

$\emph{O'Niell's Original Schematic and The Role of Practical Judgement}$

O'Neill$\footnote{p. 37}$ @{cite "actingonprinciple"} presents what Kitcher @{cite whatisamaxim}  calls the widely accepted 
view that a maxim is a circumstance, act, goal tuple. A maxim 
is an action-guiding rule and thus naturally includes an act and the circumstances under which 
it should be performed, which are often referred to as ``morally relevant circumstances." 

She also includes a purpose, end, or goal in the maxim because Kant includes this in many of his 
example maxims and because Kant argues that human activity, because it is guided by a rational will, 
is inherently purposive@{cite groundwork}\footnote{(G 4:428)}. A rational will does not act randomly (else it would not be rational), 
but instead in the pursuit of ends which it deems valuable. This inclusion is also essential for the version of the universalizability test 
that I will implement, explained in Section ??.

O'Neill's inclusion of circumstances is potentially controversial because it leaves open the question of what qualifies as a 
relevant circumstance for a particular maxim. This is gives rise to ``the tailoring objection" @{cite whatisamaxim}$\footnote{Kitcher
on p.217 cites Wood p. 102 @{cite kantsethicalthought} as offering an example of a false positive due to this objection.}$, 
under which maxims are arbitrarily specified to pass the FUL. For example, the maxim ``When my name is Lavanya Singh,
I will lie to get some easy money," is universalizable, but is clearly a false positive. One solution to 
this problem is to argue that the circumstance ``When my name is Lavanya Singh" is not morally relevant 
to the act and goal. This solution requires some discussion of what qualifies as a relevant circumstance.

O'Neill seems to acknowledge the difficult of determining relevant circumstances when she concedes that a maxim cannot include all 
of the infinitely many circumstances in which the agent may perform the action$\footnote{p. 37}$. She argues that this is 
an artifact of the fact that maxims are rules of practical reason, the kind of reason that helps us decide what to do 
and how to do it @{cite bok}. Like any practical rule, 
maxims require the exercise of practical judgement to determine in which circumstances they should be applied. 
This judgement, applied in both choosing when to exercise the maxim and in the formulation of the maxim 
itself, is what determines the ``morally relevant circumstances."

The upshot for computational ethics is that the computer cannot perform all ethical activity alone. 
Human judgement and the exercise of practical reason are essential to both formulate maxims and 
determine when the actual conditions of life coincide with the circumstances in which the maxim is relevant. 
Choosing when to exercise a maxim is less relevant to my project because analyzing a formal representation of the FUL requires 
making the circumstances in a given scenario precise, but will be important for applications of 
computational ethics to guiding AI agents. The difficulty in formulating a maxim, on the other hand, demonstrates 
the important fact that ethics, as presented here, is not a solely computational activity. A
human being must create a representation for the dilemma they wish to test, effectively translating 
a complex, real situation into a flat logical structure. This parallels the challenge that programmers 
face when translating the complexity of reality to a programming langauge or computational representation. Not only will some of the situation's complexity
inevitably be lost, the outcome of the universalizability test will depend on how the human formulates the maxim
and whether or not this formulation does indeed include morally relevant circumstances. If the human puts 
garbage into the test, the test will return garbage out.

While this may appear to be a weakness of my system, I believe that it actually
allows my system to retain some of the human complexity that many philosophers agree cannot be automated away.\footnote{Powers @{cite powers} presents 
the determination of morally relevant circumstances as an obstacle to the automation of Kantian ethics.}
Ethics is a fundamentally human activity. Kant argues that the categorical imperative is a statement 
about the properties of rational wills. In fact, Korsgaard argues that morality derives its authority over us, 
or normativity, only because is it a property of a rational will, and we, as human beings, are rational wills.
If ethics is meant to guide human behavior, the role of the computer becomes clear as not a replacement for our will,
but instead as a tool to help guide our wills and reason more efficiently 
and more effectively. Just as calculators don't render mathematicians obsolete, computational ethics
does not render human judgement or philosophy obsolete. Chapter 4 Section ?? will be devoted to a more complete discussion 
of this issue.

$\emph{Exclusion of Motive}$

Kitcher @{cite whatisamaxim} begins with O'Niell's circumstance, act, goal view and expands it to include the motive 
behind performing the maxim. This additional component is read 
as ``In circumstance C, I will do A in order to G because of M," where M may be ``duty" or ``self-love."
Kitcher argues that the inclusion of motive is necessary for the fullest, most general form of a maxim
in order to capture Kant's idea that an action derives its moral worth from being done for the sake of duty itself.
Under this view, the FUL would obligate maxims of the form 
``In circumstance C, I will do A in order to G because I can will that I and everyone else simultaneously
will do A in order to G in circumstance C." In other words, if Kant is correct in arguing that moral 
actions must be done from the motive of duty, the affirmative result of the FUL becomes 
the motive for a moral action.

While Kitcher's conception of a maxim captures Kant's idea of acting for duty's own sake, I will not implement it 
because it is not necessary for putting maxims through the FUL. Indeed, Kitcher acknowledges that 
O'Neill's formulation suffices for the universalizability test, but is not the general notion of a maxim.
In order to pass the maxim through the FUL, it suffices to know the circumstance, act, and goal. The FUL
derives the motive that Kitcher bundles into the maxim, so automating the FUL does not require 
including a motive. The ``input" to the FUL is the circumstance, act, goal pair. My project takes 
this input and returns the motivation that the dutiful, moral agent would adopt. Additionally, doing
justice to the rich notion of motive requires modelling the operation of practical reason itself, 
which is outside the scope of this project. My work focuses on the universalizability test, but future work that 
models the process of practical reason may use my implementation of the FUL as a ``library." Combined 
with a logic of practical reason, an implementation of the FUL can move from evaluating a maxim to 
evaluating an agent's behavior, since that's when ``acting from duty" starts to matter.\<close>

abbreviation will :: "maxim \<Rightarrow> s\<Rightarrow>  t" ("W _ _")
  where "will \<equiv> \<lambda>(c, a, g) s. (c \<^bold>\<rightarrow> (a s))"
print_theorems

text \<open>Korsgaard claims that ``to will an end, rather than just
wishing for it or wanting it, is to set yourself to be its cause" @{cite "sources"}. To will a maxim, then, 
is to set yourself to, in the relevant circumstances, be the cause of its goal by taking the means 
specified in the maxim. This coheres with 
Kitcher's and Korsgaard's understanding of a maxim as a principle or rule to live by. At worlds 
where the circumstances do not hold, a maxim is vacuously willed. If you decide to act on the rule ``I will 
do X in these cirumstances", then you are vacuously obeying it when the circumstances don't hold.  

The above discussion implies that willing a maxim is particular to the agent, justifying my choice to 
require that a particular subject will a maxim. O'Neill argues for this interpretation when she distinguishes 
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

abbreviation effective :: "maxim\<Rightarrow>s\<Rightarrow> t" ("E _ _")
  where "effective  \<equiv> \<lambda>(c, a, g) s. ((will (c, a, g) s) \<^bold>\<equiv> g)"
print_theorems

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

abbreviation universalized::"maxim\<Rightarrow>s\<Rightarrow>t" where 
"universalized \<equiv> \<lambda>M s. (\<lambda>w. (\<forall>p. W M p w))"

abbreviation not_universalizable :: "maxim\<Rightarrow>s\<Rightarrow>bool" where 
"not_universalizable \<equiv> \<lambda>M s. (\<Turnstile> (universalized M s \<^bold>\<rightarrow> (\<^bold>\<not> (E M s))))"
\<comment>\<open>The maxim willed by subject $s$ is not universalizable if, for all people $p$, if $p$ wills M, then 
$M$ is no longer effective for $s$.\<close>

text \<open> Below is my first attempt at formalizing Korgsaard's definition of the practical contradiction
interpretation:  a maxim is not universalizable 
if, in the world where the maxim becomes the standard practice (i.e. everyone acts on the maxim), the
agent's attempt to use the maxim's act to achieve the maxim's goal is frustrated. In other words, if 
the maxim is universally willed (captured by applying a universal qunatifier and the will function 
to the maxim on the LHS), then it is no longer effective for the subject $s$ (RHS above). 
\<close>

abbreviation prohibited::"maxim\<Rightarrow>s\<Rightarrow>t" where 
"prohibited \<equiv> \<lambda>(c, a, g) s. O{\<^bold>\<not> (will (c,a, g) s) | c}"

abbreviation FUL0::bool where "FUL0 \<equiv> \<forall> c a g s. not_universalizable (c, a, g) s \<longrightarrow> \<Turnstile>((prohibited (c, a, g) s))"
\<comment>\<open>This representation of the Formula of Universal Law reads, ``For all circumstances, goals, acts, 
and subjects, if the maxim of the subject performing the act for the goal in the circumstances is not 
universalizable (as defined above), then, at all worlds, in those circumstances, the subject 
is prohibited (obligated not to) from willing the maxim.\<close>

lemma "FUL0 \<longrightarrow> False" using O_diamond 
  using prod.simps(2) split_conv by fastforce

text \<open>FUL0 is not consistent, and sledgehammer is indeed able to show that it implies a contradiction. 
The axioms that sledgehammer used are O\_diamond, which is @{"thm" "O_diamond"}. This axiom captures 
the idea that an obligation can't contradict its context. This is particularly problematic if the goal or 
action of a maxim are equivalent to its circumstances. In other words, if the maxim has already been 
acted on or the goal has already been achieved, then prohibiting it is impossible. 
In any model that has at least one term, it is possible to construct a maxim where the circumstances, goal, 
and act (once a subject acts on it) are all that same term, resulting in a contradiction. 

To get around this, I will exclude what I call ``badly formed maxims," which are those maxims sucht that the goal has already been 
achieved or the act has already been acted on. Under my formalization, such maxims are 
not well-formed. To understand why, we can return to Korsgaard's and O'Neill's interpretations of a maxim as a practical
guide to action. A maxim is a practical principle that guides how we behave in everyday life. A 
principle of the form ``When you are eating breakfast, eat breakfast in order to eat breakfast," is not 
practically relevant. No agent would ever need to act on such a principle. It's not necessarily contradictory
or prohibited, but it is the wrong kind of question to be asking yourself. It is not a 
well-formed maxim, so the categorical imperative does not apply to it.\<close>

abbreviation well_formed::"maxim\<Rightarrow>s\<Rightarrow>i\<Rightarrow>bool" where 
"well_formed \<equiv> \<lambda>(c, a, g) s w. (\<not> ( (c \<^bold>\<rightarrow> g) w)) \<and> (\<not> ( (c \<^bold>\<rightarrow> a s) w))"
\<comment>\<open>This abbreviation formalizes the well-formedness of a maxim for a subject. The goal cannot be 
already achieved in the circumstances and the subject cannot have already performed the act.\<close>

abbreviation FUL where "FUL \<equiv> \<forall>M::maxim. \<forall>s::s. (\<forall>w. well_formed M s w) \<longrightarrow> (not_universalizable M s \<longrightarrow> \<Turnstile> prohibited M s )"
\<comment>\<open>Let's try the exact same formalization of the FUL as above, except that it only applies to 
maxims that are well-formed at every world.\<close>

lemma "FUL"
  nitpick[user_axioms, falsify=true] oops
\<comment>\<open>The FUL does not hold in DDL, because nitpick is able to find a model for my system in which it is 
false. If the FUL were already a theorem of the system, adding it wouldn't make the system any more 
powerful, so this is the desired result.
$\color{blue}$ Nitpick found a counterexample for card s = 1 and card i = 1:

  Skolem constants:
    a = ($\lambda x. \_$)($s_1$ := ($\lambda x. \_$)($i_1$ := False))
    c = ($\lambda x. \_$)($i_1$ := True)
    g = ($\lambda x. \_$)($i_1$ := False)
    $\lambda w$. p = ($\lambda x. \_$)($i_1$ := $s_1$)
    s = $s_1$ $\color{black}$ \<close>

axiomatization where FUL:FUL

lemma True
  nitpick[user_axioms, falsify=false] by simp
\<comment>\<open>The system is still consistent! Nitpick is able to find a model in which all axioms are satisfied, 
so this version of the FUL is consistent.
$\color{blue}$ Nitpick found a model for card i = 1 and card s = 1:

  Empty assignment $\color{black}$ \<close>

text \<open>During the process of making FUL0 consistent, I used Isabelle to gain philosophical insights, 
especially about vacuous maxims. I used Nitpick and Sledgehammer to quickly test if a small tweak 
to FUL0 fixed the problem or if I was still able to derive a contradiction.  I then realized that if 
I defined the circumstances, act, and goal as constant, then FUL0 was indeed consistent. After some 
experiementation, Prof. Amin correctly pointed out that, as constants, these three entities were 
distinct. When merely quantifying over (c, a, g), all members of a tuple could be equivalent. Within
a minute, I could formalize this notion, add it to FUL0, and test if it solved the problem. The fact 
that it did spurred my philosophical insight about vacuous maxims. 

The logic confirmed that certain kinds
of circumstance, act, goal tuples are too badly formed for the categorical imperative to logically 
apply to them. The realization of this subtle problem would have been incredibly difficult without 
computational tools. The syntax and typing of Isabelle/HOL forced me to bind the free-variable $M$
in the FUL in different ways and allowed me to quickly test many bindings. The discovery of this 
logical inconsistency then enabled a philosophical insight about which kinds of maxims make sense as 
practical principles. This is one way to do computational ethics: model a system in a logic, use 
computational tools to refine and debug the logic, and then use insights about the logic to derive 
insights about the ethical phenonema it is modelling. This procedure parallels the use of proofs in 
theoretical math to understand the world.\<close>

text \<open>One potential problem with my formalization is that it does not hugly use the modal nature of the system. 
All of the properties that the FUL investigates hold at all worlds, in effect removing the modal nature 
of the system. This approach simplifies logical and therefore computational complexity, improving 
performance. On the other hand, it doesn't use the full expressivity of DDL. If I run into problems 
later on, one option is to tweak the FUL to use this expressivity. \<close> 

(*<*)

  text \<open>This is a formulation of the FUL in which, assuming every maxim is universalized at some
world (this is the axiom imagination works), at that world (or other worlds like it), if the maxim is 
not effective for the agent, then it is prohibited at the current world cw. Couple of optimizations 
necessary to get Nitpick able to handle this:
(1) Couldn't use the effective and will functions becuase they made Nitpick time out. Is there a way 
to have a purely syntactic version of these functions? They'll make notation prettier? Like an 
abbreviation with free variables?

(2) If I quantify over the maxim's components, then Nitpick times out. If I specify a 
single maxim as a constant, then it can handle everything just fine. I could try, every 
time I'm working with an example, specifying properties of these constants. The downside is that if I want 
to work with 2 maxims at once, then I have to add more constants and add the FUL as an axiom again for each of these maxims. This might not 
be too annoying in practice (I don't think I'll need that many maxims), but there's something theoretically
unsatisfying about it. I guess one theoretical explanation is that the system can only handle small models?
Which is maybe not a huge problem?


One worry is the order of the universal quantifier and the $\vDash$ or derivability symbol. In this 
representation, the universal quantifier is tightly bound to the left hand side of the equation, so it 
only quantifies into the statement ``All p will maxim M at any world." We can imagine an alternate
representation that quantifies over the sentence $\vDash W M p \longrightarrow \sim E M s$. This is 
a sentence of type $s \longrightarrow bool$, since it accepts a subject ($p$) as input and returns 
a boolean (the result of $p$ substituted into the sentence.) Thus, applying the universal quantifier 
$\forall p$ to this sentence results in a boolean that tracks the universalizability (or lack thereof) 
of the maxim. I chose my representation because it tracks the intuitive meaning of the universalizability 
test better: ``IF (the maxim is universalized) THEN (it is no longer effective)".

It's not clear to me if there's any intuitive difference between these two representations, but the lemmas 
below (using simplified versions of the representations) show that my representation is weaker than 
the representation where the quantifier has larger scope. This seems promising—the representation in 
lemma test\_2 is likely too strong because the quantifier quantifies into $M a$ as well. It really 
doesn't seem like this should make a difference, since $p$ never appears on the RHS expression. Let's
see if Prof. Amin has insight.\<close>

abbreviation imagine_a_world::"maxim\<Rightarrow>bool" where 
"imagine_a_world \<equiv> \<lambda>M. (\<exists>w. \<not> w = cw \<and> (\<forall>p. (W M p) w))"
\<comment>\<open>This abbreviation formalizes the idea that, for any maxim, some world where exist where the maxim 
is universally willed.\<close>

abbreviation not_contradictory::"maxim\<Rightarrow>bool" where 
"not_contradictory \<equiv> \<lambda>(c, a, g). (\<forall>p w. \<not> ((c \<^bold>\<and> (a p)) \<^bold>\<rightarrow> \<^bold>\<bottom>) w)"
\<comment>\<open>This abbreviation formalizes the idea of a non-contradictory maxim, defined as a maxim such that 
no matter who wills it at what world, the combination of the circumstances and the action never 
lead to a contradiction.\<close> 

text \<open>axiomatization where imagination_works:"$\forall$M::maxim.  (not_contradictory M) \<longrightarrow>  (imagine_a_world M)"\<close>
\<comment>\<open>This axiom says, effectively, that our imagination works. In other words, for every maxim, if it 
isn't contradictory, there is some (imagined) world where it is universalized. This guarantees that the 
FUL can't be vacuously true, since there is some world where the universalizability test is carried out.\<close>

lemma True
  nitpick[user_axioms, falsify=false] by simp 
\<comment>\<open>Asserting that we can successfully imagine a non-contradictory maxim to be universalized still results
in a consistent system.
$\color{blue}$ Nitpick found a model for card i = 1 and card s = 1:

  Empty assignment $\color{black}$\<close>
abbreviation not_universalizable_modal::"maxim\<Rightarrow>s\<Rightarrow>bool"
  where "not_universalizable_modal \<equiv> \<lambda>M s. (\<forall>w. \<forall>p. (W M p) w \<longrightarrow> \<not> E M s w)"

text \<open>To fix this, I return to the text of @{cite KorsgaardFUL}$\footnote{p. 20}$, in which she describes the universalizability 
test as taking place in an ``imagined" world where the maxim is universalized. In other words, the test
does not require that the maxim is actually universalized in reality in the current universe. Instead, 
we imagine that it is universalized in some parallel universe and study that alternate universe to 
understand what our obligations are in the real world. Under this reading, the maxim should be universalized
at some other world, and then we should decide whether or not it is obligatory at the current world. 

To formalize this, I will first add as an axiom the idea that every non-contradictory maxim is 
universalized at some world. In order for the test to actually be able to find a world where the 
maxim is universalized, we need to imagine that such a world exists. Practically, this axiom asserts
that we are able to successfully imagine a world where the maxim is universalized. Notice that this 
axiom can only hold for non-contradictory maxims, else we would have a world where a contradiction holds 
and the logic would become inconsistent! This coheres with basic moral intuitions as well—asking if 
a contradictory maxim is morally prohibited is, in effect, asking an incoherent question. Garbage in, garbage out!\<close>
end
(*>*)
