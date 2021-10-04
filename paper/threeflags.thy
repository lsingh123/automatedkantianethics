(*<*) theory threeflags
  imports paper41

begin(*>*)


text \<open>The literature on Kantian ethics is expansive and complicated. To focus my thesis on the contributions 
of automated ethics to Kantian thought, I make the following choices.

$\textbf{Choice to Formalize the FUL}$

I am only studying formalizations of Kant's first formulation of the categorical imperative,
the formula of universal law (FUL), because it is the most formal and thus the easiest to formalize and implement. 
Onora O'Neill @{cite actingonprinciple}\footnote{p. 33} explains that the formalism of the FUL allows 
for greater precision in philosophical arguments analyzing its implications and power. This precision 
is particularly useful in a computational context because any formalism necessarily makes its content 
precise. The FUL's existing precision reduces ambiguity, allowing me to remain faithful to Kant's writing and 
philosophical interpretations of it. Precision reduces the need to make choices to resolve debates 
and ambiguities. Some of these choices may be well-studied and grounded in literature, 
but some may be unique to formalizing the FUL and thus understudied. Minimizing these choices minimizes 
arbitrariness in my formalization and puts it on solid philosophical footing. Given that this thesis is a proof-of-concept, 
the formalism of the FUL is attractive because it reduces both the computational and philosophical complexity of my work. 

While some criticize the FUL for its formalism and percieved ``sterility" @{cite actingonprinciple}, 
Kantian constructivists embrace it. My project is not committed to Kantian constructivism; I argue that computational
ethics is a valuable tool for any ethicist, with a focus on general Kantian ethics. Nonetheless, Kantian constructivists may find the focus on 
the FUL particularly appealing. 

Though Kantians study all formulations of the categorical imperative, Kant argues in Groundwork 
that the three formulations of the categorical imperative are equivalent @{cite groundwork}. While this 
argument is disputed @{cite sepkant}, for those who believe it, the
stakes for my choice of the FUL are greatly reduced. If all formulations are equivalent, then a formalization of the FUL
lends the exact same power as a formalization of the second or third formulation of the categorical 
imperative. In fact, future work could formalize the other formulas and try to prove that they 
are identical. Kant believes that his argument for the equality of the formulas is analytical, and
if he is correct, it should be possible to recreate the argument in logic.

$\textbf{Definition of a Maxim}$

I define a maxim as a circumstance, act, goal tuple (C, A, G), read 
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
evaluating an agent's behavior, since that's when ``acting from duty" starts to matter.

$\textbf{Practical Contradiction Interpretation}$

Kantians debate the correct interpretation of the formula of universal law because Kant, 
at times, appears to interpret the universalizability test in different ways. My project uses Korsgaard's practical contradiction 
interpretation, broadly accepted as correct within the philosophical community @{cite ebelsduggan}\footnote{p. 177}.
Below, I briefly reconstruct Korsgaard's argument for the practical contradiction interpretation. While 
she believes that the text partially supports this interpretation, her argument is philosophical and 
derives its strength from the plausibility of the practical contradiction interpretation.

Recall that the formula of universal law is “act only in accordance with that maxim through which you can at the 
same time will that it become a universal law” @{cite groundwork}\footnote{(G: 4:421)}. To determine if a maxim can be willed as a 
universal law, one must use the “universalizability test,” which requires imagining a world in which 
everyone for all of time has willed the maxim. If willing the maxim in such a world generates a contradiction, 
then the action is prohibited. There are three interpretations of what sort of contradiction is necessary: 
(1) the teleological view, prohibiting actions that conflict with some assumed teleological end when 
universalized, (2) the logical contradiction view, prohibiting maxims that are logically impossible 
when universalized, and (3) the practical contradiction view, prohibiting maxims that are self-defeating 
when universalized.

Under the logical contradiction interpretation, falsely promising to repay a loan to get some quick cash
fails the universalizability test because, in such a world, the practice of promising would die out so 
making a false promise would be impossible. Korsgaard appeals to Dietrichson @{cite dietrichson} to construct the example of 
a mother killing her children that tend to cry more than average so that she can get some 
sleep at night. Universalizing this maxim does not generate a logical contradiction, but it is clearly 
morally wrong. The problem here is that killing is a natural action, which Korsgaard distinguishes from 
a practice, like promising. Natural actions will never be logically impossible, so the logical contradiction 
view fails to prohibit them.

Under the teleological contradiction interpretation, a maxim is prohibited if it undercuts some natural 
or assigned purpose for some practice, act, or object. For example, the purpose of promising is to 
create a system of mutual trust and false promising undercuts this purpose and is thus prohibited. The problem 
with this view is that it assumes that the agent is committed, either because of their own goals or 
because of some property of a rational will, to some teleological system. Acton formulates Hegel's argument that @{cite acton},
an agent doesn't have to be committed to promising as a system of mutual trust. Korsgaard concludes that 
assigning teleological purposes to actions is difficult because ``such purposes may have
nothing to do with what the agent wants or ought rationally to want, or even with what
any human being wants." If the agent is not committed to the purpose, then will not see a contradiction 
in willing an act that violates this purpose.

This difficulty with the teleological contradiction interpretation drives Korsgaard to look for purposes
that an agent must necessarily be committed to, and she concludes that this must be the purpose of the 
maxim itself. By willing a maxim, an agent commits themselves to the goal of the maxim, and thus cannot 
rationally will a system in which this goal is undercut. This system satisfactorily handles natural actions
like those of the sleep-deprived mother: in willing the end of sleeping through the night, she is 
implicitly willing that she be alive in order to secure and enjoy her sleep. If any mother is allowed to kill
any loud child, then she cannot be secure in the possession of her life, because her own mother may have 
grown frustrated with her crying. Her willing this maxim thwarts the end that she sought to secure. 

The practical contradiction interpretation not only addresses the problems with the first two 
interpretations, it also offers a much more satisfying explanation of why certain maxims are immoral. 
The problem is not the existence of a contradiction itself, but instead the fact that these maxims 
involve parasitic behavior on social conditions that the agent seeks to benefit from. The false promiser 
simultaneously wants to abuse the system of promising and benefit from it, and is thus making an exception 
of themselves. It is this kind of free-riding that the universalizability test seeks to draw out. The test
raises the same kinds of objections that the question ``What if everyone did that?" seeks to draw out.\<close>

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
