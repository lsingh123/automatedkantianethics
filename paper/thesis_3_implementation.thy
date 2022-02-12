(*<*) theory thesis_3_implementation
  imports  paper22 paper224

begin(*>*)

section \<open>Implementation Details\label{details}\<close>

text "In this section, I present the details of my implementation of automated Kantian ethics. I take
a logic-programming approach in which I formalize the FUL in Dyadic Deontic Logic and then implement 
this logic in Isabelle/HOl. I 
also present my testing framework, which demonstrates one way to evaluate how faithful an implementation
of automated ethics is to philosophical literature. This testing framework shows that my system outperforms
two other possible implementations of automated Kantian Ethics."

subsection "Formalization and Implementation of the FUL"

text \<open>Before formalizing the FUL, I must define and implement the relevant logical background. Dyadic
Deontic Logic can express obligation and prohibition, but it cannot represent more complex features of 
moral judgement like actions, subject, maxims, and ends. I augment DDL by adding representations 
of these concepts, drawn from philosophical literature.\<close>

subsubsection "Logical Background"

text\<open>Kantian ethics is centered on practical reason because it is action-guiding; the categorical
imperative is a moral rule that agents can use to decide between potential actions. Thus, before I even
begin to formalize a specific formulation of the categorical imperative, I must define the notions of 
subjects and actions. Concretely, I need to add logical background so that my logic can express sentences 
like, ``x does action.''\<close>

typedecl s \<comment>\<open>I declare a new type, $s$ as the type for a ``subject,'' i.e. the subject of a sentence.\<close>

text \<open>The \texttt{typedecl} keyword indicates that I am defining a new atomic type, which is not composed
of pre-existing types but is instead a new kind of thing altogether. I try to minimize the number of 
atomic types, so this will be one of the few new types that I define. To define a subject, it suffices
to declare a new type to represent a subject, as that is all that is needed to apply the Formula of
Universal Law. Notice that I have not defined any properties of this type, such as the idea that a subject
must be rational or human. Throughout my project, I will use bare syntactic units like types and constants 
to define new ideas and will add the minimum necessary definitions, or ``thin'' definitions, to achieve the desired results.
By avoiding complex definitions of a subject, I can avoid murky philosophical debates about the nature
of agency and reduce the potential for controversy or errors. 

In this interpretation, the defining feature of a subject is that it can act, a relatively uncontroversial
notion. I represent that below by allowing subjects to substitute into sentences, a property that I will use 
to represent the notion of different people performing certain actions.\<close>

type_synonym os = "(s \<Rightarrow> t)" \<comment>\<open>To model the idea of a subject being substituted into an action, I 
define \texttt{type\_synonym} $os$ for an open sentence. An open sentence takes as input a subject and 
returns a complete or ``closed'' DDL formula by, binding the free variable in the sentence to the input. 
For example, ``runs'' is an open sentence that can be instantiated with subject, ``Sara'' to create
the DDL term ``Sara runs,'' which can be true or false at a world. An open sentence itself is not
the kind of thing that can be true or false at a world, so it is not truth-apt, but when an action is 
substituted into an open sentence, the resulting term is truth apt. ``Runs'' is not the kind of thing 
that can be true or false, but ``Sara runs'' is a sentence that can be true or false.\<close>

subsubsection \<open>Maxim \label{whatisamaxim}\<close>

text\<open>Recall from Section \ref{whyful} that I formalize a version of the categorical imperative called
the Formula of Universal, which reads ``act only according to that maxim by which you can at the same 
time will that it should become a universal law'' \cite{groundwork}. In order to faithfully formalize
the FUL, I must make precise the notions of of ``willing a maxim'' and violating the FUL. I draw on 
reliable definitions of willing, maxims, and the FUL from Kantian literature and represent them in DDL.

The central unit of evaluation for Kantian ethics is a ``maxim,'' which Kant defines as ``the subjective 
principle of willing,'' or the principle that the agent understands themselves as acting on \cite{groundwork}. 
Modern Kantians differ in their interpretations of this definition. I adopt O'Neill's view, derived from 
Kant's example maxims, that a maxim includes the act, the circumstances, and the agent's purpose of 
acting or goal \citep{actingonprinciple}. 

\begin{definition}[Maxim]
    A maxim is a circumstance, act, goal tuple (C, A, G), read as ``In circumstances C, act A for goal G.''
\end{definition}

I implement this definition in Isabelle by defining the \texttt{type\_synonym} below for the type
of a maxim. 
\<close>

type_synonym maxim = "(t * os * t)"
\<comment>\<open>A maxim is of type term, open sentence, term tuple, such as ``(When I am broke, will falsely promise
to repay a loan, to get some easy cash)''. The first term represents the circumstance, which
can be true or false at a world. For example, the circumstance ``when I am broke'' is true at the real 
world when my bank account is empty. The second term represents the action, which is an open sentence
because different agents can perform a particular action. For example, the action, ``will falsely promise
to repay a loan'' is an open sentence that can be acted on by a subject. The third term represents 
the goal, which can again be true or false at a world. For example, the goal ``to get some easy cash''
is true at the real world if I have gotten easy cash. \<close>

text \<open>O'Neill \cite[37]{actingonprinciple} argues that maxim 
is an action-guiding rule and thus naturally includes an act and the circumstances under which 
it should be performed, which are often referred to as ``morally relevant circumstances'' \citep[37]{actingonprinciple}. 
She also includes a purpose, end, or goal in the maxim because human activity, is guided by a rational will, 
and is thus inherently purposive \citep[4:428]{groundwork}. A rational will does not act randomly (else it would not be rational), 
but instead in the pursuit of ends which it deems valuable\footnote{Some argue that a maxim should also
include the agent's motive or motivation and I address this concern in Appendix \ref{maximmotive}.}. The inclusion a maxim's end is essential for the version of the FUL
that I will implement, explained in Section Practical Contradiction.

\color{red} SHOULD THIS GO HERE OR IN THE LIMITATIONS SECTION OF THE DISCUSSION
O'Neill's inclusion of circumstances is potentially controversial because it leaves open the question of what qualifies as a 
relevant circumstance for a particular maxim. This is gives rise to ``the tailoring objection" \citep[217]{whatisamaxim} \footnote{Kitcher
cites \citet{kantsethicalthought} as offering an example of a false positive due to this objection.}, 
under which maxims are arbitrarily specified to pass the FUL. For example, the maxim ``When my name is Jane Doe,
I will lie to get some easy money," is universalizable, but is clearly a false positive. One solution to 
this problem is to argue that the circumstance ``When my name is Jane Doe" is not morally relevant 
to the act and goal. This solution requires determining what qualifies as a relevant circumstance.

O'Neill seems to acknowledge the difficulty of determining relevant circumstances when she concedes that a maxim cannot include all 
of the infinitely many circumstances in which the agent may perform an action \citep[4:428]{actingonprinciple}. She argues that this is 
an artifact of the fact that maxims are rules of practical reason, the kind of reason that helps us decide what to do 
and how to do it \citep{bok}. Like any practical rule, 
maxims require the exercise of practical judgement to determine in which circumstances they should be applied. 
This judgement, applied in both choosing when to exercise the maxim and in the formulation of the maxim 
itself, is what determines the morally relevant circumstances.

The difficulty in determining relevant circumstances is a limitation of my system and may require that a 
human being formulate the maxim or that future work develop heuristics to classify circumstances as morally 
relevant. For proponents of the ``human-in-the-loop'' model of AI ethics, in which ethical AI requires that 
humans guide machines, this kind of human involvement may be a feature \citep{loop}. In this model, 
a human being must create a representation for the dilemma they wish to test, translating 
a complex situation into a flat logical structure. This parallels the challenge that programmers 
face when translating the complexity of reality to a programming langauge or computational representation. 
The outcome of the universalizability test will depend on how the human formulates the maxim
and whether or not this formulation does indeed include morally relevant circumstances. If the human puts 
garbage into the test, the test will return garbage out.

Another solution to this problem may be to develop heuristics to classify circumstances as morally 
relevant. For example, one such attempt could define a moral closeness relation between an action, a 
goal, and circumstances. This heuristic would define morally relevant circumstance as those that 
reach a certain closeness threshhold with the action and the goal. Determining morally relevant
circumstances, either using heuristics or human involvement, is a ripe area for future work.
\color{black}

To will a maxim is to adopt it as a principle to live by, or to commit oneself to the action for the 
sake of the end in the relevant circumstances. Korsgaard argues that ``to will an end, rather than 
just wishing for it or wanting it, is to set yourself to be its cause" \cite[38]{sources}. I formalize
this idea in Definition \ref{willing}.

\begin{definition}[Willing]\label{willing}
For maxim $M = (C, A, G)$ and actor $s$,

$$will \, M \, s \equiv \forall w \, (C \longrightarrow A \, (s)) \, w$$

At all worlds $w$, if the circumstances hold at that world, agent $s$ performs act $A$.

\end{definition}

If I will the example maxim above about falsely promising to pay a loan, then whenever I need cash, 
I will falsely promise to repay a loan. I can represent this definition using the following Isabelle
formula.\<close>

abbreviation will :: "maxim \<Rightarrow> s\<Rightarrow>  t" ("W _ _")
  where "will \<equiv> \<lambda>(c, a, g) s. (c \<^bold>\<rightarrow> (a s))"
\<comment>\<open>An agent $s$ wills a maxim iff in the circumstances, $s$ performs the action, or $s$ substituted
into the open sentence $a$ is true. This is an Isabelle \texttt{abbreviation}, which is syntactic
sugar for an Isabelle formula. The type of this formula is $maxim \rightarrow s \rightarrow t$, so it 
takes as input a maxim and a subject and returns the term, ``s wills maxim.'' \<close>

subsubsection \<open>Practical Contradiction Interpretation \label{praccon}\<close>

text \<open>In order to actually evaluate the moral status of a maxim, I must precise the idea of failing
the universalizability test or a non-universalizable maxim.  Kantians debate the correct interpretation of 
the Formula of Universal Law because Kant himself appears to interpret the criterion in different ways. 
My project uses Korsgaard's practical contradiction interpretation, broadly accepted as correct within 
the philosophical community \citep{ebelsduggan}.
 
Recall that the Formula of Universal Law is to “act only in accordance with that maxim through which 
you can at the same time will that it become a universal law” \citep{groundwork}. To determine if a 
maxim can be willed as a universal law, we can use the “universalizability test”, which requires 
imagining a world in which everyone has willed the maxim. If willing the maxim in such a world 
generates a contradiction, then the action is prohibited. 

One interpretation of the FUL, the logical contradiction interpretation, prohibits maxims that are 
logically impossible when universalized. Under this view, falsely promising to repay a loan fails the 
universalizability test because, in the universalized world, the practice of promising would die out, 
so making a false promise would be impossible.

One problem with this view is that it cannot handle natural acts. Korsgaard appeals to 
\citet{dietrichson} to construct the example natural act of a mother killing her children that tend to 
cry at night so that she can get some sleep. Universalizing this maxim does not generate a logical 
contradiction, but it is clearly wrong. Because killing is a natural act, it can never be logically 
impossible so the logical contradiction view cannot prohibit it.

As an alternative to the logical contradiction view, Korsgaard endorses the practical contradiction view, 
which prohibits maxims that are self-defeating, or ineffective, when universalized. By willing a maxim, 
an agent commits themselves to the maxim's goal, and thus cannot rationally will that this goal be 
undercut. This interpretation can prohibit natural acts like those of the sleep-deprived mother: in 
willing the end of sleeping, she is implicitly willing that she is alive. If all mothers kill all 
loud children, then she cannot be secure in the possession of her life, because her own mother would 
have killed her as an infant. Her willing this maxim thwarts the end that she sought to secure. 

The practical contradiction interpretation offers a satisfying explanation of \emph{why} certain 
maxims are immoral. These maxims involve parasitic behavior on social conditions that the agent seeks 
to benefit from. The false promiser simultaneously wants to abuse the system of promising and benefit 
from it, and is thus making an exception of themselves. The test formalizes the kinds of objections 
that the question ``what if everyone did that?'' seeks to draw out.

Using the practical contradiction interpretation, the FUL states, ``If, when universalized, a maxim is 
not effective, then it is prohibited.'' This requires defining effectiveness and universalization. 
If an agent wills an effective maxim, then the maxim's goal is achieved, and if the agent does 
not will it, then the goal is not achieved. 

\begin{definition}[Effective Maxim]
For a maxim $M = (C, A, G)$ and actor $s$,

$$\text{\emph{effective}} \, M \, s \equiv \forall w \, (\text{\emph{will}} \, (C, A, G) \, s \iff G) \, w$$

\end{definition}

I can implement this in Isabelle using another abbreviation.
\<close>

abbreviation effective :: "maxim\<Rightarrow>s\<Rightarrow> t" ("E _ _")
  where "effective  \<equiv> \<lambda>(c, a, g) s. ((will (c, a, g) s) \<^bold>\<equiv> g)"
\<comment>\<open>A maxim is effective for a subject if the goal is achieved if and only if the subject wills the maxim.
Once again, I use an abbreviation to conveniently refer to this Isabelle formula.\<close>

text \<open>The former direction of the implication is intuitive: if the act results in the goal, it was 
effective in causing the goal. This represents sufficient causality. The latter direction represents 
necessary causality, or the idea that, counterfactually, if the maxim were not willed, then the goal 
would not be achieved \citep{lewiscausality}.\footnote{Thank you for Jeremy Zucker for helping me 
think about causality in this way.}  Note that nothing else changes about this
counterfactual world—the circumstances are identical and we neither added additional theorems nor 
specified the model any further. This represents Lewis's idea of "comparative similarity,"  where 
a counterfactual is true if it holds at the most similar world @{cite lewiscounterfactuals}. 
In our case, this is just the world where everything is the same except the maxim is not acted on.
Combining these ideas, this definition of effective states that a maxim is effective if the 
maxim being acted on by a subject is the necessary and sufficient cause of the goal.\<close>

abbreviation universalized::"maxim\<Rightarrow>t" where 
"universalized \<equiv> \<lambda>M. (\<lambda>w. (\<forall>p. (W M p) w))"

abbreviation holds::"maxim\<Rightarrow>t" where 
"holds \<equiv> \<lambda>(c, a, g). c"

abbreviation not_universalizable :: "maxim\<Rightarrow>s\<Rightarrow>bool" where 
"not_universalizable \<equiv> \<lambda>M s. \<forall>w. ((universalized M)  \<^bold>\<rightarrow> (\<^bold>\<not> (E M s))) w"
\<comment>\<open>The formula above reads ``at world $w$, if M is universalized and M is acted on (i.e. the circumstances 
of M hold), then M is not effective." 
Notice that the antecedent specifies that the circumstances hold at the given world. 
When evaluating if a maxim is universalizable or not, we want to ignore worlds where the circumstance 
do not hold. At these worlds, the maxim is trivially effective and thus trivially universalizable. If we didn't exclude such worlds from 
consideration, a maxim with circumstances that ever fail to hold would be universalizable. Clearly 
this is not a desirable conclusion, since maxims like ``When you need money, lie to get easy money"
would be universalizable.  \<close>

text \<open>As before, the concepts of prohibition and permissibility will be helpful here. The unit of 
evaluation for my formalization of the FUL is the act of willing a maxim, which entails performing 
the maxim's act in the relevant circumstances. Therefore, I will say that, just as the act of willing a
 maxim can be obligatory for a subject, it can be prohibited or permissible for a subject.\footnote{In 
the rest of this section, for convenience, I will use the phrase ``subject s willing maxim M is obligatory" 
interchangeably with ``maxim M is obligatory for subject s." I will use ``maxim M is obligatory" to 
refer to M being obligatory for any arbitrary subject, which I will show to be equivalent to M being 
obligatory for a specific subject.} \<close>

abbreviation prohibited::"maxim\<Rightarrow>s\<Rightarrow>t" where 
"prohibited \<equiv> \<lambda>(c, a, g) s. O{\<^bold>\<not> (will (c,a, g) s) | c}"

abbreviation permissible::"maxim\<Rightarrow>s\<Rightarrow>t"
  where "permissible \<equiv> \<lambda>M s. \<^bold>\<not> (prohibited M s)"
\<comment>\<open>I will say that a maxim is permissible for a subject if it is not prohibited for that subject to 
will that maxim. \<close>

text \<open>
When analyzing the naive formalization and Kroy's formalization, I learned that DDL and the prior 
formalizations allow contradictory obligations. This is a major weakness of these systems, and my 
formalization should fix this. To do so, I will add as an axiom the idea that obligations cannot 
contradict each other or their internal circumstances. Formally, conflicting obligations are defined below. \<close>

abbreviation non_contradictory where 
"non_contradictory A B c w \<equiv> ((O{A|c} \<^bold>\<and> O{B|c}) w) \<longrightarrow> \<not>((A \<^bold>\<and> (B \<^bold>\<and> c)) w \<longrightarrow> False)"
\<comment>\<open>Terms A and B are non contradictory in circumstances c if, when A and B are obligated in circumstances 
c, the conjunction of A, B, and c, does not imply False. \<close>

axiomatization where no_contradictions:"\<forall>A::t. \<forall>B::t. \<forall>c::t. \<forall>w::i. non_contradictory A B c w"
\<comment>\<open>This axiom formalizes the idea that, for any terms A, B, and circumstances c, A and B must be 
non-contradictory in circumstances c at all worlds. Intuitively, this axiom requires that obligations 
do not conflict. \<close>

subsection "Formalizing the FUL"

text \<open> Below is my first attempt at formalizing Korgsaard's definition of the practical contradiction
interpretation:  a maxim is not universalizable 
if, in the world where the maxim becomes the standard practice (i.e. everyone acts on the maxim), the
agent's attempt to use the maxim's act to achieve the maxim's goal is frustrated. In other words, if 
the maxim is universally willed (captured by applying a universal qunatifier and the will function 
to the maxim on the LHS), then it is no longer effective for the subject $s$ (RHS above). 
\<close>

abbreviation FUL0::bool where "FUL0 \<equiv> \<forall> c a g s. not_universalizable (c, a, g) s \<longrightarrow> \<Turnstile>((prohibited (c, a, g) s))"
\<comment>\<open>This representation of the Formula of Universal Law reads, ``For all circumstances, goals, acts, 
and subjects, if the maxim of the subject performing the act for the goal in the circumstances is not 
universalizable (as defined above), then, at all worlds, in those circumstances, the subject 
is prohibited (obligated not to) from willing the maxim.\<close>

lemma "FUL0 \<longrightarrow> False" using O_diamond
  using case_prod_conv no_contradictions old.prod.case old.prod.case by fastforce
  
text \<open>FUL0 is not consistent, and sledgehammer is able to prove this by showing that it implies a contradiction 
usig axiom O\_diamond, which is @{"thm" "O_diamond"}. This axiom captures 
the idea that an obligation can't contradict its context. This is particularly problematic if the goal or 
action of a maxim are equivalent to its circumstances. In other words, if the maxim has already been 
acted on or the goal has already been achieved, then prohibiting it is impossible. 
In any model that has at least one term, it is possible to construct a maxim where the circumstances, goal, 
and act (once a subject acts on it) are all that same term, resulting in a contradiction. 

To get around this, I will exclude what I call ``badly formed maxims," which are those maxims such that the goal has already been 
achieved or the act has already been acted on. Under my formalization, such maxims are 
not well-formed. To understand why, I return to Korsgaard's and O'Neill's interpretations of a maxim as a practical
guide to action. A maxim is a practical principle that guides how we behave in everyday life. A 
principle of the form ``When you are eating breakfast, eat breakfast in order to eat breakfast," is not 
practically relevant. No agent would ever need to act on such a principle. It is not contradictory
or prohibited, but it is the wrong kind of question to be asking. It is not a 
well-formed maxim, so the categorical imperative does not apply to it. (more explanation in philosophical 
writing collection)\<close>

abbreviation well_formed::"maxim\<Rightarrow>s\<Rightarrow>i\<Rightarrow>bool" where 
"well_formed \<equiv> \<lambda>(c, a, g). \<lambda>s. \<lambda>w. (\<not>  (c \<^bold>\<rightarrow> g) w) \<and> (\<not>  (c \<^bold>\<rightarrow> a s) w)"
\<comment>\<open>This abbreviation formalizes the well-formedness of a maxim for a subject. The goal cannot be 
already achieved in the circumstances and the subject cannot have already performed the act.\<close>

abbreviation FUL where 
"FUL \<equiv> \<forall>M::maxim. \<forall>s::s. (\<forall>w. well_formed M s w) \<longrightarrow> (not_universalizable M s \<longrightarrow> \<Turnstile> (prohibited M s) )"
\<comment>\<open>Let's try the exact same formalization of the FUL as above, except that it only applies to 
maxims that are well-formed at every world.\<close>

lemma "FUL"
  nitpick[user_axioms, falsify=true] oops
\<comment>\<open>The FUL does not hold in DDL, because nitpick is able to find a model for my system in which it is 
false. If the FUL were already a theorem of the system, adding it wouldn't make the system any more 
powerful, so this is the desired result.

$\color{blue}$ Nitpick found a counterexample for card s = 1 and card i = 1:

  Skolem constants:
    M = (($\lambda x. \_$)($i_1$ := True), ($\lambda x. \_$)($s_1$ := ($\lambda x. \_$)($i_1$ := False)), ($\lambda x. \_$)
         ($i_1$ := False))
    $\lambda$ w. p = ($\lambda x. \_$)($i_1$ := $s_1$)
    s = $s_1$ $\color{black}$ \<close>

axiomatization where FUL:FUL

lemma True
  nitpick[user_axioms, falsify=false] by simp
\<comment>\<open>Nitpick is able to find a model in which all axioms are satisfied, 
so this version of the FUL is consistent.

$\color{blue}$ Nitpick found a model for card i = 1 and card s = 1:

  Empty assignment $\color{black}$ \<close>

text \<open>During the process of making FUL0 consistent, I used Isabelle to gain philosophical insights 
about vacuous maxims. This process is an example of the power of computational tools to aid
philosophical progress. I used Nitpick and Sledgehammer to quickly test if a small tweak 
to FUL0 fixed the inconsistency or if I was still able to derive a contradiction.  I then realized that if 
I defined the circumstances, act, and goal as constants, then FUL0 was indeed consistent. After some 
experimentation, Prof. Amin correctly pointed out that as constants, these three entities were 
distinct. However, when merely quantifying over (c, a, g), all members of a tuple could be equivalent. Within
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
theoretical math to understand the mathematical objects they model.\<close>

text \<open>One potential problem with my formalization is that it does not use the modal nature of the system. 
All of the properties that the FUL investigates hold at all worlds, in effect removing the modal nature 
of the system. This approach simplifies logical and therefore computational complexity, improving 
performance. On the other hand, it doesn't use the full expressivity of DDL. If I run into problems 
later on, one option is to tweak the FUL to use this expressivity. \<close> 

end
(*>*)

