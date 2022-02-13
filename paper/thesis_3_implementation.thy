(*<*) theory thesis_3_implementation
  imports  paper22 paper224

begin(*>*)

section \<open>Implementation Details\label{details}\<close>

text "In this section, I present the details of my implementation of automated Kantian ethics. I first 
formalize the FUL in Dyadic Deontic Logic and then implement this logic in Isabelle/HOl. I 
also present a testing framework that can evaluate how faithful an implementation
of automated ethics is to philosophical literature. This testing framework shows that my system outperforms
two other possible implementations of automated Kantian ethics."

subsection "Formalization and Implementation of the FUL"

text \<open>Before formalizing the FUL, I must define and implement the relevant logical background. Dyadic
Deontic Logic can express obligation and prohibition, but it cannot represent more complex features of 
moral judgement like actions, subject, maxims, and ends. I augment DDL by adding representations 
of these concepts, drawn from philosophical literature.\<close>

subsubsection "Logical Background"

text\<open>Kantian ethics is centered on practical reason because it is action-guiding; the categorical
imperative is a moral rule that agents can use to decide between potential actions. Thus, before I 
begin to formalize a specific formulation of the categorical imperative, I must define the notions of 
subjects and actions. I need to add logical background so that my logic can express sentences 
of the form, ``x does action.''\<close>

typedecl s \<comment>\<open>I declare a new type $s$ as the type for a ``subject,'' as in the subject of a sentence.\<close>

text \<open>The \texttt{typedecl} keyword indicates that I am defining a new atomic type, which is not composed
of pre-existing types but is instead a new kind of object altogether. To define a subject, it suffices
to declare a new type to represent a subject without specifying any of its complex properties, such as the idea that a subject
must be rational or human. Instead of providing a complete definition of subject, which would require wading into murky
philosophical debates about the nature of agency, I will provide a ``thin'' definition which includes
only the minimum necessary properties to apply the FUL. Throughout my project, I will use bare syntactic units like types and constants
to define new ideas and will add thin definitions to achieve the desired results.

In this interpretation, it suffices to make the defining feature of a subject that it can act. 
I represent that below by allowing subjects to substitute into sentences, a property that I will use 
to represent the idea that different people can perform the same actions.\<close>

type_synonym os = "(s \<Rightarrow> t)" 
\<comment>\<open>To model the idea of a subject being substituted into an action, I 
define \texttt{type\_synonym} $os$ for an open sentence. An open sentence takes as input a subject and 
returns a complete or ``closed'' DDL formula by binding the free variable in the sentence to the input. 
For example, ``runs'' is an open sentence that can be instantiated with subject, ``Sara'' to create
the DDL term ``Sara runs,'' which can be true or false at a world. An open sentence itself is not truth-apt,
ot the kind of thing that can be true or false at a world. When an action is 
substituted into an open sentence, the resulting term is truth apt. ``Runs'' is not the kind of thing 
that can be true or false, but ``Sara runs'' is a sentence that can be true or false.\<close>

subsubsection \<open>Maxim \label{whatisamaxim}\<close>

text\<open>Recall from Section \ref{whyful} that I formalize a version of the categorical imperative called
the Formula of Universal, which reads ``act only according to that maxim by which you can at the same 
time will that it should become a universal law'' \citep{groundwork}. In order to faithfully formalize
the FUL, I must make precise what it means to will a maxim and violate the FUL. I draw on 
reliable definitions of willing, maxims, and the FUL from Kantian literature and represent them in DDL.
Throughout this section, I will use one of Kant's most famous maxims as an example to demonstrate
my formalization.

\begin{example}[False Promising]\label{falsepromise}
  The false promising example maxim reads, ``When I am broke, I wil falsely promise to repay a loan 
to get some easy cash.''
\end{example}

The central unit of evaluation for Kantian ethics is a ``maxim,'' which Kant defines as ``the subjective 
principle of willing,'' or the principle that the agent understands themselves as acting on \citep{groundwork}. 
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
but instead in the pursuit of ends which it deems valuable.\footnote{Some argue that a maxim should also
include the agent's motive or motivation and I address this concern in Appendix \ref{maximmotive}.} The inclusion a maxim's end is essential for the version of the FUL
that I will implement, explained in Section Practical Contradiction.

\color{red} SHOULD THIS GO HERE OR IN THE LIMITATIONS SECTION OF THE DISCUSSION

O'Neill's inclusion of circumstances is potentially controversial because it leaves open the question of what qualifies as a 
relevant circumstance for a particular maxim. This is gives rise to ``the tailoring objection", 
under which maxims are arbitrarily specified to pass the FUL  \citep[217]{whatisamaxim}. \footnote{Kitcher
cites \citet{kantsethicalthought} as offering an example of a false positive due to this objection.} For example, the maxim ``When my name is Jane Doe
and I am wearing a purple shirt and it is Tuesday morning, I will murder my boss so I can take their job," 
is universalizable but is clearly a false positive because we think that murder for professional gain is wrong. 
One solution to this problem is to argue that the circumstance ``When my name is Jane Doe and I am wearing a 
purple shirt and it is Tuesday morning" is not morally relevant 
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
goal, and circumstances. This heuristic would define morally relevant circumstances as those that 
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

If I will example \nameref{falsepromise} maxim about falsely promising to pay a loan, then whenever I need cash, 
I will falsely promise to repay a loan. I can represent this definition using the following Isabelle
formula.\<close>

abbreviation will :: "maxim \<Rightarrow> s\<Rightarrow>  t" ("W _ _")
  where "will \<equiv> \<lambda>(c, a, g) s. (c \<^bold>\<rightarrow> (a s))"
\<comment>\<open>An agent $s$ wills a maxim if in the circumstances, $s$ performs the action, or $s$ substituted
into the open sentence $a$ is true. This is an Isabelle \texttt{abbreviation}, which is syntactic
sugar for an Isabelle formula. The type of this formula is $maxim \rightarrow s \rightarrow t$, so it 
takes as input a maxim and a subject and returns the term, ``s wills maxim.'' \<close>

subsubsection \<open>Practical Contradiction Interpretation of the FUL \label{praccon}\<close>

text \<open>In order to evaluate the moral status of a maxim, I must precise the idea of failing
the universalizability test or a non-universalizable maxim.  Kantians debate the correct interpretation of 
the Formula of Universal Law because Kant himself appears to interpret the criterion in different ways. 
My project uses Korsgaard's practical contradiction interpretation, broadly accepted as correct within 
the philosophical community \citep{ebelsduggan}.
 
Recall that the Formula of Universal Law is to “act only in accordance with that maxim through which 
you can at the same time will that it become a universal law” \citep{groundwork}. To determine if a 
maxim can be willed as a universal law, we can use the “universalizability test”, which requires 
imagining a world in which everyone has willed the maxim. If willing the maxim in such a world 
generates a contradiction, then the action is prohibited. In the case of the example maxim about 
lying to 

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
that the question ``What if everyone did that?'' seeks to draw out.

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
a counterfactual is true if it holds at the most similar world \citep{lewiscounterfactuals}. 
In our case, this is just the world where everything is the same except the maxim is not acted on.
Combining these ideas, this definition of effective states that a maxim is effective if the 
maxim being acted on by a subject is the necessary and sufficient cause of the goal.

Next, I define what it means for a maxim to be universalized. Recall that the universalizability 
test requires imagining a world in which everyone wills a maxim. Therefore, a maxim is universalized
when everyone wills the maxim. 

\begin{definition}[Universalized]
  For a maxim $M$ and agent $s$,

  $$\text{\emph{universalized}} \, M  \equiv \forall w \, (\forall p \, \text{\emph{will}} \, M \, p)$$
\end{definition}

I can once again represent this as an abbreviation in Isabelle.
\<close>

abbreviation universalized::"maxim\<Rightarrow>t" where 
"universalized \<equiv> \<lambda>M. (\<lambda>w. (\<forall>p. (W M p) w))"
\<comment>\<open>The abbreviation $universalized$ takes a maxim as input and returns a term which is true at a world 
if all people at that world will the maxim.\<close>

(*<*)
abbreviation holds::"maxim\<Rightarrow>t" where 
"holds \<equiv> \<lambda>(c, a, g). c"(*>*)

text \<open>With the above definitions of effective and universalization, I can define what it means for 
a maxim to not be universalizable. This is the core of the FUL; it states that if a maxim is not 
universalizable, it is prohibited. The practical contradiction interpretation states that a  maxim is 
not universalizable if, when universalized, it is no longer effective.

\begin{definition}[Not Universalizable]
For a maxim $M$ and agent $s$,

$$not\_universalizable \, M \, s  \equiv [ \text{\emph{universalized}} M \longrightarrow \neg \, \text{\emph{effective}} \, M \, s ]$$

A maxim is not universalizable when, if everyone wills the maxim, then it is no longer effective.
\end{definition}

I implement this definition in Isabelle using another abbreviaion.\<close>

abbreviation not_universalizable :: "maxim\<Rightarrow>s\<Rightarrow>bool" where 
"not_universalizable \<equiv> \<lambda>M s. \<forall>w. ((universalized M)  \<^bold>\<rightarrow> (\<^bold>\<not> (E M s))) w"
\<comment>\<open>The formula above reads ``at world $w$, if M is universalized, then M is not effective.'' \<close>

text \<open>The final set of definitions necessary to implement the FUL are obligation, permissibility, 
and prohibition. To judge an action, my system evaluates the moral status of the action 
``person $s$ wills maxim $M$.'' This action can be obligated, prohibited, or permissible.
I will use the phrase ``subject s willing maxim M is obligatory" 
interchangeably with ``maxim M is obligatory for subject s." I will use ``maxim M is obligatory" to 
refer to M being obligatory for any arbitrary subject, which I is equivalent to M being 
obligatory for a specific subject.\footnote{The full proof for this result is in Appendix Extra Tests}. 

\begin{definition}[Obligation]

Let maxim $M$ be composed of the circumstances, act, goal tuple $C, A, G$ and let $s$ be an arbitrary agent.

$$obligated \, M \, s \equiv O\{ will \, (C, A, G) \, s \, | \, C\}$$

\end{definition}

The action ``$s$ wills $M$'' is the first argument passed to the dyadic obligation operator and is 
thus the action that is shown to be obligated or not. The second argument passed to the obligation 
operator represents the context in which the obligation holds and is thus naturally the maxim's circumstances.
This definition does not require any additional syntactic sugar, since it merely uses the dyadic obligation
operator in a clever way. Using this definition, I can define prohibition and permissibility.

\begin{definition}[Prohibition and Permissibility] Let maxim $M$ be composed of the circumstances, act, 
goal tuple $C, A, G$ and let $s$ be an arbitrary agent.\footnote{Technically, a maxim is not a boolean 
type, so the term $\neg M$ is not type correct. The expression $obligated \, \neg M$ merely provides 
intuition for the meaning of prohibition, but the exact definition is given by 
$O\{ \neg will \, (C, A, G) \, s \, | \, C\}$.}

\newcommand*{\approxident}{%
  \mathrel{\vcenter{\offinterlineskip
  \hbox{$\sim$}\vskip-.35ex\hbox{$\sim$}\vskip-.35ex\hbox{$\sim$}}}}

$$ prohibited \, M \, s \approxident obligated \, \neg M \, \equiv O\{ \neg will \, (C, A, G) \, s \, | \, C\}$$

$$permissible \, M \, s \equiv \neg prohibited \, M \, s \equiv \neg O\{ \neg will \, (C, A, G) \, s \, | \, C\}$$

\end{definition} 

Once again, I represent these definitions as abbreviations in Isabelle.\<close>

abbreviation prohibited::"maxim\<Rightarrow>s\<Rightarrow>t" where 
"prohibited \<equiv> \<lambda>(c, a, g) s. O{\<^bold>\<not> (will (c,a, g) s) | c}"
\<comment>\<open>A maxim is prohibited for a subject $s$ if its negation is obligated for $s$. It is morally wrong 
for an agent to will a prohibited maxim. \<close>

abbreviation permissible::"maxim\<Rightarrow>s\<Rightarrow>t"
  where "permissible \<equiv> \<lambda>M s. \<^bold>\<not> (prohibited M s)"
\<comment>\<open>A maxim is permissible for a subject $s$ if it is not prohibited for $s$. It is morally acceptable 
for an agent to will or not will a permissible maxim. \<close>

text \<open>One additional piece of logical background necessary before I implement the FUL is the 
notion of contradictory obligations. Many deontic logics, including DDL, allow contradictory
obligations. As I will explain in Section Tests, Kantian ethics never prescribes contradictory
obligations, so I will add this as an axiom. \<close>

abbreviation non_contradictory where 
"non_contradictory A B c w \<equiv> ((O{A|c} \<^bold>\<and> O{B|c}) w) \<longrightarrow> \<not>((A \<^bold>\<and> (B \<^bold>\<and> c)) w \<longrightarrow> False)"
\<comment>\<open>Terms $A$ and $B$ are non contradictory in circumstances $c$ if, when $A$ and $B$ are obligated in circumstances 
$c$, the conjunction of $A$, $B$, and $c$, does not imply $False$. \<close>

axiomatization where no_contradictions:"\<forall>A::t. \<forall>B::t. \<forall>c::t. \<forall>w::i. non_contradictory A B c w"
\<comment>\<open>This axiom formalizes the idea that, for any terms $A$, $B$, and circumstances $c$, $A$, and $B$ must be 
non-contradictory in circumstances $c$ at all worlds. Intuitively, this axiom requires that obligations 
do not conflict. \<close>

subsubsection "Formalizing the FUL"

text \<open>With this logical background, I can begin to implement the Formula of Universal Law, as defined 
by the practical contradiction interpretation, which states that a maxim is prohibited if it is ineffective
when universalized. A first attempt to formalize the FUL simply translates this into Isabelle's syntax
using the abbreviations above.
\<close>

abbreviation FUL0::bool where "FUL0 \<equiv> \<forall> c a g s. not_universalizable (c, a, g) s \<longrightarrow> \<Turnstile>((prohibited (c, a, g) s))"
\<comment>\<open>This representation of the Formula of Universal Law reads, ``For all circumstances, goals, acts, 
and subjects, if the maxim of the subject performing the act for the goal in the circumstances is not 
universalizable (as defined above), then, at all worlds, in those circumstances, the subject 
is prohibited (obligated not to) from willing the maxim.''\<close>

text\<open>I can immediately determine if this version of the FUL is sensical by checking if it is consistent.
If \texttt{FUL0} implies False, then it is inconsistent.\<close>

lemma "FUL0 \<longrightarrow> False" using O_diamond
  using case_prod_conv no_contradictions old.prod.case old.prod.case by fastforce
  
text \<open>FUL0 is not consistent, and Isabelle's proof-finding tool, Sledgehammer, is able to prove this by showing that it implies a contradiction 
usig axiom \texttt{O\_diamond}\footnote{The full axiom reads @{"thm" "O_diamond"}.} \citep{sledgehammer}. 
This axiom captures the idea that an obligation can't contradict its context. This is particularly problematic 
if the goal or action of a maxim are equivalent to its circumstances. In other words, if the maxim has already been 
acted on or the goal has already been achieved, then prohibiting it is impossible. 
In any model that has at least one term, it is possible to construct a maxim where the circumstances, goal, 
and act (once a subject acts on it) are all that same term, resulting in a contradiction. 

This motivates the exclusion of what I call ``badly formed maxims," which are those maxims such that 
the goal has already been achieved or the act has already been acted on. Under my formalization, such maxims are
not well-formed. 

\begin{definition}[Well-Formed Maxim]
A maxim is well-formed if the circumstances do not contain the act and goal. For a maxim $(C, A, G)$, and subject $s$, 
$$ \text{\emph{well\_formed}} \, (C, A, G) \, s \equiv \forall w \, (\neg (C \longrightarrow G) \wedge \neg (C \longrightarrow A \, s)) \, w$$

\end{definition}

For example, the maxim ``When I eat breakfast, I will eat breakfast to eat breakfast'' is not well-formed 
because the circumstance ``when I eat breakfast'' contains the act and goal. Well-formedness is not 
discussed in the literature, but if I require that the FUL only holds for well-formed maxim, it will now
be consistent.\<close>

abbreviation well_formed::"maxim\<Rightarrow>s\<Rightarrow>i\<Rightarrow>bool" where 
"well_formed \<equiv> \<lambda>(c, a, g). \<lambda>s. \<lambda>w. (\<not>  (c \<^bold>\<rightarrow> g) w) \<and> (\<not>  (c \<^bold>\<rightarrow> a s) w)"
\<comment>\<open>This abbreviation formalizes the well-formedness of a maxim for a subject. The goal cannot be 
already achieved in the circumstances and the subject cannot have already performed the act.\<close>

text\<open>If I modify \texttt{FUL0} to only hold for well-formed maxims, it becomes consistent.\<close>

abbreviation FUL where 
"FUL \<equiv> \<forall>M::maxim. \<forall>s::s. (\<forall>w. well_formed M s w) \<longrightarrow> (not_universalizable M s \<longrightarrow> \<Turnstile> (prohibited M s) )"
\<comment>\<open>This formalization states that if a maxim is well-formed, then if it is not universalizable, 
it is prohibited.\<close>

lemma "FUL"
  nitpick[user_axioms, falsify=false] oops
\<comment>\<open>Nitpick is Isabelle's countermodel checker, and I can use it to quickly check that an axiom is 
consistent \citep{nitpick}. If Nitpick can find a model in which the axioms of DDL hold and the FUL is 
true then it is consistent.
$\color{blue}$ Nitpick found a model for card $i$ = 1 and card $s$ = 2:

  Empty assignment $\color{black}$ \<close>

text \<open>Above, I used Isabelle and my logic to show that if the FUL holds for badly formed maxims then 
it is inconsistent. This is not just a logical property of my system, but it also has philosophical
significance that coheres with Korsgaard's and O'Neill's interpretations of a maxim as a practical
guide to action \citep{actingforareason,actingonprinciple}. A maxim is a practical principle that guides how we behave in everyday life. A 
principle of the form ``When you are eating breakfast, eat breakfast in order to eat breakfast,'' is not 
practically relevant. No agent would ever need to act on such a principle. It is neither contradictory
nor prohibited, and it is the wrong kind of question to be asking. It is not a 
well-formed maxim, so the categorical imperative cannot apply to it. 

The fact that Isabelle revealed a philosophical insight about which kinds of maxims are well-formed
enough to evaluate using the categorical imperative is an example of the power of computational tools to aid
philosophical progress. Nitpick and Sledgehammer helped me confirm that certain kinds
of circumstance, act, goal tuples are too badly formed for the categorical imperative to logically 
apply to them. The realization of this subtle problem would have been incredibly difficult without 
computational tools, and serves as evidence of the power of computational ethics. I discuss the philosophical
properties and implications of well-formed maxims and the power of computational ethics further in
Chapter Discussion in Section Computational Ethics.

Now that I have a consistent version of the FUL, I can complete my implementation by adding it as an axiom.\<close>

axiomatization where FUL:FUL

text\<open>This concludes my implementation of the Formula of Universal Law in Isabelle/HOL. My implementation
consistents of necessary logical background, first formalized in DDL and then implemented in Isabelle.
The code snippets in this chapter are a subset of the over 100 lines of Isabelle/HOL code necessary to
complete this implementation. In Section \nameref{testing} and Chapter Applications, I demonstrate how this
implementation can be tested and used to make moral judgements.\<close>

subsection \<open>Tests\label{testing}\<close>

text \<open>In addition to an implementation of automated Kantian ethics, I also contribute a testing framework 
to evaluate how well my implementation coheres with philosophical literature. This testing architecture 
makes the notion of ``philosophical faithfulness'' precise. Each test consists of a sentence in my logic 
and an expected outcome, where the possible outcomes are proving or refuting the sentence. For example, 
one such sentence is that obligations cannot contradict each other. To run the tests, I attempt to
 prove or refute each test sentence in my logic.  Because these tests are derived from moral 
intuition and philosophical literature, they evaluate how reliable my system is.

The test framework can be expanded by adding more test sentences. This test framework can also guide 
implementations of other parts of Kantian ethics or other ethical theories. As I was implementing my 
formalization, I checked it against the testing framework, performing test-driven development automated 
ethics. Running the tests on my implementation alone consisted of approximately 400 lines of Isabelle code.

I use my testing framework to show that my formalization and implementation of Kantian ethics outperforms 
raw DDL with no other axioms added (a control group) and Kroy's prior attempt at formalizing 
(but not implementing) the FUL, which I implement\footnote{I present the complete implementation in 
Appendix \nameref{kroy_appendix}} in Isabelle \citep{kroy}. My implementation outperforms 
both other implementations. Full test results are summarized in Figure \ref{table}. Below, I briefly 
explain some noable tests. 
\<close>

text_raw \<open>
\begin{figure}
\centering
\includegraphics[scale=0.4]{goalstable.png}
\caption{Table showing which tests each implementation passes. The naive interpretation is raw DDL, 
Kroy is based on Moshe Kroy's formalization of the FUL, and the custom formalization is my novel implementation.} \label{table}
\end{figure}\<close>

text \<open>\textbf{FUL Stronger than DDL} The FUL should not hold in raw DDL, which I use a control group. 
If the FUL holds in the base logic, then adding it as an axiom doesn't make the logic any stronger, 
which is troubling because the base logic does not come equipped with the categorical imperative built-in. It 
defines basic properties of obligation, such as ought implies can, but contains no axioms that represent
the formula of universal law. Therefore, if a formalization of the FUL holds in the 
base logic, then it is too weak to actually represent the FUL. Both Kroy's formalization
and my implementation do not hold in the base logic, and thus represent some progress over the control group.
To test this property, I used Nitpick to find a countermodel in which my version of the FUL does not hold. 
I performed this test before adding the FUL as an axiom, since after adding it no countermodel will
be possible.\<close>

text \<open>\medskip
\noindent \textbf{Obligation Universalizes Across People} The obligations prescribed by the Formula of Universal Law
should generalize across people. In other words, if a maxim is obligated for one person, it is obligated
for all other people because maxims are not person-specific. Velleman argues that, because 
reason is accessible to everyone identically, obligations apply to all people equually \citep[25]{velleman}. 
When Kant describes the categorical imperative as the objective principle of the will, he is referring 
to the fact that, as opposed to a subjective principle, the categorical imperative applies to all 
rational agents equally \citep[16]{groundwork}. At its core, the FUL best handles, ``the temptation 
to make oneself an exception: selfishness, meanness, advantagetaking, and disregard for the rights 
of others'' \citep[30]{KorsgaardFUL}. Kroy makes this property the center of his
formalization, which essentially says that if an act is permissible for someone, it is permissible for 
everyone.\footnote{Formally, $P\{A(s)\} \longrightarrow \forall p. P\{A(p)\}$} Kroy's interpretation and 
my interpretation satisfy this property, but the naive interpretation does not. Below I show how I 
ran this test for my interpreation.\<close>

lemma wrong_if_wrong_for_someone:
  shows "\<forall>w. \<forall>c::t. \<forall>g::t. \<forall>a. \<exists>s::s. O{\<^bold>\<not> (W (c, a, g) s) | c} w \<longrightarrow> (\<forall>p.  O{\<^bold>\<not> (W (c, a, g) p) | c} w) "
  by blast
\<comment>\<open>This lemma shows that if a maxim (c, a, g) is wrong for subject $s$ at a world, then it is wrong
for all people at $s$. Isabelle automatically completed this proof using the \texttt{blast} method, 
which implements a generic tableau prover, a proof method that operates on lists of formulae using 
rules for conjunction, disjunction, universal quantification, and existential quantification \citep{blast}.\<close>

lemma right_if_right_for_someone:
  shows "\<forall>w. \<forall>c::t. \<forall>g::t. \<exists>s::s. O{W (c, M, g) s | c} w \<longrightarrow> (\<forall>p.  O{W (c, M, g) p | c} w) "
  by blast
\<comment>\<open>This lemma shows that if a maxim (c, a, g) is right for subject $s$ at a world, then it is wrong
for all people at $s$. The proof similarly proceeds using \texttt{blast}. I represent my tests as 
lemmas, that I expect Isabelle to either prove or refute. The statement following the keyword \texttt{shows}
is the sentence of the lemma, and the proof follows the \texttt{by} keyword. \<close>

text\<open>\noindent \textbf{Contradictory Obligations} DDL itself allows contradictory obligations, but contradictory obligations
make obeying the prescriptions of an ethical theory impossible.
Kant subscribes to the general, popular view that morality is supposed to guide action, so ought implies 
can\footnote{Kohl points out that this principle is referred to as 
Kant's dictum or Kant's law in the literature \citep[footnote 1]{kohl}.}. Kohl reconstructs his argument for the principle as 
follows: if the will cannot comply with the moral law, then the moral law has no prescriptive authority 
for the will \citep[703-4]{kohl}. This defeats the purpose of Kant's theory, which is to develop an unconditional, categorical imperative 
for rational agents. Ought implies can requires that obligations never contradict, because an agent 
can't perform contradictory actions. Therefore, any ethical theory that respects ought implies can, 
and Kantian ethics in particular, must not result in conflicting obligations. 
Kant only briefly discusses contradictory obligations in \emph{Metaphysics of Morals}, where he argues that 
conflicting moral obligations are impossible under his theory \citep[V224]{metaphysicsintro}. Particularly, the categorical imperative generates 
``strict negative laws of omission,'' which cannot conflict by definition \citep[45]{timmerman}.\footnote{The 
kinds of obligations generated by the FUL are called ``perfect duties'' which arise from ``contradictions 
in conception,'' or maxims that we cannot even concieve of universalizing. These duties are always negative 
and thus never conflict. Kant also presents ``imperfect duties,'' generated from ``contradictions in will,''
or maxims that we can concieve of universalizing but would never want to. These duties tend to be broader, 
such as ``improve oneself" or "help others," and are secondary to perfect duties. My project only analyzes 
perfect duties, as these are always stronger than imperfect duties.} Both the naive formalization and 
Kroy's formalization allow contradictory obligations, but I explicitly add an axiom to my formalization
that prohibits contradictory obligations.\<close>

lemma conflicting_obligations:
  shows "\<not> (O{W (c, a, g) s|c} \<^bold>\<and> O{\<^bold>\<not>(W (c, a, g) s)| c}) w"
  using no_contradictions by blast
\<comment>\<open>This test passes immediately by the new axiom that prohibits contradictory obligations.\<close>

lemma implied_contradiction:
  assumes "(((W (c1, a1, g1) s) \<^bold>\<and> (W (c2, a2, g2) s)) \<^bold>\<rightarrow> \<^bold>\<bottom>) w"
  shows "\<^bold>\<not> (O{W(c1, a1, g1) s|c} \<^bold>\<and> O{W(c2, a2, g2) s|c}) w"
  using assms no_contradictions by blast
\<comment>\<open>This stronger property states that the combination of obligatory maxims can't
 imply a contradiction and should hold for the same reasons that contradictory obligations aren't
allowed. The added axiom also makes this test pass. \<close>

text\<open>During testing, I also realized that contradictory obligations are closely related to two other properties
that also fail in both prior attempts. First is the idea that obligation implies permissibility, or 
that obligation is a stronger property than permissibility. If there are no contradictory obligations, 
then this property holds because actions are either permissible or prohibited and obligation contradicts
prohibition. Moreover, in a system with contradictory obligations, this property fails because there is some
A that is obligated but also prohibited and therefore not permisible. Formalizing this property below shows 
that this follows from the definition of implication in propositional logic.

\medskip 
\<close>

lemma "\<Turnstile> ((O {A} \<^bold>\<and> O {\<^bold>\<not> A}) \<^bold>\<equiv> (\<^bold>\<not> (O {A} \<^bold>\<rightarrow> \<^bold>\<not> O {\<^bold>\<not>A})))"
  by simp
\<comment>\<open>\texttt{simp} is the simplification tactic, which unfolds definitions to complete a proof. The 
left-hand side states that $A$ is both obligated and prohibited, and is equivalent to the right-hand side, 
which states that $A$ is obligated but not permissible.\<close>

text \<open>\noindent \textbf{Distributive Property} Another property related to contradictory obligations is the distributive property for the obligation
operator.\footnote{Formally, $O\{A\} \wedge O\{B\} \longleftrightarrow O\{A \wedge B\}$.} This is 
another property that we expect to hold. The rough English translation of  $O \{ A \wedge B \} $ is ``you are obligated to 
do both A and B". The rough English translation of $O\{A\} \wedge O\{B\}$ is ``you are obligated to do A 
and you are obligated to do B." We think those English sentences mean the same thing, so they should mean 
the same thing in logic as well. Moreover, if that (rather intuitive) property holds, then contradictory
obligations are impossible, as shown in the below proof.\<close>

lemma distributive_implies_no_contradictions: 
  assumes "\<forall>A B. \<Turnstile> ((O {A} \<^bold>\<and> O {B}) \<^bold>\<equiv> O {A \<^bold>\<and> B})"
  shows "\<forall>A. \<Turnstile>( \<^bold>\<not>(O {A} \<^bold>\<and> O {\<^bold>\<not> A})) "
  using O_diamond assms by blast
\<comment>\<open>The \texttt{assumes} keyword indicates assumptions used when proving a lemma. I use it here to 
capture the idea of metalogical implication. With the assumption, the lemma above reads, ``If the distributive
property holds in this logic, then obligations cannot contradict."\<close>

text \<open>Again, this test fails in the naive formalization and for Kroy's formalization, but
passes for my interpretation because I require that obligations don't contradict as an axiom.\<close>

lemma distribution:
  assumes "\<Turnstile> (O {A} \<^bold>\<and> O {B})"
  shows "\<Turnstile> O {A \<^bold>\<and> B}"
  using assms no_contradictions by fastforce
\<comment>\<open>Once again, the proof proceeds almost immediately using the new axiom.\<close>

text\<open>\medskip 

\noindent \textbf{Un-universalizable Actions} Recall that under 
the logical contradiction interpretation of the Formula of Universal Law, it prohibits lying because, in a world 
where everyone simultaneously lies, lying is impossible. In other words, not everyone can simultaneously
lie because the institution of lying and believing would break down. In Section \nameref{praccon}, 
I recreated Korsgaard's argument for why the logical contradiction interpretation is weaker than what the
Formula of Universal Law should actually require. Therefore, any implementation of the FUL should be 
able to show that the actions prohibited by the logical contradiction interpretation are prohibited, 
because the actions prohibited by the practical contradiction interpretation are a superset of these.
The FUL should show that actions that cannot possibly be universalized are prohibited, because those acts cannot be willed in 
a world where they are universalized. This property fails to hold in both the naive formalization 
and Kroy's formalization, but holds for my custom formalization. Showing that this property holds
for my formalization required significant logical background is presented in Appendix \ref{weirdtests} \<close>


text \<open>
\noindent \textbf{Maxims} Kant does not evaluate the correctness of acts, but rather of maxims. Therefore, any 
faithful formalization of the categorical imperative must evaluate maxims, not acts. This requires 
representing a maxim and making it the input to the obligation operator, which neither of the prior 
attempts do. Because my implementation includes the notion of a maxim, it is able to perform sophisticated 
reasoning as demonstrated in Sections \nameref{joking} and \nameref{murderer}. Staying faithful to the philosophical 
literature enables my system to make more reliable judgements.

\medskip
\<close>

text \<open>\noindent \textbf{Conventional and Natural Acts} When arguing for the practical contradiction interpretation,
Korsgaard makes a distinction between conventional and natural acts \citep{KorsgaardFUL}. 
A conventional act like promising relies on a convention, like the 
convention that a promise is a commitment, whereas a natural act is possible simply because of the laws 
of the natural world. It is easier to show the wrongness of conventional acts because there are worlds 
in which these acts are impossible; namely, worlds in which the convention does not exist. For example, 
the common argument against falsely promising is that if everyone were to falsely promise, the convention 
of promising would fall apart because people wouldn't believe each other, so falsely promising is prohibited. 
It is more difficult to show the wrongness of a natural act, like murder or violence. These acts can 
never be logically impossible; even if everyone murders or acts violently, murder and violence will 
still be possible, so it is difficult to show that they violate the FUL. 

Both the naive and Kroy's interpretations fail to show the wrongness of conventional or natural acts. 
My system shows the wrongness of both natural and conventional acts because it is faithful to Korsgaard's 
practical contradiction interpretation of the FUL, which is the canonical interpretation of the 
FUL \citep{KorsgaardFUL}. This test passes due to the results shown in Chapter Applications, where I
use my system to reason about two ethical dilemmas, one which involves conventional acts and the other which
involves natural acts.
\<close>

(*<*)
lemma True
  nitpick[user_axioms, falsify=false] by simp
\<comment>\<open>Nitpick is able to find a model in which all axioms are satisfied, 
so this version of the FUL is consistent.

$\color{blue}$ Nitpick found a model for card i = 1 and card s = 1:

  Empty assignment $\color{black}$ \<close>



end
(*>*)

