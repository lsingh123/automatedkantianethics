(*<*) theory paper31 imports paper224

begin

(*>*)

section "Prior Formalizations of The Categorical Imperative"

text \<open>In this section, I present two formalizations of the categorical imperative and a testing framework
to evaluate them. In Section \ref{sec:naive}, I will consider an intuitive but naive formalization of 
the formula of universal law. This formalization is equivalent to a theorem in my base logic (DDL), so 
thus does not actually increase the power of my base logic. In effect, this formalization serves as a control
group that I use to present the testing architecture used to evaluate following formalizations.
In Section \ref{sec:kroy}, I will explore Moshe Kroy's partial formalization of 
the categorical imperative.\<close>

subsection \<open>Naive Formalization of the Formula of Universal Law \label{sec:naive}\<close>

text "This section presents a simple and intuitive formalization of the Formula of Universal Law (FUL). 
This naive formalization will hold in the base logic itself, so this formalization does not actually
improve upon an ordinary deontic logic at all. This section serves two purposes. First, the naive formalization
is a toy example that demonstrates the implementation and testing process that will be used for the more 
complex formalizations presented later in Chapters 2 and 3. Second, this formalization is effectively
a control group used to determine which properties of obligaition hold in the base logic. Future formalizations
will improve on the base logic by passing more tests, or equivalently, proving more properties of 
obligation than the base logic can.


The FUL roughly states that, if a maxim cannot be willed in a world where it is universalized, it is prohibited. One
reading of this rule is that a maxim is only permissible if it is necessarily permissible. To formalize
a reading of the FUL like this naive one, I will first represent the reading as a sentence in my logic
and then add this sentence as an axiom in my logic."

subsubsection \<open>Formalization \label{sec:naive_form}\<close>

text "Many of the formalizations of the categorical imperative that I present in this thesis require
some logical background. This naive formalization requires that I define the notion of permissibility,
where an action is permissible if and only if it is not prohibited."

abbreviation ddlpermissable::"t\<Rightarrow>t" ("P_")
  where "(P A) \<equiv> (\<^bold>\<not>(O {\<^bold>\<not>A}))"
\<comment>\<open>An act $A$ is permissible if its negation is not obligated. For example, buying a red folder is 
permissible because I am not required to refrain from buying a red folder.\<close>

text \<open>This naive formalization requires no additional logical machinery, but more complex
formalizations may require additional logical concepts. 

Let's now consider a naive reading of the Formula of Universal Law (FUL): ``act only in accordance 
with that maxim through which you can at the same time will that it become a universal law" \citep{groundwork}.
An immediate translation to DDL is that if $A$ is not necessary permissible then it is prohibited. In other
words, if we cannot universalize $P A$ (where universalizing is represented by the modal necessity 
operator), then $A$ is prohibited. This sentence is formalized in the abbreviation below:\<close>

abbreviation FUL_naive where "FUL_naive \<equiv> \<lambda>A. ((\<^bold>\<not>(\<box> (P A))) \<^bold>\<rightarrow> (O {(\<^bold>\<not>A)}))"
\<comment>\<open>For a given maxim `A', the FUL states that if A is not necessarily permissible, it is prohibited.\<close>

text "This naive formalization holds as a theorem of DDL. I show this using Isabelle below:"

lemma "\<forall>A. \<Turnstile> (FUL_naive A)"
  by simp
\<comment>\<open>In this short and simple proof, the statement ``by simp" demonstrates that the proof is completed
using the ``simp" tool, which is Isabelle's term rewriting engine. In this case, the result follows from
the definitions of the modal operators in DDL, so term rewriting suffices to complete the proof.\<close>

text \<open>The general process of implementing a formalization of the FUL will be to represent the 
formalization as a sentence in my logic, as above, and then to add the formalization as an axiom to 
the logic. Kant's ethical theory is rule based, so it involves applying the categorical
imperative to solve ethical dilemmas. In logic, this is equivalent to adopting the categorical imperative as 
an axiom and then reasoning in the newly formed logic to come to ethical conclusions. Adding the categorical
imperative as an axiom makes it impossible to violate it and thus represents the categorical imperative
as the supreme, unviolable law of morality. 

Note that under this approach, reasoning about violations of obligation is difficult. Any violation of the 
categorical imperative immediately results in a contradiction. Developing a Kantian account of contrary-
to-duty obligations is a much larger philosophical project that is still open @{cite KorsgaardRTL}. This paper will focus 
on the classical Kantian notion of an ideal moral world, and thus does not reason about violations 
of the moral law @{cite idealtheory}.

Because my naive formalization holds in the base logic, adding it as an axiom does not make the logic
any more powerful. No new theorems can be derived using the naive formalization that could not already
be derived in the base logic. Thus, this section serves as a ``control group." Tests performed in this
section establish which properties of obligation don't hold in the base logic. The fact that these 
tests will pass for the later, more sophisticated formalizations will serve as evidence for the superiority
of these formalizations over the base logic.\<close>

axiomatization where
FUL_1: "\<Turnstile> ((\<^bold>\<not>(\<box> (P A))) \<^bold>\<rightarrow> (O {(\<^bold>\<not>A)}))"

text \<open>Once I add a formalization of the FUL as an axiom to my system, I will test the formalization.
Each test will take the form of a lemma which I expect to either hold or be disproven by the categorical
imperative. For example, one test might be the lemma ``murder is wrong." I will evaluate formalizations
based on their ability to prove expected properties of the categorical imperative, as determined by 
philosophical literature. These tests fall into two categories: metaethical tests, which focus on 
abstract properties of the ethical system, and application tests, which simulate the kind of practical reasoning 
that an agent would actually perform by specifying a simple model. 

One way to understand computational ethics is as translational work that seeks
to translate an ethical theory presented by a philosopher to something that a computer can reason about.
My testing architecture evaluates how faithful a particular formalization is to the ethical theory that 
it translate. This testing approach is not specific to my ethical theory and could be used to evaluate
other formalizations of other theories as well.\<close>

  subsubsection \<open>Metaethical Tests \label{sec:meta_tests_naive}\<close>

  text \<open>First, I present metaethical tests for the naive formalization (or equivalently the base logic). 
These tests evaluate abstract properies of the system, independent of a particular agent, situation, or 
act. For example, one metaethical test may be to determine if the system is capable of generating models 
in which actions are obligated. If the system can never obligate anything, this indicates that it is 
not a good ethical system.\<close>

  text \<open>$\textbf{Preliminary Tests}$\<close>

text \<open>The immediate test for any formalization is consistency, or the property of being free of contradictions. 
An inconsistent formalization is immediately useless, because all sentences are true in an inconsistent
logic. Nitpick, Isabelle's model checker, offers a handy way of checking consistency. Specifically, 
if Nitpick can find a model that satisfies all the axioms of the logic, then the logic is consistent.
\<close>

lemma True nitpick [satisfy,user_axioms,format=2] oops
\<comment> \<open>\color{blue} Nitpick found a model for card i = 1:

  Empty assignment \color{black}\<close>
\<comment> \<open>Nitpick tells us that the FUL is consistent\footnote{``oops" at the end of a lemma indicates that the 
proof is left unfinished. It does not indicate that an error occurred. In this case, we aren't interested
in proving True (the proof is trivial and automatic), hence the oops.}\<close>


(*<*)
lemma something_is_obligatory:
  shows "\<forall> w. \<exists> A. O {A} w"
  nitpick [user_axioms]
  oops
\<comment> \<open>We might think that in every world we want something to be obligated. \<close>
\<comment> \<open>Sadly, Sledgehammer times out trying to prove this. Let's relax this\<close>
\<comment>\<open>``Nitpick found a counterexample for card i = 1:

  Empty assignment"\<close>
\<comment>\<open>Nitpick to the rescue! The formula is in fact not valid.\<close>

lemma something_is_obligatory_2:
  shows "\<forall> w. \<exists> A. O {A} w"
  nitpick [user_axioms, falsify=false]
  oops
\<comment>\<open>``Nitpick found a model for card i = 1:

  Skolem constant:
    A = ($\lambda x. \_$)($i_1$ := True)"\<close>
\<comment>\<open>Nitpick tells us that the formula is consistent - it found a model where the formula is true.\<close>
\<comment>\<open>This means that our model is underspecified - this formula is neither valid nor inconsistent.\<close>

lemma something_is_obligatory_relaxed:
  shows "\<exists> A w. O {A} w"
  nitpick [user_axioms]
  oops
\<comment>\<open>``Nitpick found a counterexample for card i = 1:

  Empty assignment"\<close>
\<comment>\<open>The relaxed version definitely isn't valid.\<close>

lemma something_is_obligatory_relaxed_2:
  shows "\<exists> A w. O {A} w"
  nitpick [user_axioms, falsify=false]
  oops
\<comment>\<open>``Nitpick found a model for card i = 1:

  Skolem constant:
    A = ($\lambda x. \_$)($i_1$ := True)"\<close>
\<comment>\<open>Nitpick tells us that the formula is consistent - it found a model where the formula is true.\<close>
\<comment> \<open>The model seems underspecified.\<close>
(*>*)


  text \<open>An initial property that we might be interested in is the possibility of permissibility, or 
whether or not the system can generate models in which certain acts are permissible. In modern ethics, 
permissibility is a well-accepted phenomenon.
An ethical theory that doesn't allow for permissibility would require that every action is either obligatory or 
prohibited. If that is the case, many counterintuitive theorems follow, including that all 
permissible actions are obligatory.\footnote{Proof is in the appendix.} Therefore, I will include 
the possibility of permissibility as one test for my formalizations.\<close>

  lemma permissible:
    shows "\<exists>A. ((\<^bold>\<not> (O {A})) \<^bold>\<and> (\<^bold>\<not> (O {\<^bold>\<not> A}))) w"
    nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue}Nitpick found a model for card i = 1:

  Skolem constant:
    A =($\lambda x. \_$)($i_1$ := False) \color{black}\<close>
\<comment>\<open>I want to show that there exists a model where there is some formula A that is permissible, or, 
in English, that permissibility is possible. Nitpick finds a model where the above formula holds, 
so permissibility is indeed possible.\<close>
\<comment>\<open>Quick note on how to read Nitpick results. Nitpick is Isabelle's model checker, and it can either 
time out, find a model that satisfies the given theorem, or find a counterexample that disproves
the given theorem. It will then provide the corresponsing model by specifying model components. For readability, 
all terms except for the free variables are hidden. This model has cardinality 1 for the world (i) type.
The term `A' is defined as false at world $i_1$. \<close>
\<comment>\<open>These details will be elided for most Nitpick examples, but this provides guidance on how to interpret
the output.\<close>

    text \<open>Another similar property is that for any arbitrary action A, there is a model that makes 
it permissible. This property is actually not desirable, because if A is "murder" then the CI should require that 
it be prohibited in every world. Therefore, in order for this test to pass, Nitpick should \emph{not}
be able to find a satisfying model for this formula.\<close>

lemma fixed_formula_is_permissible:
  fixes A
  shows "((\<^bold>\<not> (O {A})) \<^bold>\<and> (\<^bold>\<not> (O {\<^bold>\<not> A}))) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue}Nitpick found a model for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)\color{black}\<close>
\<comment>\<open>Because Nitpick finds a satisfying model for this formula, this test fails for the naive interpretation.\<close>

  text \<open>Another initial property is that arbitary actions should not be obligated. No sensible ethical
theory would require that any arbitrary action A is obligated, because A may be something obviously wrong,
like murder. In order for this test to pass, Nitpick must disprove the formula below by finding a counterexample.\<close>

lemma arbitrary_obligations:
  fixes A::"t"
  shows "O {A} w"
  nitpick [user_axioms=true] oops
\<comment> \<open>\color{blue} Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False) \color{black}\<close>
\<comment>\<open>Nitpick finds a counterexample disproving the statement that any arbitrary action is obligatory, so
this test passes.\<close>

  text \<open>$\textbf{Conflicting Obligations}$\<close>

  text \<open>The next set of tests will focus on conflicting obligations. There is some debate about Kant's
personal stance on conflicting obligations, but neo-Kantians agree that the FUL itself cannot obligate
conflicting actions. For more complete discussion of conflicting obligations in Kantian literature, 
see Section \ref{sec:priorgoals}. I will first test whether or not, for some arbitrary action, Nitpick can find
a model in which that action is both obligated and prohibited.\<close>

lemma conflicting_obligations:
  fixes A
  shows "(O {A} \<^bold>\<and> O {\<^bold>\<not> A}) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue} Nitpick found a model for card i = 2:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True) \color{black}\<close>
\<comment>\<open>Nitpick found a model with conflicting obligations, so this tests fails.\<close>

(*<*)  text \<open>This is a property of DDL itself, not necessarily of my formalization specifically. A future, 
more robust formalization should add an axiom that disallows this. Let's see if that causes any obvious 
problems.\<close>

lemma removing_conflicting_obligations:
  assumes "\<forall>A. \<Turnstile> (\<^bold>\<not> (O {A} \<^bold>\<and> O {\<^bold>\<not> A}))"
  shows True
  nitpick [satisfy,user_axioms,format=2] oops
\<comment>\<open>\color{blue} Nitpick found a model for card i = 1:

  Empty assignment \color{black}\<close>
\<comment>\<open>We can disallow conflicting obligations and the system is still consistent - that's good.\<close>(*>*)

  text \<open>The above is a rather weak notion of contradictory obligations. Korsgaard additionally argues that Kantian 
ethics also has the stronger property that if two maxims imply a contradiction, they must not be willed \citep{KorsgaardFUL}.
I test this property below. Because this property is stronger than the previous test, and the previous 
test failed, this test will also fail.\<close>

lemma implied_contradiction:
  fixes A::"t"
  fixes B::"t" 
  assumes "\<Turnstile>(\<^bold>\<not> (A \<^bold>\<and> B))"
  shows "\<Turnstile>(\<^bold>\<not> (O {A} \<^bold>\<and> O {B}))"
  nitpick [user_axioms]
proof - 
  have "\<Turnstile>(\<^bold>\<not>(\<diamond>(A \<^bold>\<and> B)))"
    by (simp add: assms)
  then have "\<Turnstile>(\<^bold>\<not> (O {A \<^bold>\<and> B}))" by (smt O_diamond)
\<comment>\<open>Notice that this is $\textbf{almost}$ the property we are interested in. In fact, if $O \{ A \wedge B \}$
is equivalent to $O\{A\} \wedge O\{B\}$, then the proof is complete.\<close>
  thus ?thesis oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 2:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := True, $i_2$ := False)
    B = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True) \color{black}\<close>
\<comment>\<open>Sadly the property I'm actually interested in doesn't follow.\<close>

    text \<open>The above proof yields an interesting observation.  $O \{ A \wedge B \} $ is not equivalent to 
$O\{A\} \wedge O\{B\}$. The rough English translation of  $O \{ A \wedge B \} $ is ``you are obligated to 
do both A and B". The rough English translation of $O\{A\} \wedge O\{B\}$ is ``you are obligated to do A 
and you are obligated to do B." We think those English sentences mean the same thing, so they should mean 
the same thing in our logic as well. This ``distributive" property of obligation is another test.\<close>

lemma distributive_property_for_obligation:
  shows "\<Turnstile> (O {A} \<^bold>\<and> O {B}) \<equiv> \<Turnstile> O {A \<^bold>\<and> B}"
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 2:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)
    B = ($\lambda x. \_$)($i_1$ := True, $i_2$ := False)\color{black}
Once again, this tests fails in the control group.\<close>

  text \<open>$\textbf{Miscellaneous Properties}$\<close>

  text \<open>The last set of metaethical tests involve miscellaneous properties of the categorical 
imperative. First, I show that the naive formalization is equivalent to the below theorem, which clearly
fails to track intuition about ethics.\<close>

lemma FUL_alternate:
  shows "\<Turnstile> ((\<diamond> (O {\<^bold>\<not> A})) \<^bold>\<rightarrow> (O {\<^bold>\<not> A}))"
  by simp
\<comment> \<open>This means that if something is possibly prohibited, it is in fact prohibited.\<close>

text \<open>This is a direct consequence\footnote{For a manual proof, see the Appendix.} of the naive formalization, but it's not clear to me that this is
actually how we think about ethics. For example, imagine an alternate universe where smiling at 
someone is considered an incredibly rude and disrespectful gesture. In this universe, I am probably 
prohibited from smiling at people, but this doesn't mean that in this current universe, smiling is 
morally wrong.\<close>

text \<open>The ``ought implies can" principle is attributed to Kant\footnote{The exact philosophical credence of this view is disputed, but the rough idea holds nonetheless. See @{cite kohl} for more.}
 and is rather intuitive: you can't be obligated to do the impossible. Deontic 
logics evolved specifically from this principle, so this should hold in the base logic @{cite [cite_macro=citep] cresswell}. \<close>

lemma ought_implies_can:
  shows "\<forall>A. \<Turnstile> (O {A} \<^bold>\<rightarrow> (\<diamond>A))"
  using O_diamond by blast

text \<open>This test passes in the base logic, and will thus hold in all future formalizations as well. 
Therefore, it's an interesting property but not actually useful in evaluating different formalizations 
of the FUL.\<close>
(*<*)

lemma distribute_obligations_if:
  assumes "\<Turnstile> O {A \<^bold>\<and> B}"
  shows "\<Turnstile> (O {A} \<^bold>\<and> O {B})"
  nitpick [user_axioms, falsify=true, verbose]
  oops
\<comment>\<open>Nitpick can't find a countermodel for this theorem, and sledgehammer can't find a proof.\<close>
\<comment>\<open>Super strange. I wonder if this is similar to $\Box (A \wedge B)$ vs $\Box A \wedge \Box B$\<close>

lemma distribute_boxes:
  assumes "\<Turnstile>( \<box>(A \<^bold>\<and> B))"
  shows "\<Turnstile> ((\<box>A) \<^bold>\<and> (\<box>B))"
  using assms by blast
\<comment>\<open>We really expect the O operator to be acting like the $\square$ operator. It's like a modal necessity operator,
like necessity across ideal worlds instead of actual worlds. Therefore, we'd expect theorems that hold of $\square$
to also hold of O.\<close>(*>*)

subsubsection \<open>Application Tests \label{sec:app_tests_naive}\<close>

text "The second category of tests I will consider is Application tests, which involve specifying models
to encode certain facts into the system, and then asking questions about obligations. Metaethical tests
focus on properties that apply to all acts, circumstances, and actors, but application tests focus
on specific acts. Let's start with analyzing an obvious example - that murder is 
wrong.

First, I will define murder as a constant below. Notice that right now, this constant is just a term. 
I haven't specified any properties of murder, so as of now, it's interchangeable with any other term. 
Application tests generally define an act and then define properties of the act (e.g. if X is murdered,
X dies). The tests aim to show that acts with certain properties are either obligated or prohibited. "

consts M::"t"
abbreviation murder_wrong::"bool" where "murder_wrong \<equiv> \<Turnstile>(O {\<^bold>\<not> M})"
\<comment>\<open>This abbreviation merely represents the statement that murder is prohibited.\<close>

text \<open>I will now define properties of murder and see if they achieve the desired result that murder
is prohibited. First, I start with the rather basic property that murder is prohibited in some 
world, or that murder is possibly wrong. This is quite a strong assumption because it gives the system
a moral fact about a kind of prohibition against murder. Ideally, an ethical theory can take nonmoral
facts about murder (like murder kills) and use these to generate a moral judgement about the wrongness of 
murder. This property is much stronger than the assumptions that we make in ordinary moral
reasoning and thus should be more than enough to show that murder is wrong. \<close>

abbreviation possibly_murder_wrong::"bool" where "possibly_murder_wrong \<equiv> (\<diamond> (O {\<^bold>\<not> M})) cw"

lemma wrong_if_possibly_wrong:
  shows "possibly_murder_wrong \<longrightarrow> murder_wrong"
  by simp
\<comment>\<open>This lemma gets to the ``heart" of this naive interpretation. If something
 isn't necessarily obligated, it's not obligated anywhere.\<close>

text "The above example does exactly what I expect it to: it shows that if something is wrong somewhere 
it's wrong everywhere. That being said, it seems like quite a weak claim. I assumed a very strong, moral 
fact about murder (that it is wrong somewhere), so it's not surprise that I was able to show the wrongness 
of murder."

text \<open>Let's try a different example using a much weaker, nonmoral assumption. Kant argues that the FUL
prohibits lying.\footnote{Specifically, he prohibits making a false promise in order to get some cash \cite[idk page no]{groundwork}.}
In this example, I will define lying as a term such that not everyone can lie simultaneously. This is 
one of Kant's canonical examples of the universalizability test. Lying fails the universalizability 
test because, in a world where everyone lied, no one would believe each other anymore, so the very system 
or truth-telling would break down, making lying impossible. I can represent this reasoning in my logic 
as the assumption that not everyone can lie simultaneously. 

To fully capture this idea, I need some notion of
a person, so that I can argue that not all people can lie simultaneously.
\<close>

typedecl person
consts lie::"person\<Rightarrow>t"
consts me::"person"

text \<open>Again, this machinery is quite empty because it doesn't specify any axioms about what a person can 
or cannot do. In future formalizations, I will define a more robust notion of a person, but the naive 
formalization has no conception of a person.\<close>

abbreviation lying_not_universal::"bool" where "lying_not_universal \<equiv> \<forall>w. \<not> ((\<forall>x. lie(x) w) \<and> (lie(me) w))"

text "This is a rough translation of failure of the universalizability test: I  test the maxim universally,
as represented by the universal quantifier in the first conjunct, and simultaneously, as represented by 
the second conjunct @{cite [cite_macro=citep] simul}. The FUL says that if this sentence is true, then lying should be prohibited. 
Therefore, the above sentence should imply that lying is prohibited."

lemma breaking_promises:
  assumes lying_not_universal
  shows "(O {\<^bold>\<not> (lie(me))}) cw"
  nitpick [user_axioms]
  oops
\<comment>\<open>\color{blue}Nitpick found a counterexample for card i = 1 and card person = 1:

  Empty assignment \color{black}\<close>

  text \<open>This test fails. The FUL should say that lying is prohibited and the fact that it
doesn't demonstrates the weakness of this naive formulation of the categorical imperative. Kant's version of
the FUL universalizes across people, as in the definition of @{abbrev lying_not_universal}. When universalizing
an act, Kant imagines a world in which all \emph{people} perform the act. The naive formalization, 
on the other hand, universalizes an act across \emph{worlds} because it uses the $\Box$ operator
to represent universalization. This is the philosophical error that makes the naive 
formalization so naive, and future formalizations will need to remedy this error.
This serves as an example of the kind of reasoning that 
Isabelle empowers us to do. Even this simple argument has philosophical consequences. It tells us that
reading the FUL as a claim about consistency across possible worlds, instead of consistency across 
agents, leads to counterintuitive conclusions.

Additionally, Kant argued that obligations are not person-specific but instead apply equally to all 
rational agents.\footnote{For a philosophical analysis of this idea, see Section \ref{sec:priorgoals}}
Thus, any formalization of the categorical should generate obligations that are consistent across people.
This next step analyzes this property. \<close>

lemma equal_obligations:
  assumes "\<Turnstile> O {(lie(me))}"
  shows "\<forall>x. \<Turnstile> (O {(lie(x))})"
  nitpick [user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card person = 2 and card i = 2:

  Free variable:
    lie = ($\lambda x. \_$)($p_1$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := True), $p_2$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := False))
  Skolem constant:
    x = $p_2$ \color{black}\<close>

  text \<open>In this section, I presented the framework I will use to implement and test different interpretations
of the categorical imperative. An implementation consists of some necessary logical background, a 
representation of the FUL using that logical background, and a logical system that adds that representation
as an axiom. To test such an implementation, I design a ``test suite" that consists of properties of 
the categorical imperative verified by philosophical literature. I demonstrated the performance of 
these tests in my base logic, which serves as a control group. 

I will evaluate more sophisticated formalizations of the FUL using this testing framework. The properties
I test will remain more or less consisten across different formalizations, but the exact logical representation
of the tests will depend on the specifics of a particular implementation. In the next section, I will 
implement Moshe Kroy's formalization of the FUL and evaluate it using this testing framework. Finally, 
I will use the results of these tests to define clear goals for a custom formalization of the categorical 
imperative. These goals represent areas of improvement over previous formalizations, and I will justify
them using philosophical literature.\<close>


(*<*)
end
(*>*)


