(*<*) theory paper31 imports paper224

begin

(*>*)

section "The Categorical Imperative"

text \<open>In this section, I will present two formulations of the categorical imperative. In Section \ref{sec:naive}, I will 
consider a simple, naive formulation of the formula of universal law. This formulation is, as I will 
show, clearly not a good ethical rule. The purpose of this section is to explore the kinds of ethical
tests that Isabelle can carry out. In Section \ref{sec:kroy}, I will explore Moshe Kroy's @{cite kroy} partial formalization of 
the first two formulations of the categorical imperative.\<close>

subsection \<open>Naive Formulation of the Formula of Universal Law \label{sec:naive}\<close>

text "This section presents a simple and intuitive formalization of the formula of universal law, which 
is to will only those maxims that you would simultaneously will universalized. The universalizability 
test creates negative obligations: if a maxim passes the universalizability test, it is permissible. Else,
it is prohibited. In order to appropriately formalize this, we need some notion of permissibility."

abbreviation ddlpermissable::"t\<Rightarrow>t" ("P_")
  where "(P A) \<equiv> (\<^bold>\<not>(O {\<^bold>\<not>A}))"
\<comment>\<open>An act $A$ is permissible if its negation is not obligated. For example, buying a red folder is 
permissible because I am not required to refrain from buying a red folder.\<close>

text "This naive formalization will require very little additional logical machinery, but more complex
formalizations may require additional logic concepts. 

Let's now consider a naive reading of the Formula of Universal Law (FUL): `act only in accordance 
with that maxim through which you can at the same time will that it become a universal law' @{cite groundwork}.
An immediate translation to DDL is that if $A$ is not necessary permissible then it is prohibited. In other
words, if we cannot universalize $P A$ (where universalizing is represented by the modal necessity 
operator), then $A$ is prohibited. Let's add this as an axiom to our logic."

axiomatization where
FUL_1: "\<Turnstile> ((\<^bold>\<not>(\<box> (P A))) \<^bold>\<rightarrow> (O {(\<^bold>\<not>A)}))"

text "Why add the categorical imperative as an axiom of this logic? The purpose of this logic is to 
perform ethical reasoning. Kant's ethical theory is rule based, so it involves applying the categorical
imperative to solve ethical dilemmas. In logic, this is equivalent to adopting the categorical imperative as 
an axiom and then reasoning in the newly formed logic to come to ethical conclusions. Adding the categorical
imperative as an axiom makes it impossible to violate it. 

Note that in this system, reasoning about violations of obligation is difficult. Any violation of the 
categorical imperative immediately results in a contradiction. Developing a Kantian account of contrary-
to-duty obligations is a much larger philosophical project that is still open @{cite KorsgaardRTL}. This paper will focus 
on the classical Kantian notion of an ideal moral world @{cite idealtheory}.

The immediate test for any formalization is consistency, which we can check with Nitpick."


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

subsubsection "Specifying the Model"

text "One category of tests involves specified models to encode certain facts 
into the system and then ask questions about obligations. Without specifying the model, we are limited 
to showing high-level metaethical facts. Let's start with analyzing an obvious example - that murder is 
wrong."

consts M::"t"
abbreviation murder_wrong::"bool" where "murder_wrong \<equiv> \<Turnstile>(O {\<^bold>\<not> M})"

(*<*)
lemma something_is_obligatory_2:
  assumes murder_wrong
  shows "\<forall> w. \<exists> A. O {A} w"
  using assms by auto
\<comment> \<open>It works this time, but I think ``murder wrong" might be too strong of an assumption\<close>(*>*)

abbreviation possibly_murder_wrong::"bool" where "possibly_murder_wrong \<equiv> (\<diamond> (O {\<^bold>\<not> M})) cw"
\<comment>\<open>These are very simple properties. @{text poss_murder_wrong} is an abbreviation for the axiom
that there is some world where murder might be prohibited. Even this is quite a strong assumption - 
ideally we'd want to give the system nonmoral facts about murder (like a definition) and then make 
moral claims.\<close>

lemma wrong_if_possibly_wrong:
  shows "possibly_murder_wrong \<longrightarrow> murder_wrong"
  by simp
\<comment>\<open>This lemma gets to the ``heart" of this naive interpretation. We really want to say that if something
 isn't necessarily obligated, it's not obligated anywhere.\<close>

text "The above example does exactly what we expect it to: we show that if something is wrong somewhere 
it's wrong everywhere. That being said, it seems like quite a weak claim. We assumed a very strong, moral 
fact about murder (that it is wrong somewhere), so it's not surprise that we were able to reach our desired conclusion."

text "Let's try a weaker assumption: Not everyone can lie."

typedecl person
consts lie::"person\<Rightarrow>t"
consts me::"person"
\<comment>\<open>Notice that this machinery is quite empty. We don't give axioms about what a person can or can't do.\<close>

abbreviation lying_not_universal::"bool" where "lying_not_universal \<equiv> \<forall>w. \<not> ((\<forall>x. lie(x) w) \<and> (lie(me) w))"

text "This is a rough translation of failure of the universalizability test: we will test the maxim universally,
as represented by the universal quantifier in the first conjunct, and simultaneously @{cite simul}, as represented by 
the second conjunct. The FUL tells us that if this sentence is true, then lying should be prohibited. 
Let's test it."

lemma breaking_promises:
  assumes lying_not_universal
  shows "(O {\<^bold>\<not> (lie(me))}) cw"
  nitpick [user_axioms]
  oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card person = 2 and card i = 2:

  Free variable:
    lie = ($\lambda x. \_$)($p_1$ := ($\lambda x. \_$)($i_1$ := True, $i_2$ := False), $p_2$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := False)) \color{black}\<close>
\<comment>\<open>Quick note on how to read Nitpick results. Nitpick will either say that it found a ``model" or a ``counterexample" in 
the first line. It will then provide a model by specifying model components. For readability, all except for the 
free variables are hidden. This model has cardinality 2 for the person and world (i) types. The term \texttt{lie} is 
defined for people $p_1$ and $p_2$. $p_1$ lies at world $i_1$ and does not lie at world $i_2$. $p_2$ does
the opposite.\<close>
\<comment>\<open>These details will be elided for most Nitpick examples, but this provides guidance on how to interpret
the output.\<close>

  text \<open>This formula isn't valid. While the FUL should tell us that lying is prohibited, the fact that it 
doesn't demonstrates the weakness of this naive formulation of the categorical imperative. Kant's version of
the FUL universalizes across people, as we did in the definition of @{abbrev lying_not_universal}. The 
naive formalization universalizes across worlds using the $\Box$ operator, so it makes sense that it can't
handle this example appropriately.

The above implies that the FUL should prescribe consistent obligations across people. If our formalization
doesn't, clearly something has gone wrong somewhere. Let's test that!\<close>

lemma universalizability:
  assumes "\<Turnstile> O {(lie(me))}"
  shows "\<forall>x. \<Turnstile> (O {(lie(x))})"
  nitpick [user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card person = 2 and card i = 2:

  Free variable:
    lie = ($\lambda x. \_$)($p_1$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := True), $p_2$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := False))
  Skolem constant:
    x = $p_2$ \color{black}\<close>

  text \<open>This lemma demonstrates the problem with the naive interpretation. The FUL universalizes across people
but the naive formalization universalizes across worlds. Because this interpretation is so naive, it is 
limited in its power. However, this serves as an example of the kind of reasoning that 
Isabelle empowers us to do. Even this simple argument has philosophical consequences. It tells us that
reading the FUL as a claim about consistency across possible worlds, instead of consistency across 
agents, leads to counterintuitive conclusions.\<close>

  subsubsection "Metaethical Properties"

  text \<open>The above section specified the model to simulate practical ethical reasoning, or the kind of 
reasoning that is useful when an agent has to decide what to do. Formalizations of the categorical 
imperative can also be used to do metaethical reasoning, which can evaluate a particular ethical theory
as good or bad. In this case, we can analyze properties of the system in the form of theorems. For example,
if we can show that, in this system, nothing is ever obligated, that would indicate that we have a bad 
ethical system. This is not only philosophical work, but is also a useful way to test different ethical
reasoning systems.

An initial property that we might be interested in is permissibility itself. More generally, an ethical
theory that doesn't allow for permissibility would require that every action is either obligatory or 
prohibited. In fact, if that is the case, many counterintuitive theorems follow, including that all 
permissible actions are obligatory.\footnote{Proof is in the appendix.}\<close>
  lemma permissible:
    shows "\<exists>A. ((\<^bold>\<not> (O {A})) \<^bold>\<and> (\<^bold>\<not> (O {\<^bold>\<not> A}))) w"
    nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue}Nitpick found a model for card i = 1 and card s = 1:

  Skolem constant:
    A =($\lambda x. \_$)($i_1$ := False) \color{black}\<close>
\<comment>\<open>We want to show that there exists a model where there is some formula A that is permissible, or, 
in English, that permissibility is possible. Nitpick finds a model where the above formula holds, 
so permissibility is indeed possible.\<close>
\<comment>\<open>Note that it's not clear @{cite kitcher} if Kant actually thought that permissibility was a coherent 
concept. Either way, in modern ethics, permissibility is a pretty widely accepted phenomenon.\<close>

lemma fixed_formula_is_permissible:
  fixes A
  shows "((\<^bold>\<not> (O {A})) \<^bold>\<and> (\<^bold>\<not> (O {\<^bold>\<not> A}))) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue}Nitpick found a model for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)\color{black}\<close>
\<comment>\<open>This is a slightly stronger result: for any arbitrary action A, there is a model that makes it 
permissible. We actually don't want this to hold, because if A is "murder" then the CI requires that 
it be prohibited in every world.\<close>

  text \<open>Another initial test is the possibility of arbitrary obligations. If anything can be shown to be 
obligatory in this theory, then clearly it doesn't track our intuitions.\<close>

lemma arbitrary_obligations:
  fixes A::"t"
  shows "O {A} w"
  nitpick [user_axioms=true] oops
\<comment> \<open>\color{blue} Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False) \color{black}\<close>
\<comment>\<open>This is good! Shows us that any arbitrary term isn't obligatory.\<close>

  text \<open>$\textbf{Conflicting Obligations}$\<close>

  text \<open>A more complex metaethical property is the possibility of conflicting obligations. Many deontological
ethics are criticized for prescribing conflicting obligations, but in Kantian ethics, 
obligations never conflict @{cite contradictoryob}. In order for morality to be action-guiding, it needs to be free of 
conflicting obligations. Let's see if we can have contradictary obligations under the naive formalization.\<close>

lemma conflicting_obligations:
  fixes A
  shows "(O {A} \<^bold>\<and> O {\<^bold>\<not> A}) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue} Nitpick found a model for card i = 2:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True) \color{black}\<close>
\<comment>\<open>Oh no! Nitpick found a model with conflicting obligations - that's bad!\<close>

  text \<open>This is a property of DDL itself, not necessarily of my formalization specifically. A future, 
more robust formalization should add an axiom that disallows this. Let's see if that causes any obvious 
problems.\<close>

lemma removing_conflicting_obligations:
  assumes "\<forall>A. \<Turnstile> (\<^bold>\<not> (O {A} \<^bold>\<and> O {\<^bold>\<not> A}))"
  shows True
  nitpick [satisfy,user_axioms,format=2] oops
\<comment>\<open>\color{blue} Nitpick found a model for card i = 1:

  Empty assignment \color{black}\<close>
\<comment>\<open>We can disallow conflicting obligations and the system is still consistent - that's good.\<close>

  text \<open>The above is a rather weak notion of contradictory obligations. Korsgaard @{cite KorsgaardFUL} argues that Kantian 
ethics also has the stronger property that if two maxims imply a contradiction, they must not be willed.
Let's see if that fact holds in this formalization.\<close>

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
\<comment>\<open>Sadly the property we're actually interested in doesn't follow.\<close>

    text \<open>The above proof yields an interesting observation.  $O \{ A \wedge B \} $ is not equivalent to 
$O\{A\} \wedge O\{B\}$. The rough English translation of  $O \{ A \wedge B \} $ is ``you are obligated to 
do both A and B". The rough English translation of $O\{A\} \wedge O\{B\}$ is ``you are obligated to do A 
and you are obligated to do B." We think those English sentences mean the same thing, so they should mean 
the same thing in our logic as well. Let's test that.\<close>

lemma distribute_obligations:
  assumes  "\<Turnstile> (O {A} \<^bold>\<and> O {B})"
  shows "\<Turnstile> O {A \<^bold>\<and> B}"
  nitpick [user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 2:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := True, $i_2$ := False)
    B = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)\color{black}\<close>

  text \<open>Note that this is a property of DDL itself, not just my formalization. A future formalization might 
add this property as an axiom.\footnote{For discussion of why this property doesn't hold in DDL, see the Appendix.}\<close>

  text \<open>$\textbf{Miscellaneous Properties}$\<close>

  text \<open>I named this formalization the naive formulation for a reason. Though it seems to be an immediate
translation of the FUL into DDL, it doesn't fully respect the properties of modal logic itself. In particular, the 
formalization as given is equivalent to the below theorem.\<close>

lemma FUL_alternate:
  shows "\<Turnstile> ((\<diamond> (O {\<^bold>\<not> A})) \<^bold>\<rightarrow> (O {\<^bold>\<not> A}))"
  by simp
\<comment> \<open>This means that if something is possibly prohibited, it is in fact prohibited.\<close>
\<comment> \<open>This is a direct consequence\footnote{For a manual proof, see the Appendix.} of the naive formalization, but it's not clear to me that this is 
actually how we think about ethics. For example, we can imagine an alternate universe where smiling at 
someone is considered an incredibly rude and disrespectful gesture. In this universe, we are probably 
prohibited from smiling at people, but this doesn't mean that in this current universe, smiling is 
morally wrong.\<close>

text \<open>The ``ought implies can" principle is attributed to Kant\footnote{The exact philosophical credence of this view is disputed, but the rough idea holds nonetheless. See @{cite kohl} for more.}
 and is rather intuitive: you can't be obligated to do the impossible. It is worth noting that deontic 
logics evolved @{cite cresswell} specifically from this principle, so this should hold in both my 
modified logic and in DDL. \<close>

lemma ought_implies_can:
  shows "\<forall>A. \<Turnstile> (O {A} \<^bold>\<rightarrow> (\<diamond>A))"
  using O_diamond by blast
\<comment>\<open>@{thm O_diamond} is an axiom of DDL itself, so this theorem holds in DDL.\<close>

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
to also hold of O.\<close>




end
(*>*)


