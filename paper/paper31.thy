(*<*) theory paper31 imports paper224

begin

(*>*)

section "The Categorical Imperative"

text "In this section, I will present three formulations of the categorical imperative. In Section 3.1, I will 
consider a simple, naive formulation of the formula of universal law. This formulation is, as I will 
show, clearly not a good ethical rule. The purpose of this section is to explore the kinds of ethical
tests that Isabelle can carry out. In Section 3.2, I will explore Moshe Kroy's @{cite kroy} partial formalization of 
the first two formulations of the categorical imperative. I will also explore drawbacks of this attempt, 
particularly in the lack of the machinery to handle the important Kantian concept of a maxim: an action 
performed for a particular end. In Section 3.3, I will present my own improved
formalization of the categorical imperative."

subsection "Naive Formulation of the Formula of Universal Law"

text "This section presents a simple and intuitive formalization of the formula of universal law, which 
is to will only those maxims that you would simultaneously will universalized. The universalizability 
test presents negative obligations: if a maxim passes the universalizability test, it is permissible. Else,
it is prohibited. In order to appropriately formalize this, we need some notion of permissibility."

abbreviation ddlpermissable::"t\<Rightarrow>t" ("P_")
  where "(P A) \<equiv> (\<^bold>\<not>(O {\<^bold>\<not>A}))"
\<comment>\<open>An act $A$ is permissible if its negation is not obligated. For example, buying a red folder is 
permissible because I am not required to refrain from buying a red folder.\<close>
(*<*)
\<comment> \<open>This operator represents permissibility\<close>
\<comment> \<open>Will be useful when discussing the categorical imperative\<close>
\<comment> \<open>Something is permissible if it is not prohibited\<close>
\<comment> \<open>Something is prohibited if its negation is obligatory\<close>
(*>*)

text "This naice formalization will require very little additional logical machinery, but more complex
formalizations may require additional logic concepts beyond just that of permissibility. 

Let's now consider a naive reading of the Formula of Universal Law (FUL): 'act only in accordance 
with that maxim through which you can at the same time will that it become a universal law' @{cite groundwork}.
An immediate translation to DDL is that if A is not necessary permissible then it is prohibited. In other
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
on the classical Kantian notion of an ideal moral world @{cite idealtheory}."

(*<*)subsection "Basic Tests"

lemma True nitpick [satisfy,user_axioms,format=2] oops
\<comment> \<open>``Nitpick found a model for card i = 1:

  Empty assignment"\<close>
\<comment> \<open>Nitpick tells us that the FUL is consistent\<close>
\<comment> \<open>``oops" after Nitpick does not mean Nitpick failed.\<close>

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

subsection "Specifying the Model"

text "Let's specify the model. What if we add something impermissible?"

consts M::"t"
abbreviation murder_wrong::"bool" where "murder_wrong \<equiv> \<Turnstile>(O {\<^bold>\<not> M})"

lemma something_is_obligatory_2:
  assumes murder_wrong
  shows "\<forall> w. \<exists> A. O {A} w"
  using assms by auto
\<comment> \<open>It works this time, but I think ``murder wrong" might be too strong of an assumption\<close>

abbreviation poss_murder_wrong::"bool" where "poss_murder_wrong \<equiv> \<Turnstile>(\<diamond> (O {\<^bold>\<not> M}))"

lemma wrong_if_posibly_wrong:
  assumes poss_murder_wrong
  shows murder_wrong
  using assms by blast
\<comment>\<open>This lemma holds and uses a slightly weaker assumption. This also seems to get closer to the ``heart" of 
this naive interpretation. We really want to say that if something isn't necessarily obligated, it's not obligated anywhere."\<close>


text "Let's try an even weaker assumption: Not everyone can lie."

typedecl person
consts lies::"person\<Rightarrow>t"
consts me::"person"

lemma breaking_promises:
  assumes "\<not> (\<forall>x. lie(x) cw) \<and> (lie(me) cw)"
  shows "(O {\<^bold>\<not> (lie(me))}) cw"
  nitpick [user_axioms]
  oops
\<comment> \<open>No proof found. Makes sense:\<close>
\<comment> \<open>This version of FUL simply universalizes across worlds (using the $\Box$ operator),\<close>
\<comment> \<open>But NOT across people, which is really what the most obvious reading of FUL implies\<close>
\<comment>\<open>``Nitpick found a counterexample for card person = 2 and card i = 2:

  Free variable:
    lie = ($\lambda x. \_$)($p_1$ := ($\lambda x. \_$)($i_1$ := True, $i_2$ := False), $p_2$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := False))"\<close>

lemma universalizability:
  assumes "\<Turnstile> O {(lie(me))}"
  shows "\<forall>x. \<Turnstile> (O {(lie(x))})"
  nitpick [user_axioms] oops
\<comment>\<open>Nitpick found a counterexample for card person = 2 and card i = 2:

  Free variable:
    lie = ($\lambda x. \_$)($p_1$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := True), $p_2$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := False))
  Skolem constant:
    x = $p_2$\<close>
\<comment>\<open>This lemma demonstrates the point even more clearly - we really want to think that obligations are consistent 
across people, but because we don't have a notion of agency, we don't have that property. \<close>

subsection "Consistent Sentences"

text "The above section tested validity. We might also be interested in some weaker properties"
text "Let's test whether certain sentences are consistent - can we find a model that makes them true?"

lemma permissible:
  fixes A
  shows "((\<^bold>\<not> (O {A})) \<^bold>\<and> (\<^bold>\<not> (O {\<^bold>\<not> A}))) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>``Nitpick found a model for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)"\<close>
\<comment>\<open>Awesome! Permissible things are consistent - clearly we've fixed the bug from categorical\_imperative\_1\<close>
\<comment>\<open>Note that apparently it's not clear {@cite kitcher} if Kant actually thought that permissibility was a coherent concept. Either way, 
I think permissibility is a pretty widely accepted ethical phenomenon.\<close>

lemma conflicting_obligations:
  fixes A
  shows "(O {A} \<^bold>\<and> O {\<^bold>\<not> A}) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>``Nitpick found a model for card i = 2:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)"\<close>
\<comment>\<open>Oh no! Nitpick found a model with conflicting obligations - that's bad!\<close>

subsection "Metaethical Tests"

lemma FUL_alternate:
  shows "\<Turnstile> ((\<diamond> (O {\<^bold>\<not> A})) \<^bold>\<rightarrow> (O {\<^bold>\<not> A}))"
  by simp
\<comment> \<open>One problem becomes obvious if we look at the definition of permissible\<close>
\<comment> \<open>Expanding the FUL gives us: $\sim \Box \sim O(\sim A) \longrightarrow O(\sim A)$\<close>
\<comment> \<open>By modal duals we get that $\diamond O(\sim A) \longrightarrow O(\sim A)$\<close>
\<comment> \<open>This means that if something is possibly prohibited, it is in fact prohibited.\<close>
\<comment> \<open>I'm not convinced that this is a desirable property of an ethical theory.\<close>

lemma arbitrary_obligations:
  fixes A::"t"
  shows "O {A} w"
  nitpick [user_axioms=true] oops
\<comment> \<open>``Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)"\<close>
\<comment>\<open>This is good! Shows us that any arbitrary term isn't obligatory.\<close>

lemma removing_conflicting_obligations:
  assumes "\<forall>A. \<Turnstile> (\<^bold>\<not> (O {A} \<^bold>\<and> O {\<^bold>\<not> A}))"
  shows True
  nitpick [satisfy,user_axioms,format=2] oops
\<comment>\<open>`` Nitpick found a model for card i = 1:

  Empty assignment"\<close>
\<comment>\<open>We can disallow conflicting obligations and the system is still consistent - that's good.\<close>

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
  thus ?thesis oops
\<comment>\<open>@{cite KorsgaardFUL} mentions that if two maxims imply a contradiction, they must not be willed.\<close>
\<comment>\<open>Above is a natural interpretation of this fact that we are, so far, unable to prove.\<close>
\<comment>\<open>``Nitpick found a counterexample for card i = 2:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := True, $i_2$ := False)
    B = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)"\<close>
\<comment>\<open>This isn't actually a theorem of the logic as formed - clearly this is a problem.\<close>

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


lemma distribute_obligations_onlyif:
  assumes  "\<Turnstile> (O {A} \<^bold>\<and> O {B})"
  shows "\<Turnstile> O {A \<^bold>\<and> B}"
  nitpick [user_axioms] oops
\<comment>\<open>``Nitpick found a counterexample for card i = 2:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := True, $i_2$ := False)
    B = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)"\<close>
\<comment>\<open>If this was a theorem, then contradictory obligations would be ruled out pretty immediately.\<close>
\<comment>\<open>Note that all of this holds in CJ's original DDL as well, not just my modified version.\<close>
\<comment>\<open>We might imagine adding this equivalence to our system.\<close>

lemma ought_implies_can:
  shows "\<forall>A. \<Turnstile> (O {A} \<^bold>\<rightarrow> (\<diamond>A))"
  using O_diamond by blast
\<comment>\<open>``ought implies can" is often attributed to Kant and is a pretty basic principle - you can't be obligated to do the impossible.
I'm not surprised that our base logic has this as an axiom. It's often said to be the central motivation behind deontic logics.\<close>


end
(*>*)


