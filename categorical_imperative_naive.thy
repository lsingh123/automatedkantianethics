theory categorical_imperative_naive imports carmojones_DDL_completeness

begin

section "The Categorical Imperative"

subsection "Simple Formulation of the Formula of Universal Law"

text "This is my second attempt at formalizing the Formula of Universal Law"

abbreviation ddlpermissable::"t\<Rightarrow>t" ("P_")
  where "(P A) \<equiv> (\<^bold>\<not>(O {\<^bold>\<not>A}))"
\<comment> \<open>This operator represents permissibility\<close>
\<comment> \<open>Will be useful when discussing the categorical imperative\<close>
\<comment> \<open>Something is permissible if it is not prohibited\<close>
\<comment> \<open>Something is prohibited if its negation is obligatory\<close>

text "Let's consider a naive reading of the Formula of Universal Law (FUL).
From the Groundwork, 'act only in accordance with that maxim through which you can at the same time will that it become a universal law'.
What does this mean in DDL? One interpretation is if A is not necessarily permissible, then its negation is obligated."

axiomatization where
FUL_1: "\<Turnstile> ((\<^bold>\<not>(\<box> (P A))) \<^bold>\<rightarrow> (O {(\<^bold>\<not>A)}))"

subsection "Basic Tests"

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

text "Let's try a weaker assumption: Not everyone can lie."

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
  then have "\<Turnstile>(\<^bold>\<not> (O {A \<^bold>\<and> B}))" by (smt carmojones_DDL_completeness.O_diamond)
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
end
    


