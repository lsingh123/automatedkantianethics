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

lemma True nitpick [satisfy,user_axioms,show_all,format=2] oops 
\<comment> \<open>Nitpick tells us that the FUL is consistent\<close>


lemma something_is_obligatory:
  shows "\<forall> w. \<exists> A. O {A} w"
  oops
\<comment> \<open>We might think that in every world we want something to be obligated. \<close>
\<comment> \<open>Sadly, Sledgehammer times out trying to prove this. Let's relax this\<close>

lemma something_is_obligatory_relaxed:
  shows "\<exists> A w. O {A} w"
  oops
\<comment> \<open>Wow, even the relaxed version times out!\<close>

text "Maybe the problem is that currently, everything is permissible. What if we add something impermissible?"

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
  oops
\<comment> \<open>No proof found. Makes sense:\<close>
\<comment> \<open>This version of FUL simply universalizes across worlds (using the $\Box$ operator),\<close>
\<comment> \<open>But NOT across people, which is really what the most obvious reading of FUL implies\<close>

subsection "Metaethical Tests"

lemma FUL_alternate:
  shows "\<Turnstile> ((\<diamond> (O {\<^bold>\<not> A})) \<^bold>\<rightarrow> (O {\<^bold>\<not> A}))"
  by simp
\<comment> \<open>One problem becomes obvious if we look at the definition of permissible\<close>
\<comment> \<open>Expanding the FUL gives us: $\sim \Box \sim O(\sim A) \longrightarrow O(\sim A)$\<close>
\<comment> \<open>By modal duals we get that $\diamond O(\sim A) \longrightarrow O(\sim A)$\<close>
\<comment> \<open>This means that if something is possibly prohibited, it is in fact prohibited.\<close>
\<comment> \<open>I'm not convinced that this is a desirable property of an ethical theory.\<close>

axiomatization where
ax_morally_neutral: "\<exists>A.(((\<^bold>\<not> (O {A})) \<^bold>\<and> (O {\<^bold>\<not> A}))) w"

lemma True nitpick [satisfy,user_axioms,show_all,format=2] oops 
\<comment> \<open>We might imagine that we want to allow for ``morally neutral" statements\<close>
\<comment> \<open>Ex: it is neither obligated nor prohibited that I eat lunch today.\<close>
\<comment> \<open>Nitpick successfully finds a model with morally neutral statements! \<close>

end



    


