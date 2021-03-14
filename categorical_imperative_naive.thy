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

lemma True nitpick [satisfy,user_axioms,show_all,format=2] oops 
\<comment> \<open>Nitpick tells us that the FUL is consistent\<close>

text "I'm going to test this formulation now."

\<comment> \<open>lemma test1:
  shows $\forall w. \exists A. O \{A\}w$
\<comment> \<open>We might think that in every world we want something to be obligated. \<close>
\<comment> \<open>Sadly, Sledgehammer times out trying to prove this. Let's relax this\<close>

lemma test1_relaxed:
  shows $\exists A w. O \{A\} w$
Wow, even the relaxed version times out!
One problem becomes obvious if we look at the definition of permissible
Expanding the FUL gives us: $\sim \square \sim O(\sim A)$ $\longrightarrow$ $O(\sim A)$
By modal duals we get that diamond O($\sim$A) $\longrightarrow$ O($\sim$A) which is clearly not a desirable property of an ethical theory\<close>

text "Interestingly Isabelle struggles to show even this very obvious lemma."

end



    


