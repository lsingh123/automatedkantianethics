theory carmojones_DDL_completeness imports carmojones_DDL

begin

text "This theory shows completeness for this logic with respect to the models presented in carmojonesDDl.thy."

section "Inference Rules"

subsection "Basic Inference Rules"

text "These inference rules are common to most modal and propostional logics"

lemma modus_ponens: assumes "\<Turnstile> A" assumes "\<Turnstile> (A \<^bold>\<rightarrow> B)"
  shows "\<Turnstile>B"
  using assms(1) assms(2) by blast
\<comment> \<open>Because I have not defined a ``derivable" operator, inference rules are written using assumptions.\<close>
\<comment> \<open>For further meta-logical work, defining metalogical operators may be useful\<close>

lemma nec: assumes "\<Turnstile>A" shows "\<Turnstile>(\<box>A)"
  by (simp add: assms)

lemma nec_a: assumes "\<Turnstile>A" shows "\<Turnstile>(\<box>\<^sub>aA)"
  by (simp add: assms)
lemma nec_p: assumes "\<Turnstile>A" shows "\<Turnstile>(\<box>\<^sub>pA)"
  by (simp add: assms)

subsection "Fancier Inference Rules"

text "These are new rules that Carmo and Jones introduced for this logic."

text "B and A must not contain w. not sure how to encode that requirement.
one option is to define a new free variables predicate and use that, but that requires a deeper embedding than I have.
If Benzmuller and Parent can survive without these inference rules, so can I"

section Axioms 

subsection Box

\<comment> \<open>$\Box$ is an S5 modal operator, which is where these axioms come from.\<close>
lemma K:
  shows "\<Turnstile> ((\<box>(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((\<box>A) \<^bold>\<rightarrow> (\<box>B)))"
  by blast

lemma T:
  shows "\<Turnstile> ((\<box>A) \<^bold>\<rightarrow>A)"
  by blast

lemma 5:
  shows "\<Turnstile> ((\<diamond>A) \<^bold>\<rightarrow> (\<box>(\<diamond>A)))"
  by blast

subsection O

text "This characterization of O comes from Carmo and Jones p 593"
lemma O_diamond:
  shows "\<Turnstile> (O{A|B} \<^bold>\<rightarrow> (\<diamond>(B \<^bold>\<and> A)))"
  using ax_5b ax_5a
  by metis
\<comment> \<open>A is only obligatory in a context if it can possibly be true in that context.\<close>

lemma O_C:
  shows "\<Turnstile>(((\<diamond>(A \<^bold>\<and> (B \<^bold>\<and> C))) \<^bold>\<and> (O{B|A} \<^bold>\<and> O{C|A})) \<^bold>\<rightarrow> (O{B\<^bold>\<and>C|A}) )"
  by (metis ax_5b ax_5c2)
\<comment> \<open>The conjunction of obligations in a context is obligatory in that context.\<close>
\<comment> \<open>The restriction $\Diamond (A \and B \and C)$ is to prevent contradictory obligations and contexts.\<close>

lemma O_SA:
  shows "\<Turnstile>(((\<box>(A \<^bold>\<rightarrow>B)) \<^bold>\<and> ((\<diamond>(A \<^bold>\<and>C)) \<^bold>\<and> O{C|B})) \<^bold>\<rightarrow> (O{C|A}))"
  using ax_5e by blast
\<comment> \<open>The principle of strengthening the antecedent.\<close>

lemma O_REA:
  shows "\<Turnstile>((\<box>(A \<^bold>\<equiv> B)) \<^bold>\<rightarrow> (O{C|A} \<^bold>\<equiv> O{C|B}))"
  using O_diamond ax_5e by blast
\<comment> \<open>Equivalence for equivalent contexts.\<close>

lemma O_contextual_REA:
  shows "\<Turnstile> ((\<box>(C \<^bold>\<rightarrow> (A \<^bold>\<equiv>B))) \<^bold>\<rightarrow> (O{A|C} \<^bold>\<equiv> O{B|C}))"
  by (metis ax_5b)
\<comment> \<open>The above lemma, but in some context C.\<close>

lemma O_nec:
  shows "\<Turnstile>(O{B|A} \<^bold>\<rightarrow> (\<box>O{B|A}))"
  by simp
\<comment> \<open>Obligations are necessarily obligated.\<close>

lemma ax_5b'': 
  shows "ob X Y \<longleftrightarrow> ob X (\<lambda>z. (Y z) \<and> (X z))"
  by (metis (no_types, lifting) ax_5b)

lemma O_to_O:
  shows "\<Turnstile>(O{B|A}\<^bold>\<rightarrow>O{(A\<^bold>\<rightarrow>B)|\<^bold>\<top>})"
proof-
  have "\<forall>X Y Z. (ob X Y \<and> (\<forall>w. X w \<longrightarrow> Z w)) \<longrightarrow> ob Z (\<lambda>w.(Z w \<and> \<not>X w) \<or> Y w)"
  by (smt ax_5d ax_5b ax_5b'')
  thus ?thesis
proof -
  obtain ii :: "(i \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> bool) \<Rightarrow> i" where
"\<forall>x0 x2. (\<exists>v3. (x2\<^bold>\<and>(\<^bold>\<not> x0)) v3) = x2\<^bold>\<and>(\<^bold>\<not> x0) (ii x0 x2)"
    by moura
  then have "\<forall>p pa pb. (\<not> ob p pa \<or> p\<^bold>\<and>\<^bold>\<not> pb (ii pb p)) \<or> ob pb (\<^bold>\<or> pb\<^bold>\<and>\<^bold>\<not> p pa)"
    by (metis (no_types) \<open>\<forall>X Y Z. ob X Y \<and> \<Turnstile>X\<^bold>\<rightarrow>Z \<longrightarrow> ob Z (\<^bold>\<or> Z\<^bold>\<and>\<^bold>\<not> X Y)\<close>)
  then show ?thesis
    by fastforce
qed
qed
\<comment> \<open>Moving from the dyadic to monadic obligation operators.\<close>

subsection "Possible Box"

\<comment> \<open> $\Box_p$ is a KT modal operator.\<close>
lemma K_boxp:
  shows "\<Turnstile>((\<box>\<^sub>p(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((\<box>\<^sub>pA) \<^bold>\<rightarrow> (\<box>\<^sub>pB)))"
  by blast
lemma T_boxp:
  shows "\<Turnstile>((\<box>\<^sub>pA) \<^bold>\<rightarrow> A)"
  using ax_4b by blast

subsection "Actual Box"

\<comment> \<open>$\Box_a$ is a KD modal operator.\<close>
lemma K_boxa:
  shows "\<Turnstile>((\<box>\<^sub>a(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((\<box>\<^sub>aA) \<^bold>\<rightarrow> (\<box>\<^sub>aB)))"
  by blast
lemma D_boxa:
  shows "\<Turnstile>((\<box>\<^sub>aA) \<^bold>\<rightarrow> (\<diamond>\<^sub>aA))"
  using ax_3a by blast

subsection "Relations Between the Modal Operators"

\<comment> \<open>Relation between $\Box$, $\Box_a$, and $\Box_p$.\<close>
lemma box_boxp:
  shows "\<Turnstile>((\<box>A) \<^bold>\<rightarrow> (\<box>\<^sub>pA))"
  by auto
lemma boxp_boxa:
  shows "\<Turnstile>((\<box>\<^sub>pA) \<^bold>\<rightarrow> (\<box>\<^sub>aA))"
  using ax_4a by blast

\<comment> \<open>Relation between actual/possible O and $\Box$.\<close>
lemma not_Oa:
  shows "\<Turnstile>((\<box>\<^sub>aA) \<^bold>\<rightarrow> ((\<^bold>\<not>(O\<^sub>a A)) \<^bold>\<and> (\<^bold>\<not>(O\<^sub>a (\<^bold>\<not>A)))))"
  using O_diamond by blast
lemma not_Op:
shows "\<Turnstile>((\<box>\<^sub>pA) \<^bold>\<rightarrow> ((\<^bold>\<not>(O\<^sub>p A)) \<^bold>\<and> (\<^bold>\<not>(O\<^sub>p (\<^bold>\<not>A)))))"
  using O_diamond by blast
lemma equiv_Oa:
  shows "\<Turnstile>((\<box>\<^sub>a(A \<^bold>\<equiv>B)) \<^bold>\<rightarrow> ((O\<^sub>a A) \<^bold>\<equiv> (O\<^sub>a B) ))"
  using O_contextual_REA by blast
lemma equiv_Op:
  shows "\<Turnstile>((\<box>\<^sub>p(A \<^bold>\<equiv>B)) \<^bold>\<rightarrow> ((O\<^sub>p A) \<^bold>\<equiv> (O\<^sub>p B) ))"
  using O_contextual_REA by blast

\<comment> \<open>relationships between actual possible O and $\Box$ and O proper.\<close>
lemma factual_detach_a:
  shows "\<Turnstile>(((O{B|A} \<^bold>\<and> (\<box>\<^sub>aA)) \<^bold>\<and> ((\<diamond>\<^sub>aB) \<^bold>\<and> (\<diamond>\<^sub>a(\<^bold>\<not>B)))) \<^bold>\<rightarrow> (O\<^sub>a B))"
  using O_SA by auto
lemma factual_detach_p:
  shows "\<Turnstile>(((O{B|A} \<^bold>\<and> (\<box>\<^sub>pA)) \<^bold>\<and> ((\<diamond>\<^sub>pB) \<^bold>\<and> (\<diamond>\<^sub>p(\<^bold>\<not>B)))) \<^bold>\<rightarrow> (O\<^sub>p B))"
  by (smt O_SA boxp_boxa)

end

