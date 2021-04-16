(*<*) theory paper224 imports paper22

begin

text "This theory shows completeness for this logic with respect to the models presented in carmojonesDDl.thy."

section "Inference Rules"

subsection "Basic Inference Rules"

text "These inference rules are common to most modal and propostional logics"(*>*)

text \<open>\textbf{Modus Ponens}\<close>

lemma modus_ponens: assumes "\<Turnstile> A" assumes "\<Turnstile> (A \<^bold>\<rightarrow> B)"
  shows "\<Turnstile>B"
  using assms(1) assms(2) by blast
\<comment> \<open>Because I have not defined a ``derivable" operator, inference rules are written using assumptions.\<close>
\<comment> \<open>The rule {\color{blue} blast} is a classical reasoning method that comes with Isabelle out of the box. @{cite isabelle}\<close>
\<comment>\<open>This is an example of a metalogical proof in this system using the validity operator.\<close>
(*<*)
lemma nec: assumes "\<Turnstile>A" shows "\<Turnstile>(\<box>A)"
  by (simp add: assms)

lemma nec_a: assumes "\<Turnstile>A" shows "\<Turnstile>(\<box>\<^sub>aA)"
  by (simp add: assms)
lemma nec_p: assumes "\<Turnstile>A" shows "\<Turnstile>(\<box>\<^sub>pA)"
  by (simp add: assms)

subsection "Fancier Inference Rules"

text "These are new rules that Carmo and Jones introduced for this logic."

lemma Oa_boxaO:
  assumes "\<Turnstile>(B \<^bold>\<rightarrow> ((\<^bold>\<not>(\<box>((O\<^sub>a A) \<^bold>\<rightarrow> ((\<box>\<^sub>aw) \<^bold>\<and> O{A|w}))))))"
  shows "\<Turnstile>(B \<^bold>\<rightarrow> (\<^bold>\<not>(\<diamond>(O\<^sub>a A))))"
  oops
lemma Oa_boxpO:
  assumes "\<Turnstile>(B \<^bold>\<rightarrow> ((\<^bold>\<not>(\<box>((O\<^sub>p A) \<^bold>\<rightarrow> ((\<box>\<^sub>pw) \<^bold>\<and> O{A|w}))))))"
  shows "\<Turnstile>(B \<^bold>\<rightarrow> (\<^bold>\<not>(\<diamond>(O\<^sub>p A))))"
  oops
\<comment> \<open>The oops indicates that we were not able to find a proof for these lemmas.\<close>


text "B and A must not contain w. not sure how to encode that requirement.
one option is to define a new free variables predicate and use that, but that requires a deeper embedding than I have.
May become a problem later"

section Axioms 

subsection Box
(*>*)

text \<open>Another relevant operator for our purposes is $\Box$, the modal necessity operator. In 
this system, $\Box$ behaves as an S5 modal necessity operator.\<close>
lemma K:
  shows "\<Turnstile> ((\<box>(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((\<box>A) \<^bold>\<rightarrow> (\<box>B)))" by blast

lemma T:
  shows "\<Turnstile> ((\<box>A) \<^bold>\<rightarrow>A)" by blast

lemma 5:
  shows "\<Turnstile> ((\<diamond>A) \<^bold>\<rightarrow> (\<box>(\<diamond>A)))" by blast

(*<*)
subsection O
(*>*)

text "As mentioned earlier, the obligation operator is most interesting for my purposes. Here are some 
of its properties."

lemma O_diamond:
  shows "\<Turnstile> (O{A|B} \<^bold>\<rightarrow> (\<diamond>(B \<^bold>\<and> A)))"
  using ax_5b ax_5a
  by metis
\<comment> \<open>A is only obligatory in a context if it can possibly be true in that context. This is meant to 
prevent impossible obligations in a context.\<close>

(*<*)
lemma O_C:
  shows "\<Turnstile>(((\<diamond>(A \<^bold>\<and> (B \<^bold>\<and> C))) \<^bold>\<and> (O{B|A} \<^bold>\<and> O{C|A})) \<^bold>\<rightarrow> (O{B\<^bold>\<and>C|A}) )"
  by (metis ax_5c2)
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
(*>*)

lemma O_nec:
  shows "\<Turnstile>(O{B|A} \<^bold>\<rightarrow> (\<box>O{B|A}))"
  by simp
\<comment> \<open>Obligations are necessarily obligated. This axiom is faithful to Kant's interpretation of ethics 
and is evidence of Deontic Logic's power in representing Kant's theory. Kant claimed that the categorical
imperative was not contingent on any facts about the world, but instead a property of the concept of 
morality itself @{cite groundwork}. Under this view, obligation should not be world-specific.\<close>

(*<*)
lemma ax_5b'': 
  shows "ob X Y \<longleftrightarrow> ob X (\<lambda>z. (Y z) \<and> (X z))"
  by (metis (no_types, lifting) ax_5b)
(*>*)

text \<open>Below is an example of a more involved proof in Isabelle. This proof was almost completely automatically
generated. The property itself here is not very interesting for my purposes because I will rarely mix the dyadic
and monadic obligation operators.\<close>

lemma O_to_O:
  shows "\<Turnstile>(O{B|A}\<^bold>\<rightarrow>O{(A\<^bold>\<rightarrow>B)|\<^bold>\<top>})"
proof-
  have "\<forall>X Y Z. (ob X Y \<and> (\<forall>w. X w \<longrightarrow> Z w)) \<longrightarrow> ob Z (\<lambda>w.(Z w \<and> \<not>X w) \<or> Y w)"
\<comment>\<open>I had to manually specify this subgoal, but once I did Isabelle was able to prove it automatically.\<close>
    by (smt ax_5d ax_5b ax_5b'')
\<comment>\<open>Isabelle's proof-finding tool, Sledgehammer  @{cite sledgehammer}, comes with out-of-the-box support for smt solving @{cite smt}.\<close>
  thus ?thesis
  proof -
    have f1: "\<forall>p pa pb. ((\<not> (ob p pa)) \<or> (\<exists>i. (p\<^bold>\<and>(\<^bold>\<not> pb)) i)) \<or> (ob pb ((pb\<^bold>\<and>(\<^bold>\<not> p))\<^bold>\<or>  pa))"
      using \<open>\<forall>X Y Z. ob X Y \<and> (\<Turnstile>(X\<^bold>\<rightarrow>Z)) \<longrightarrow> ob Z ( (Z\<^bold>\<and>(\<^bold>\<not> X))\<^bold>\<or> Y)\<close> by force
    obtain ii :: "(i \<Rightarrow> bool) \<Rightarrow> (i \<Rightarrow> bool) \<Rightarrow> i" where
      "\<forall>x0 x2. (\<exists>v3. (x2\<^bold>\<and>(\<^bold>\<not> x0)) v3) = (x2\<^bold>\<and>(\<^bold>\<not> x0)) (ii x0 x2)"
      by moura
    then have "\<forall>p pa pb. ((\<not> ob p pa) \<or> (p\<^bold>\<and>(\<^bold>\<not> pb)) (ii pb p)) \<or> ob pb ( (pb\<^bold>\<and>(\<^bold>\<not> p))\<^bold>\<or> pa)"
      using f1 by presburger
    then show ?thesis
      by fastforce
  qed
\<comment>\<open>This entire Isar style proof was automatically generated using Sledgehammer.\<close>
qed

text \<open>The implementation of DDL showcases some of the useful features of Isabelle. Abbreviations allow
us to embed the syntax of DDL into HOL without defining an entire abstract sytax tree. Automated 
support for proof-finding using Sledgehammer makes proving lemmas trivial, and proving more complex theorems
far easier. Nitpick's model finding ability is useful to check for consistency and create countermodels.\<close>
(*<*)
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

\<comment> \<open>Relation between actual and possible O and $\Box$.\<close>
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

\<comment> \<open>relationships between actual and possible O and $\Box$ and O proper.\<close>
lemma factual_detach_a:
  shows "\<Turnstile>(((O{B|A} \<^bold>\<and> (\<box>\<^sub>aA)) \<^bold>\<and> ((\<diamond>\<^sub>aB) \<^bold>\<and> (\<diamond>\<^sub>a(\<^bold>\<not>B)))) \<^bold>\<rightarrow> (O\<^sub>a B))"
  using O_SA by auto
lemma factual_detach_p:
  shows "\<Turnstile>(((O{B|A} \<^bold>\<and> (\<box>\<^sub>pA)) \<^bold>\<and> ((\<diamond>\<^sub>pB) \<^bold>\<and> (\<diamond>\<^sub>p(\<^bold>\<not>B)))) \<^bold>\<rightarrow> (O\<^sub>p B))"
  by (smt O_SA boxp_boxa)

end
(*>*)
