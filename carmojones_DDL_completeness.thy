theory carmojones_DDL_completeness imports carmojones_DDL

begin

(*Completeness.*)

(*inference rules*)
lemma modus_ponens:
  assumes "\<Turnstile> A"
  assumes "\<Turnstile> (A \<^bold>\<rightarrow> B)"
  shows "\<Turnstile>B"
  using assms(1) assms(2) by blast
lemma nec:
  assumes "\<Turnstile>A"
  shows "\<Turnstile>(\<box>A)"
  by (simp add: assms)
lemma nec_a:
 assumes "\<Turnstile>A"
  shows "\<Turnstile>(\<box>\<^sub>aA)"
  by (simp add: assms)
lemma nec_p:
 assumes "\<Turnstile>A"
  shows "\<Turnstile>(\<box>\<^sub>pA)"
  by (simp add: assms)
(*fancier inference rules*)
lemma Oa_boxaO:
  assumes "\<Turnstile>(B \<^bold>\<rightarrow> (\<lambda>w. (\<^bold>\<not>(\<box>((\<circle>\<^sub>aA) \<^bold>\<rightarrow> ((\<box>\<^sub>aw) \<^bold>\<and> \<circle>{A|w}))))))"
  shows "\<top>"

(*\<box> is an S5 modal operator*)
lemma K:
  shows "\<Turnstile> ((\<box>(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((\<box>A) \<^bold>\<rightarrow> (\<box>B)))"
  by blast
lemma T:
  shows "\<Turnstile> ((\<box>A) \<^bold>\<rightarrow>A)"
  by blast
lemma 5:
  shows "\<Turnstile> ((\<diamond>A) \<^bold>\<rightarrow> (\<box>(\<diamond>A)))"
  by blast

(*Characterization of O, CJ p 593*)
lemma O_diamond:
  shows "\<Turnstile> (\<circle>{A|B} \<^bold>\<rightarrow> (\<diamond>(B \<^bold>\<and> A)))"
  using ax_5b ax_5a
  by metis
lemma O_C:
  shows "\<Turnstile>(((\<diamond>(A \<^bold>\<and> (B \<^bold>\<and> C))) \<^bold>\<and> (\<circle>{B|A} \<^bold>\<and> \<circle>{C|A})) \<^bold>\<rightarrow> (\<circle>{B\<^bold>\<and>C|A}) )"
  by (metis (no_types, lifting) ax_5b)
lemma O_SA:
  shows "\<Turnstile>(((\<box>(A \<^bold>\<rightarrow>B)) \<^bold>\<and> ((\<diamond>(A \<^bold>\<and>C)) \<^bold>\<and> \<circle>{C|B})) \<^bold>\<rightarrow> (\<circle>{C|A}))"
  using ax_5e by blast
lemma O_REA:
  shows "\<Turnstile>((\<box>(A \<^bold>\<equiv> B)) \<^bold>\<rightarrow> (\<circle>{C|A} \<^bold>\<equiv> \<circle>{C|B}))"
  using O_diamond ax_5e by blast
lemma O_contextual_REA:
  shows "\<Turnstile> ((\<box>(C \<^bold>\<rightarrow> (A \<^bold>\<equiv>B))) \<^bold>\<rightarrow> (\<circle>{A|C} \<^bold>\<equiv> \<circle>{B|C}))"
  by (metis ax_5b)
lemma O_nec:
  shows "\<Turnstile>(\<circle>{B|A} \<^bold>\<rightarrow> (\<box>\<circle>{B|A}))"
  by simp
lemma O_to_O:
  shows "\<Turnstile>(\<circle>{B|A} \<^bold>\<rightarrow> \<circle>(A \<^bold>\<rightarrow> B))"
  by (metis (no_types, lifting) O_REA ax_5a ax_5b)

(*characterization of \<box>\<^sub>p as a KT modal operator*)
lemma K_boxp:
  shows "\<Turnstile>((\<box>\<^sub>p(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((\<box>\<^sub>pA) \<^bold>\<rightarrow> (\<box>\<^sub>pB)))"
  by blast
lemma T_boxp:
  shows "\<Turnstile>((\<box>\<^sub>pA) \<^bold>\<rightarrow> A)"
  using ax_4b by blast

(*characterization of \<box>\<^sub>a as a KD modal operator*)
lemma K_boxa:
  shows "\<Turnstile>((\<box>\<^sub>a(A \<^bold>\<rightarrow> B)) \<^bold>\<rightarrow> ((\<box>\<^sub>aA) \<^bold>\<rightarrow> (\<box>\<^sub>aB)))"
  by blast
lemma D_boxa:
  shows "\<Turnstile>((\<box>\<^sub>aA) \<^bold>\<rightarrow> (\<diamond>\<^sub>aA))"
  using ax_3a by blast

(*relationships between \<box>, \<box>\<^sub>a, and \<box>\<^sub>p*)
lemma box_boxp:
  shows "\<Turnstile>((\<box>A) \<^bold>\<rightarrow> (\<box>\<^sub>pA))"
  by auto
lemma boxp_boxa:
  shows "\<Turnstile>((\<box>\<^sub>pA) \<^bold>\<rightarrow> (\<box>\<^sub>aA))"
  using ax_4a by blast

(*relationships between \<circle>\<^sub>a\<^sub>\\<^sub>p and \<box>\<^sub>a\<^sub>\\<^sub>p*)
lemma not_Oa:
  shows "\<Turnstile>((\<box>\<^sub>aA) \<^bold>\<rightarrow> ((\<^bold>\<not>(\<circle>\<^sub>aA)) \<^bold>\<and> (\<^bold>\<not>(\<circle>\<^sub>a(\<^bold>\<not>A)))))"
  using O_diamond by blast
lemma not_Op:
shows "\<Turnstile>((\<box>\<^sub>pA) \<^bold>\<rightarrow> ((\<^bold>\<not>(\<circle>\<^sub>pA)) \<^bold>\<and> (\<^bold>\<not>(\<circle>\<^sub>p(\<^bold>\<not>A)))))"
  using O_diamond by blast
lemma equiv_Oa:
  shows "\<Turnstile>((\<box>\<^sub>a(A \<^bold>\<equiv>B)) \<^bold>\<rightarrow> ((\<circle>\<^sub>aA) \<^bold>\<equiv> (\<circle>\<^sub>aB) ))"
  using O_contextual_REA by blast
lemma equiv_Op:
  shows "\<Turnstile>((\<box>\<^sub>p(A \<^bold>\<equiv>B)) \<^bold>\<rightarrow> ((\<circle>\<^sub>pA) \<^bold>\<equiv> (\<circle>\<^sub>pB) ))"
  using O_contextual_REA by blast

(*relationships between \<circle>, \<circle>\<^sub>a\<^sub>\\<^sub>p, \<box>\<^sub>a\<^sub>\\<^sub>p *)
lemma factual_detach_a:
  shows "\<Turnstile>(((\<circle>{B|A} \<^bold>\<and> (\<box>\<^sub>aA)) \<^bold>\<and> ((\<diamond>\<^sub>aB) \<^bold>\<and> (\<diamond>\<^sub>a(\<^bold>\<not>B)))) \<^bold>\<rightarrow> (\<circle>\<^sub>aB))"
  using O_SA by auto
lemma factual_detach_p:
  shows "\<Turnstile>(((\<circle>{B|A} \<^bold>\<and> (\<box>\<^sub>pA)) \<^bold>\<and> ((\<diamond>\<^sub>pB) \<^bold>\<and> (\<diamond>\<^sub>p(\<^bold>\<not>B)))) \<^bold>\<rightarrow> (\<circle>\<^sub>pB))"
  by (smt O_SA boxp_boxa)




