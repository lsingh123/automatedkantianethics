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

