(*Lavanya Singh, 2021*)
(*recreating Benzmuller and Parent's implementation: https://www.mi.fu-berlin.de/inf/groups/ag-ki/publications/dyadic-deontic-logic/C71.pdf*)
theory carmojones_DDL imports Main

begin
typedecl i (*type for a set of possible worlds*)
(*tau represents a DDL formula. a wff can be applied to a set of worlds*)
type_synonym t = "(i \<Rightarrow> bool)"

(*accessibility relations map a set of worlds to*)
consts av::"i \<Rightarrow> t" (*actual worlds*)
consts pv::"i \<Rightarrow> t" (*possible worlds*)
consts ob::"t \<Rightarrow> (t \<Rightarrow> bool)" (*set of propositions obligatory in context*)
consts cw::i (*current world*)

(*semantic embedding, so these are constraints on wf models*)
axiomatization where 
ax_3a: "\<exists>x. av(w)(x)" 
and ax_4a: "\<forall>x. av(w)(x) \<longrightarrow> pv(w)(x)" 
and ax_4b: "pv(w)(w)"
and ax_5a: "\<not>ob(X)(\<lambda>w. False)"
(*note that X(w) denotes w is a member of X*)
and ax_5b: "\<forall>w. ((X(w) \<and> Y(w)) \<longleftrightarrow> (X(w) \<and> Z(w))) \<longrightarrow> (ob(X)(Y) \<longleftrightarrow> ob(X)(Z))"
(*ob(X)(\<lambda>w. Fw) roughly means F\<in>ob(X)*)
and ax_5c: "(\<forall>Z. \<beta>(Z) \<longrightarrow> ob(X)(Z) \<and> (\<exists>Z. \<beta>(Z))) \<longrightarrow>
(\<exists>y.(\<forall>Z. (\<beta>(Z) \<longrightarrow> Z(y))) \<and> X(y)) \<longrightarrow> ob(X)(\<lambda>w. \<forall>Z.(\<beta>(Z) \<longrightarrow> Z(w)))"
and ax_5d: "(\<forall>w. (Y(w)\<longrightarrow>X(w)) \<and> (ob(X)(Y)) \<and> (\<forall>w. (X(w) \<longrightarrow>Z(w)))) \<longrightarrow>
(ob(Y)(\<lambda>w. Y(w) \<or> (Z(w) \<and> \<not>X(w))))"
and ax_5e: "((\<forall>w. (Y(w)\<longrightarrow>X(w))) \<and> ob(X)(Z) \<and> (\<exists>w.(Y(w) \<and> Z(w)))) \<longrightarrow> ob(Y)(Z)"

(*abbreviations as defined in Benzmuller&Parent, p9*)
abbreviation ddlneg::"t\<Rightarrow>t" ("\<^bold>\<not>") 
  where "\<^bold>\<not> A \<equiv> \<lambda>w. \<not> A(w)" 
abbreviation ddlor::"t\<Rightarrow>t\<Rightarrow>t" ("\<^bold>\<or>") 
  where "\<^bold>\<or> A B \<equiv> \<lambda>w. (A(w) \<or> B(w))"
abbreviation ddlbox::"t\<Rightarrow>t" ("\<box>") 
  where "\<box> A \<equiv> \<lambda>w.\<forall>y. A(y)" 
abbreviation ddldiamond::"t \<Rightarrow> t" ("\<diamond>")
  where "\<diamond>A \<equiv> \<^bold>\<not>(\<box>(\<^bold>\<not>A))"
abbreviation ddlob::"t\<Rightarrow>t\<Rightarrow>t" ("\<circle>{_|_}")
  where "\<circle>{B|A} \<equiv> \<lambda> w. ob(A)(B)"
abbreviation ddlboxa::"t\<Rightarrow>t" ("\<box>\<^sub>a")
  where "\<box>\<^sub>aA \<equiv> \<lambda>x.\<forall>y. (\<not> av(x)(y) \<or> A(y))"
abbreviation ddldiamonda::"t\<Rightarrow>t" ("\<diamond>\<^sub>a")
  where "\<diamond>\<^sub>aA \<equiv> \<^bold>\<not>(\<box>\<^sub>a(\<^bold>\<not>A))"
abbreviation ddlboxp::"t\<Rightarrow>t" ("\<box>\<^sub>p")
  where "\<box>\<^sub>pA \<equiv> \<lambda>x.\<forall>y. (\<not> pv(x)(y) \<or> A(y))"
abbreviation ddldiamondp::"t\<Rightarrow>t" ("\<diamond>\<^sub>p")
  where "\<diamond>\<^sub>pA \<equiv> \<^bold>\<not>(\<box>\<^sub>a(\<^bold>\<not>A))"
abbreviation ddloba::"t\<Rightarrow>t" ("\<circle>\<^sub>a")
  where "\<circle>\<^sub>aA \<equiv> \<lambda>x. ob(av(x))(A) \<and> (\<exists>y.(av(x)(y) \<and> \<not>A(y)))"
abbreviation ddlobp::"t\<Rightarrow>t" ("\<circle>\<^sub>p")
  where "\<circle>\<^sub>pA \<equiv> \<lambda>x. ob(pv(x))(A) \<and> (\<exists>y.(pv(x)(y) \<and> \<not>A(y)))"
(*don't need these, but they will make my life easier*)
abbreviation ddland::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<and>_")
  where "A\<^bold>\<and> B \<equiv> \<lambda>w. (A(w) \<and> B(w))"
abbreviation ddlif::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<rightarrow>_")
  where "A\<^bold>\<rightarrow>B \<equiv> \<lambda>w. (\<not> A(w) \<or> B(w))"
abbreviation ddlequiv::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<equiv>_")
  where "(A\<^bold>\<equiv>B) \<equiv> ((A\<^bold>\<rightarrow>B) \<^bold>\<and> ( B\<^bold>\<rightarrow>A))"
abbreviation ddltrue::"t" ("\<top>")
  where "\<top> \<equiv> \<lambda>w. True"
abbreviation ddlob_normal::"t\<Rightarrow>t" ("\<circle>_")
  where "(\<circle>A) \<equiv> (\<circle>{A|\<top>}) "
(*validity*)
abbreviation ddlvalid::"t\<Rightarrow>bool" ("\<Turnstile>_")
  where "\<Turnstile>A \<equiv> \<forall>w. A(w)"
abbreviation ddlvalidcw::"t\<Rightarrow>bool" ("\<Turnstile>\<^sub>c_")
  where "\<Turnstile>\<^sub>cA \<equiv> A(cw)"

(*nitpick shows consistency*)
lemma True nitpick [satisfy,user_axioms,show_all,format=2] oops 

end
