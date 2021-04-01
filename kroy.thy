theory kroy
  imports carmojones_DDL

begin

text "This theory will contain a formalization of the CI based on Moshe Kroy's partial formalization. @{cite kroy}}"

section "The Substitution Operator"

subsection Definition

typedecl s \<comment>\<open>s is the type for a ``subject", like the subject of a sentence\<close>
\<comment>\<open>Intuitively, we need some notion of ``x does action", which we can write as ``x is the subject of the sentence 'does action'"\<close>

type_synonym os = "(s \<Rightarrow> t)"
\<comment>\<open>An open sentence is a generalized version of Kroy's substitution operator @{cite kroy} 196\<close>
\<comment>\<open>``does action" is an open sentence that can be instantiated with a subject\<close>
\<comment>\<open>``P sub (d/e)" can be written as ``S(e)", where S(d) = P\<close>
\<comment>\<open>So the terms that we substitute into are actually instantiations of an open sentence, and substitution just requires re-instantiating the open sentence with a different subject\<close>

subsection Abbreviations

abbreviation os_neg::"os \<Rightarrow> os" ("\<^emph>\<not>_")
  where "(\<^emph>\<not>A) \<equiv> \<lambda>x. \<^bold>\<not>(A(x))"
abbreviation os_and::"os \<Rightarrow> os \<Rightarrow> os" ("_\<^emph>\<and>_")
  where "(A \<^emph>\<and> B) \<equiv> \<lambda>x. ((A(x)) \<^bold>\<and> (B(x)))"
abbreviation os_or::"os \<Rightarrow> os \<Rightarrow> os" ("_\<^emph>\<or>_")
  where "(A \<^emph>\<or> B) \<equiv> \<lambda>x. ((A(x)) \<^bold>\<or> (B(x)))"
abbreviation os_ob::"os \<Rightarrow> os" ("\<^emph>O{_}")
  where "\<^emph>O{A} \<equiv> \<lambda>x. (O {A(x)})"
\<comment>\<open>We could probably do without these abbreviations, but they will simplify the notiation a bit and unify it with Kroy's original paper.\<close>

abbreviation ddl_permissible::"t\<Rightarrow>t" ("P {_}")
  where "P {A} \<equiv> \<^bold>\<not> (O {\<^bold>\<not> A})"
abbreviation os_permissible::"os\<Rightarrow>os" ("\<^emph>P {_}")
  where "\<^emph>P {A} \<equiv> \<lambda>x. P {A(x)}"
\<comment>\<open>Carmo and Jones don't make much use of permissibility, but we will find it useful here.\<close>

section "Differences Between Kroy's Logic (Kr) and DDL"

text "@{cite kroy} uses a different logic than DDL. Let's see if the semantics that Kr requires hold in DDL"

lemma permissible_semantic:
  fixes A w
  assumes "P {A} w"
  shows "\<exists>x. (\<forall>B. B(x) \<longrightarrow> ob((\<lambda>w. True))(B) \<and> A(x))"
  nitpick[user_axioms] oops
\<comment>\<open>TBC...this is definitely wrong\<close>

section "The Categorical Imperative"

abbreviation CI::"bool" where "CI \<equiv> \<forall>w. (\<exists>p. P {p}w \<longrightarrow> (\<forall>x. P {x}w))"

lemma CI:
  fixes Lav::s
  fixes P::os
  shows " \<forall>w. (\<exists>p. P {p}w \<longrightarrow> (\<forall>x. P {x}w))"
  oops
\<comment>\<open>ugh\<close>

end