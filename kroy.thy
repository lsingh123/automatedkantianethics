theory kroy
  imports carmojones_DDL

begin

text "This theory will contain a formalization of the CI based on Moshe Kroy's partial formalization. @{cite kroy}"

section "Kroy's Formalization of the Categorical Imperative"

subsection "The Substitution Operator"

subsubsection Definition

typedecl s \<comment>\<open>s is the type for a ``subject", like the subject of a sentence\<close>
\<comment>\<open>Intuitively, we need some notion of ``x does action", which we can write as ``x is the subject of the sentence 'does action'"\<close>

type_synonym os = "(s \<Rightarrow> t)"
\<comment>\<open>An open sentence is a generalized version of Kroy's substitution operator @{cite kroy} 196\<close>
\<comment>\<open>``does action" is an open sentence that can be instantiated with a subject\<close>
\<comment>\<open>``P sub (d/e)" can be written as ``S(e)", where S(d) = P\<close>
\<comment>\<open>So the terms that we substitute into are actually instantiations of an open sentence, and substitution just requires re-instantiating the open sentence with a different subject\<close>

subsubsection Abbreviations

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

subsection "Differences Between Kroy's Logic (Kr) and DDL"

text "@{cite kroy} uses a different logic than DDL. Let's see if the semantics that Kr requires hold in DDL"

lemma permissible_semantic_faithful:
  fixes A w
  shows "P {A} w \<longrightarrow> (\<exists>x. A(x))"
  nitpick[user_axioms] oops
\<comment>\<open>The most faithful interpretation of Kr is that if A is permissible in a context, then 
it must be true at some world in that context. Kr operates under the ``deontic alternatives" view, 
summarized by Solt as ``A proposition of the sort OA is true at the actual world w if and
only if A is true at every deontic alternative world to t." Under this view, permissible propositions
are obligated at some deontic alternative, but not at all of them.

DDL does not adopt a deontic alternatives view, which is why this proposition seems wildly counterintuitive
in DDL. In DDL, the ob operator abstracts away the notion of deontic alternatives and completely determines
obligations. Even if one belives that permissible statements should be true at some deontic alternative, 
it's not clear that permissible statements must be realized at some world, hence the failure of this 
lemma in DDL.\<close>
\<comment>\<open>Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)\<close>

lemma permissible_semantic_faithful_2:
  fixes A w
  shows "P {A} w \<longrightarrow> (\<exists>x. O {A} x)"
  nitpick[user_axioms] oops
\<comment>\<open>Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)\<close>
\<comment>\<open>This is the most clear lemma that we would expect to hold under the deontic alternatives view. The 
fact that it doesn't shows DDL is not a logic of deontic alternatives. There are pros and cons to this
approach. The deontic alternatives view is quite simple to visualize and offers clear intuition. On
the other hand, DDL's ob function can encode more complex relations than the deontic alternatives view,
and can encode these in a more intuitive manner. The notion of a ``deontically perfect alternative"
is a squishy one, and an ob function more directly captures the idea of obligation.\<close>


lemma permissible_semantic_vacuous:
  fixes A w
  shows "P {A} w \<longrightarrow> (\<exists>x. ob(x)(A))"
  nitpick[user_axioms] oops
\<comment>\<open>Kr does not allow vasuously permissible statements -> if something is permissible it has to be obligated 
at some deontically perfect alternative. In DDL, this can be roughly translated as, if A is permissible, 
it is obligated in some context.\<close>
\<comment>\<open>Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)\<close>
\<comment>\<open>In order to make this true, we'd have to require that everything is either obligatory or 
prohibited somewhere. But as found in the buggy version of DDL, that breaks everything and destroys the 
notion of permissibility everywhere. I am going to allow for vacuous permissibility. If something breaks later
in Kr, it may be because of this.\<close>

lemma permissible_ob:
  fixes A w
  shows "O {A} w \<longrightarrow> P {A} w"
  nitpick [user_axioms] oops
\<comment>\<open>Nitpick found a counterexample for card i = 2:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)\<close>
\<comment>\<open>This one is definitely problematic. Being permissible should be a precondition for being obligatory.
In my eventual logic, I will need to add this as an axiom, because I can't see any ethical theory succeeding without this.\<close>

subsection "The Categorical Imperative"

abbreviation FUL::"bool" where "FUL \<equiv> \<forall>w A. ((\<exists>p. (\<^emph>P {A}p )w) \<longrightarrow> (\<forall>x. (\<^emph>P {A}x)w))"
\<comment>\<open>This is Kroy's formalization of the FUL in DDL. Recall that the FUL says
``act only in accordance with that maxim through which you can at the same time will that it become a universal law" @{cite groundwork}
Kroy interprets this to mean that if an action A is permissible for some agent p, then it must be permissible for everyone.
This formalizes the important moral intuition that the formula of universal law prohibits free-riding. No one is a moral exception\<close>

lemma FUL:
  shows FUL
  nitpick[user_axioms] oops
\<comment>\<open>Nitpick found a counterexample for card s = 2 and card i = 2:

  Skolem constants:
    A = ($\lambda x. \_$)($s_1$ := ($\lambda x. \_$)($i_1$ := True, $i_2$ := True), $s_2$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := False))
    p = $s_1$
    x = $s_2$
This formalization doesn't hold in DDL. Good - this means that adding it as an axiom will change the logic.\<close>

lemma "\<Turnstile> (\<^bold>\<not> (O {\<^bold>\<not> \<^bold>\<top>}))"
  by (simp add: ax_5a) 

lemma complete:
  shows "(\<Turnstile> (((A \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<top>)))) \<longrightarrow> (\<Turnstile> (\<^bold>\<not> (O {A})))"
proof - 
  have "(\<exists>x. (\<^bold>\<not> (\<diamond> A)) x) \<longrightarrow> (\<exists>x. (\<^bold>\<not> O {A}) x)"
    by (simp add: ax_5a ax_5b)
  thus ?thesis
    by blast
qed

axiomatization where CI: CI and 
possible: "(\<forall>w. \<not> \<diamond>A w) \<longrightarrow> \<Turnstile>(O {\<^bold>\<not> A})"
\<comment>\<open>We really need a way to add negative obligations - to related the concept of contradiction and 
obligation. This seems reasonable - if A is never possible at any world, then it's prohibited.\<close>
and hmm: "\<Turnstile> (\<^bold>\<not> (O {\<^bold>\<not> \<^bold>\<top>}))"

subsection "Tests"

lemma True nitpick [satisfy,user_axioms] oops 
\<comment>\<open>Nitpick found a model for card s = 1 and card i = 1:

  Empty assignment\<close>
\<comment>\<open>The categorical imperative is consistent!\<close>

  subsubsection "Specifying the Model"


lemma breaking_promises:
  fixes me::s
  fixes lie::os
  assumes "\<exists>x. (\<^bold>\<not> (\<diamond>(lie(x))) cw)"
  shows "\<exists>x. (\<^bold>\<not> (O {lie(x)})) cw"
  by (metis assms ax_5a ax_5b)


lemma breaking_promises:
  fixes me::s
  fixes lie::os
  assumes "\<exists>x. (\<^bold>\<not> (\<diamond>(lie(x))) cw)"
  shows "\<exists>x. (\<^bold>\<not> (P {lie(x)})) cw"
  nitpick[user_axioms] oops



  subsubsection "Metaethical Tests"

  subsubsection "Kroy's Tests"





end