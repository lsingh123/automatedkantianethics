(*<*) theory paper32
  imports paper31 paper22 paper224

begin
(*>*)


subsection "Kroy's Formalization of the Categorical Imperative"

text \<open>This section contains a formalization of the categorical imperative introduced by Moshe Kroy in 
1976 @{cite kroy}. Kroy used Hinktikka's deontic logic to formalize the Formula of Universal Law and
the Formula of Humanity. I will first import the additional logical tools that Hintikka's logic contains 
that Kroy relies on, then examine the differences between his logic and DDL, and finally implement 
and test both of Kroy's formalizations.\<close>

subsubsection "Additional Logical Tools"

text \<open>Kroy's logic relies heavily on some notion of identity or agency. We need some notion of ``x does action", 
which we can write as ``x is the subject of the sentence 'does action'". This requires defining a subject.\<close>

typedecl s \<comment>\<open>s is the type for a ``subject", like the subject of a sentence\<close>

text \<open>Kroy also defines a substitution operator\footnote{See page 196 in Kroy's original paper @{cite kroy}.}. $P (d/e)$ is read in his logic as ``P with e substituted 
for d." DDL has no such notion of substitution, so I will define a more generalized notion of an ``open 
sentence." An open sentence takes as input a subject and returns a complete or ``closed" DDL formula. For example, 
``does action" is an open sentence that can be instantiated with a subject. \<close>

type_synonym os = "(s \<Rightarrow> t)"
\<comment>\<open>``P sub (d/e)" can be written as ``S(e)", where S(d) = P\<close>
\<comment>\<open>The terms that we substitute into are actually instantiations of an open sentence, and substitution 
just requires re-instantiating the open sentence with a different subject.\<close>

text \<open>\textbf{New Operators}

Because Isabelle is strongly typed, we need to define new operators to handle open sentences. These operators 
are similar to DDL's original operators. We could probably do without these abbreviations, but they will 
simplify the notation and make it look more similar to Kroy's original paper. \<close>

abbreviation os_neg::"os \<Rightarrow> os" ("\<^emph>\<not>_")
  where "(\<^emph>\<not>A) \<equiv> \<lambda>x. \<^bold>\<not>(A(x))"
abbreviation os_and::"os \<Rightarrow> os \<Rightarrow> os" ("_\<^emph>\<and>_")
  where "(A \<^emph>\<and> B) \<equiv> \<lambda>x. ((A(x)) \<^bold>\<and> (B(x)))"
abbreviation os_or::"os \<Rightarrow> os \<Rightarrow> os" ("_\<^emph>\<or>_")
  where "(A \<^emph>\<or> B) \<equiv> \<lambda>x. ((A(x)) \<^bold>\<or> (B(x)))"
abbreviation os_ob::"os \<Rightarrow> os" ("\<^emph>O{_}")
  where "\<^emph>O{A} \<equiv> \<lambda>x. (O {A(x)})"

text \<open>Once again, the notion of permissibility will be useful here.\<close>

abbreviation ddl_permissible::"t\<Rightarrow>t" ("P {_}")
  where "P {A} \<equiv> \<^bold>\<not> (O {\<^bold>\<not> A})"
abbreviation os_permissible::"os\<Rightarrow>os" ("\<^emph>P {_}")
  where "\<^emph>P {A} \<equiv> \<lambda>x. P {A(x)}"


subsubsection "Differences Between Kroy's Logic (Kr) and DDL"


text \<open>One complication that arises here is that Kroy's original paper uses a different logic than DDL. 
His custom logic is a slight modification of Hintikka's deontic logic @{cite hintikka}. In this section, 
I will determine if some of the semantic properties that Kroy's logic (which I will now call Kr) requires 
hold in DDL. These differences may become important later and can explain differences in my results and 
Kroy's.\<close>

text \<open>\textbf{Deontic alternatives versus the neighborhood semantics}\<close>

text \<open>The most faithful interpretation of Kr is that if $A$ is permissible in a context, then 
it must be true at some world in that context. Kr operates under the ``deontic alternatives" or Kripke semantics, 
summarized by Solt @{cite solt} as follows: ``A proposition of the sort $O A$ is true at the actual world $w$ if and
only if $A$ is true at every deontic alternative world to $w$." Under this view, permissible propositions
are obligated at some deontic alternatives, or other worlds in the system, but not at all of them. Let's 
see if this holds in DDL.\<close>

lemma permissible_semantics:
  fixes A w
  shows "(P {A}) w \<longrightarrow> (\<exists>x. A(x))"
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False) \color{black}\<close>

text \<open>Remember that DDL uses neighborhood semantics, not the deontic alternatives view, which is why this
 proposition fails in DDL. In DDL, the $ob$ function abstracts away the notion of
 deontic alternatives and completely determines obligations. Even if one belives that permissible 
statements should be true at some deontic alternative, it's not clear that permissible statements
 must be realized at some world. In some ways, this also coheres with our understanding of obligation. There 
are permissible actions like ``Lavanya buys a red folder" that might not happen in any universe.

An even stricter version of the semantics that Kr requires is that if something is permissible at a world, 
then it is obligatory at some world. This is a straightforward application of the Kripke semantics. Let's
test this proposition.\<close>

lemma permissible_semantics_2:
  fixes A w
  shows "P {A} w \<longrightarrow> (\<exists>x. O {A} x)"
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False) \color{black}\<close>


  text \<open>This also doesn't hold in DDL because DDL uses neighborhood semantics instead of the deontic 
alternatives or Kripke semantics. This also seems to cohere with our moral intuitions. The statement 
``Lavanya buys a red folder" is permissible in the current world, but it's hard to see why it would 
be oblgiatory in any world.

One implication of the Kripke semantics is that Kr disallows ``vacuously permissible statements." In 
other words, if something is permissible it has to be obligated at some deontically perfect alternative. 
If we translate this to the language of DDL, we expect that if $A$ is permissible, it is obligated in some 
context.\<close>


lemma permissible_semantic_vacuous:
  fixes A w
  shows "P {A} w \<longrightarrow> (\<exists>x. ob(x)(A))"
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False) \color{black}\<close>

text \<open>In order to make this true, we'd have to require that everything is either obligatory or
prohibited somewhere. Sadly, that breaks everything and destroys the 
notion of permissibility everywhere \footnote{See Appendix for an examination of a buggy version of DDL that led to this insight.}. 
If something breaks later in this section, it may be because of vacuous permissibility.\<close>

text \<open>\textbf{Obligatory Statements Should be Permissible}\<close>

text \<open>Kr includes the intuitively appealing theorem that if a statement is obligated at a world, then it 
is permissible at that world\footnote{This follows straightforwardly from the Kripke semantics. If proposition $A$ is 
obligated at world $w$, this means that at all of $w$'s neighbors, $O A$ holds. Therefore, 
$\exists w'$ such that $w$ sees $w'$ and $O A$ holds at $w'$ so $A$ is permissible at $w$.}. Let's see 
if that also holds in DDL.\<close>

lemma permissible_prereq_ob:
  fixes A w
  shows "O {A} w \<longrightarrow> P {A} w"
  nitpick [user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 2:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)\color{black}\<close>

  text \<open>This particular difference seems untenable. Most ethical theories require that if something is 
obligatory, it must also be permissible. This is an important enough property of an ethical theory that I 
will add it as an axiom.\<close>

axiomatization where permissible_prepreq_ob: "\<Turnstile> (O {A} \<^bold>\<rightarrow> P {A})"

(*<*)

subsection "The Categorical Imperative"

abbreviation CI::"bool" where "CI \<equiv> \<forall>w A. ((\<exists>p. (\<^emph>P {A}p )w) \<longrightarrow> (\<forall>x. (\<^emph>P {A}x)w))"
\<comment>\<open>This is Kroy's formalization of the FUL in DDL. Recall that the FUL says
``act only in accordance with that maxim through which you can at the same time will that it become a universal law" @{cite groundwork}
Kroy interprets this to mean that if an action is permissible for me, then it must be permissible for everyone.
This formalizes an important moral intuition - the CI prohibits free-riding. No one is a moral exception\<close>

lemma CI:
  shows CI
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
(*>*)