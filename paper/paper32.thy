(*<*) theory paper32
  imports  paper22 paper224

begin
(*>*)


subsection \<open>Kroy's Formalization of the Categorical Imperative \label{sec:kroy}\<close>

text \<open>This section contains a formalization of the categorical imperative introduced by Moshe Kroy in 
1976 @{cite kroy}. Kroy used Hinktikka's deontic logic to formalize the Formula of Universal Law and
the Formula of Humanity. I will first import the additional logical tools that Hintikka's logic contains 
that Kroy relies on, then examine the differences between his logic and DDL, and finally implement 
and test both of Kroy's formalizations.\<close>

subsubsection "Additional Logical Tools"

text \<open>Kroy's logic relies heavily on some notion of identity or agency. We need some notion of ``x does action", 
which we can write as ``x is the subject of the sentence `does action'". This requires defining a subject.\<close>

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

text \<open>\textbf{Obligatory statements should be permissible}\<close>

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

  text \<open>This particular difference seems untenable. My custom formalization of the categorical imperative 
must add this as an axiom.\<close>

(*<*)text\<open>axiomatization where permissible_prepreq_ob: "\<Turnstile> (O {A} \<rightarrow> P {A})"\<close> (*>*)


subsubsection "The Categorical Imperative"

text \<open>I will now implement Kroy's formalization of the Formula of Universal Law. Recall that the FUL says
``act only in accordance with that maxim which you can at the same time will a universal law" @{cite groundwork}.
Kroy interprets this to mean that if an action is permissible for a specific agent, then it must be permissible for everyone.
This formalizes an important moral intuition: the categorical imperative prohibits free-riding. No one is a moral exception.
Formalizing this interpretation requires using open sentences to handle the notion of substitution.\<close>
abbreviation FUL::"bool" where "FUL \<equiv> \<forall>w A. ((\<exists>p::s. ((P {A p}) w))  \<longrightarrow>( (\<forall>p.( P {A p}) w))) "
text "P {A p} vs *P{A} p"

\<comment>\<open>In English, this statement roughly means that, for any person $p$ if action $A$ is 
permissible for $p$, then action $A$ must be permissible for all agents $x$. The notion of ``permissible for" 
is captured by the substitution of $x$ for $p$.\<close>

text \<open>Let's check if this is already an axiom of DDL. If so, then the formalization is trivial.\<close>

lemma FUL:
  shows FUL
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card s = 2 and card i = 2:

  Skolem constants:
    A = ($\lambda x. \_$)($s_1$ := ($\lambda x. \_$)($i_1$ := True, $i_2$ := True), $s_2$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := False))
    p = $s_1$
    x = $s_2$\color{black}\<close>

  text "This formalization doesn't hold in DDL, so adding it as an axiom will change the logic."

axiomatization where FUL: FUL

text "Consistency check: is the logic still consistent with the FUL added as an axiom?"

lemma True nitpick[user_axioms, satisfy, card=1] oops
\<comment>\<open>\color{blue} Nitpicking formula... 
Nitpick found a model for card i = 1:

  Empty assignment\color{black}\<close>

  text "This completes my implementation of Kroy's formalization of the first formulation of the 
categorical imperative. I defined new logical constructs to handle Kroy's logic, studied the differences
between DDL and Kr, implemented Kroy's formalization of the Formula of Universal Law, and showed 
that it is both non-trivial and consistent. Now it's time to start testing!"



  subsubsection "Application Tests"

  text "Recall that in Section 3.1.1, we tested the naive interpretation's ability to show that murder 
is wrong. We started by showing that if murder is possibly wrong, then it is wrong. Let's test that 
here."

consts M::"t"
\<comment>\<open>Let the constant $M$ denote murder.\<close>

lemma wrong_if_possibly_wrong:
  shows "((\<diamond> (O {\<^bold>\<not> M})) cw) \<longrightarrow>  (\<forall>w. (O {\<^bold>\<not> M}) w)"
  by simp

text \<open>This is the same result we got in Section 3.1.1—if murder is wrong at some world, it is wrong at
every world. Kroy's formulation shouldn't actually mean that this property holds. Kroy interprets the 
FUL as universalizing across $people$, not worlds. In other words, Kroy's formulation implies that if
murder is wrong for someone, then it is wrong for everyone. This strange result is actually a property 
of DDL itself, not a property of Kroy's formalization. Indeed, repeating this experiment in DDL, with no
additional axioms that represent the categorical imperative shows that, in DDL, if something is 
possible wrong, it is wrong at every world. So this is not a useful example to test any formulation,
since it holds in the base logic itself.\<close>

text "Let's try adapting our murder wrong axiom to Kroy's formulation. In particular, let's see if 
murder being wrong for one person means that it's wrong for everyone."

consts M2::"os"
\<comment>\<open>Let's define murder as an open sentence this time, so that we can substitute in different people.\<close>

lemma wrong_if_wrong_for_someone:
  shows "(\<exists>p. \<Turnstile> O {\<^bold>\<not>(M2 p)}) \<longrightarrow> (\<forall>p. \<Turnstile> O {\<^bold>\<not>(M2 p)})"
  proof 
    assume "(\<exists>p. \<Turnstile> O {\<^bold>\<not>(M2 p)})"
    show "(\<forall>p. \<Turnstile> O {\<^bold>\<not>(M2 p)})"
      using FUL \<open>\<exists>p. \<Turnstile>\<^emph>O{\<^emph>\<not>M2} p\<close> by blast
  qed
\<comment>\<open>This lemma gets to the heart of Kroy's formulation of the categorical imperative. If murder is prohobited
for a specific person $p$, then it must be prohibited for all people. This test case also revealed a 
bug in my original implementation of Kroy's formulation of the FUL, demonstrating the power of such 
philosophical tests for automated ethics. Just as engineers use TDD to find bugs in their code, philosophers
and ethicists can use this approach to find bugs in the precise formulations of their theories.\<close>

  text "For the naive implementation, we also tested the slightly stronger proposition that if not 
everyone can simultaneously lie, then lying is prohibited. We want to show that if lying 
fails the universalizability test, then the FUL prohibits it."

consts lie::os 
abbreviation lying_not_universal::bool where "lying_not_universal \<equiv> \<forall>w. \<not> (\<forall>p. lie(p) w)"
\<comment>\<open>The formula above reads, ``At all worlds, it is not the case that everyone lies."\<close>

lemma lying_prohibited:
  fixes p
  shows " lying_not_universal \<longrightarrow> \<Turnstile> (O {\<^bold>\<not> (lie(p))})"
  nitpick[user_axioms] oops
\<comment>\<open>$\color{blue}$Nitpick found a counterexample for card i = 1 and card s = 1:

  Free variable:
    p = $s_1$
  Skolem constant:
    $\lambda$w. p = ($\lambda$x. $\_$)($i_1$ := $s_1$) $\color{black}$\<close>

  text "Kroy's formulation also fails to show that if not everyone can lie, then lying is prohibited. 
      There may be an issue here with our representation of lying not being universal. Specifically, 
      the FUL is violated if it's not $possible$ for everyone to simultaneously lie, but the abbreviation 
      above merely represents that fact that not everyone does, in fact, simultaneously lie. It's entirely
      possible that everyone can simultaneously lie, but for some reason, maybe out of some moral sense, 
      do not. Let's test a more accurate version of the failure of the universalizability test."

  text\<open> We want to represent the sentence, call it $S$ $\longleftrightarrow$ ``At all worlds, it is 
      not possible that everyone lies simultaneously." Consider the two abbreviations below. \<close>

abbreviation everyone_lies::t where "everyone_lies \<equiv> \<lambda>w. (\<forall>p. (lie(p) w))"
\<comment>\<open>This represents the term ``all people lie". Naively, we might think to represent this as $\forall p. lie(p)$.
In HOL, the $\forall$ operator has type $('a\rightarrow bool) \rightarrow bool$, where $'a$ is a polymorphic
type representing the type of the argument to $\forall$. This is because the universal quantifier binds 
the argument of the term given to it, such that it turns an open term into a closed term. In the given example, 
$\forall$ has the type $(s \rightarrow bool) \rightarrow bool$, so it can only be applied to a formula 
of type $s \rightarrow bool$. In the abbreviation above, we're applying the quantifier to the sentence 
$lie(p) w$ for any arbitrary $w$, so the types cohere.\<close>
\<comment>\<open>The term above is true for a set of worlds $i$ (recall that a term is true at a set of worlds) 
such that, at all the worlds $w$ in $i$, all people at $w$ lie.\<close>

abbreviation lying_not_possibly_universal::bool where "lying_not_possibly_universal \<equiv> \<forall>w. \<not>(\<diamond>everyone_lies w)"
\<comment>\<open>Armed with @{abbrev everyone_lies}, it's easy to represent the sentence $S$. The abbreviation above 
reads, ``At all worlds, it is not possible that everyone lies."\<close>

lemma lying_prohibited_2:
  shows "lying_not_possible_universal \<longrightarrow>  \<Turnstile> (O {\<^bold>\<not> (lie(p))})"
  nitpick[user_axioms] oops
\<comment>\<open>$\color{blue}$Nitpick found a counterexample for card i = 1 and card s = 2:

  Free variables:
    $lying\_not\_possible\_universal$ = True
    p = $s_1$ $\color{black}$\<close>

  text "Even with the stronger assumption that it's not possible for everyone to lie 
simultaneously, Kroy's formulation is still not able to show that lying is prohibited for an arbitrary
person. That's a problem! WHY IS THIS HAPPENING"

  subsubsection "Metaethical Tests"

  lemma permissible:
    shows "\<exists>A. ((\<^bold>\<not> (O {A})) \<^bold>\<and> (\<^bold>\<not> (O {\<^bold>\<not> A}))) w"
    nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue}Nitpick found a model for card i = 1 and card s = 1:

  Skolem constant:
    A =($\lambda x. \_$)($i_1$ := False) \color{black}\<close>
\<comment>\<open>Just as with the naive interpretation, permissibility is possible.\<close>

lemma fixed_formula_is_permissible:
  fixes A
  shows "((\<^bold>\<not> (O {A})) \<^bold>\<and> (\<^bold>\<not> (O {\<^bold>\<not> A}))) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue}Nitpick found a model for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)\color{black}\<close>
\<comment>\<open>This bad result also holds under Kroy's formulation. Recall that we want this to fail - if A is ``murder" 
then no model should render it permissible.\<close>

lemma arbitrary_obligations:
  fixes A::"t"
  shows "O {A} w"
  nitpick [user_axioms=true] oops

    text "ought implies can"



  text "arbitrary obligations"

  text "conflicting obligations"

  text "obligation and permissible relationship"

  subsection "Misc"

  text "stuff from Kroy's paper"
(*<*)
end
(*>*)