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

lemma contradictory_obs:
  fixes A B w
  assumes "\<Turnstile> (A \<^bold>\<and> B)"
  shows "(\<^bold>\<not> (O {A \<^bold>\<and> B})) w"
  nitpick [user_axioms, falsify] oops
\<comment>\<open>Contradictory things can't be obligated in Kr, since a contradiction can't be true at any deontic alternative.
This doesn't hold in DDL, and we already saw this cause problems for the naive formalization. We should 
expect those problems to hold in our implementation of Kr, but this difference suggests that they are 
a symptom of DDL, not of any inherent problem with Kroy's formalization.\<close>

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

  text_raw\<open>\textbf{Murder}\<close>

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

  text_raw\<open>\textbf{Lying}\<close>

  text "For the naive implementation, we also tested the slightly stronger proposition that if not 
everyone can simultaneously lie, then lying is prohibited. We want to show that if lying 
fails the universalizability test, then the FUL prohibits it."

consts lie::os 
(*<*) abbreviation lying_not_universal_1::bool where "lying_not_universal_1 \<equiv> \<forall>w. \<not> (\<forall>p. lie(p) w)"
\<comment>\<open>The formula above reads, ``At all worlds, it is not the case that everyone lies."\<close>

lemma lying_prohibited_1:
  fixes p
  shows " lying_not_universal_1 \<longrightarrow> \<Turnstile> (O {\<^bold>\<not> (lie(p))})"
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
      do not. Let's test a more accurate version of the failure of the universalizability test."(*>*)

  text\<open> We want to represent the sentence, call it $S$ $\longleftrightarrow$ ``At all worlds, it is 
      not possible that everyone lies simultaneously." Consider the two abbreviations below. \<close>

abbreviation everyone_lies::t where "everyone_lies \<equiv> \<lambda>w. (\<forall>p. (lie(p) w))"
\<comment>\<open>This represents the term ``all people lie". Naively, we might think to represent this as $\forall p. lie(p)$.
In HOL, the $\forall$ operator has type $('a\rightarrow bool) \rightarrow bool$, where $'a$ is a polymorphic
type of the term being bound by $\forall$. In the given example, 
$\forall$ has the type $(s \rightarrow bool) \rightarrow bool$, so it can only be applied to a formula 
of type $s \rightarrow bool$. In the abbreviation above, we're applying the quantifier to a sentence 
that takes in a given subject $p$ and returns $lie(p) w$ for any arbitrary $w$, so the types cohere.\<close>
\<comment>\<open>The term above is true for a set of worlds $i$ (recall that a term is true at a set of worlds) 
such that, at all the worlds $w$ in $i$, all people at $w$ lie.\<close>

abbreviation lying_not_possibly_universal::bool where "lying_not_possibly_universal \<equiv> \<Turnstile>(\<^bold>\<not> (\<diamond> everyone_lies))"
\<comment>\<open>Armed with @{abbrev everyone_lies}, it's easy to represent the sentence $S$. The abbreviation above 
reads, ``At all worlds, it is not possible that everyone lies."\<close>

lemma lying_prohibited:
  shows "lying_not_possibly_universal \<longrightarrow>  ( \<Turnstile>(\<^bold>\<not> P {lie(p)}))"
  nitpick[user_axioms] oops
\<comment>\<open>$\color{blue}$Nitpick found a counterexample for card i = 1 and card s = 2:

  Free variables:

    $lying\_not\_possible_universal$ = True

    p = $s_1$ $\color{black}$\<close>

  text "Even with the stronger assumption that it's not possible for everyone to lie 
    simultaneously, Kroy's formulation is still not able to show that lying is prohibited for an arbitrary
    person. That is not good. Let's investigate why this is happening."


  text \<open>Let's outline the syllogism that we $\emph{expect}$ to prove that lying is prohibited.\<close>

  text_raw\<open>\begin{enumerate}
        \item At all worlds, it's not possible for everyone to lie. (This is the assumed lemma lying\_not\_possible\_universal)
        \item At all worlds, there is necessarily someone who doesn't lie. (Modal dual of (1))
        \item If A is permissible for subject p at world w, A is possible for subject p at world w. (Ought Implies Can)
        \item If A is permissible at world w for any person p, it must be possible for everyone to A at w. (FUL and (3)) 
        \item Lying is impermissible. (Follows from (4) and (1)) \end{enumerate}\<close>

text "Armed with this syllogism, we can figure out which step fails."

lemma step2:
  shows "lying_not_possibly_universal \<longrightarrow> \<Turnstile>( (\<box> (\<lambda>w. \<exists>p. (\<^bold>\<not> (lie(p)) w)))) "
  by simp
\<comment>\<open>Step 2 holds!\<close>

lemma step3: 
  fixes A p w
  shows "P {A(p)} w \<longrightarrow> (\<diamond> (A(p)) w)"
  nitpick [user_axioms, falsify] oops
\<comment>\<open>$\color{blue}$Nitpick found a counterexample for card `a = 1, card i = 1, and card s = 1:

  Free variables:
    A = ($\lambda x. \_$)($a_1$ := ($\lambda x. \_$)($i_1$ := False))
    p = $a_1$ $\color{black}$\<close>

  text \<open>As we see above, the syllogism fails at Step 3, explaining why the lemma doesn't 
        hold as expected. Kroy explicitly states (p. 199 footnote 19) that this lemma holds in his logic, which may explain
        his choice of formalization. Taking a step back, it's not clear that Step 3 should hold. After all,
        impossible actions can be permissible (look for citation). Imagine I make a trip to Target to 
        purchase a folder, and they offer blue and black folders. No one could claim that it's impermissible
        for me to purchase a red folder, or, equivalently, that I am obligated to not purchase a red folder.\<close>

  text \<open>(This is actual philosophy - maybe worth fleshing this out?)
        Another core issue here is Kroy's interpretation of the formula of universal law. In @cite{korsgaardFUL}, 
        Korsgaard defends a practical contradiction interpretation of the categorical imperative, whereby 
        a maxim is prohibited if, when universalized, it defeats itself (Korsgaard 3). In other words, if universalizing
        the maxim renders the maxim ineffective at achieving its stated objective, the maxim fails the
        universalizability test. 

        This example shows that Kroy, on the other hand, is operating under a very different, circular view of 
        the formula of universal law. He interprets the FUL as prohibiting A if it is not simultaneously 
        permissible for everyone to A. This is empty—the categorical imperative is supposed to be a complete,
        self-contained (cite the groundwork), absolute rule of morality, but Kroy's version of the FUL prescribes obligations 
        in a self-referencing manner. The FUL is supposed to define what is permissible and what isn't, 
        but Kroy provides a circular definition that defines permissibility in terms of permissibility.
        
        This is not obvious from Kroy's presentation of his formalization of 
        the categorical imperative. This example demonstrates the power of formalized ethics. Making
        an interpretation of the categorical imperative precise demonstrated a philosophical problem 
        with that interpretation.

        Another key takeaway here is that in order for a formalization to be faithful to what Korsgaard
        argues is the most generous interpretation of the formula of universal law, we must have some notion
        of the actions and ends of a maxim. Specifically, we must be able to represent the notion of the 
        actions of a maxim being ``undermined" or impossible.\<close>

  subsubsection "Metaethical Tests"

  text "In addition to testing specific applications of the theory, we're also interested in certain 
        metaethical properties, as in the naive interpretation. First, we want to see if permissiblility
        is possible under this formalization."

lemma permissible:
  fixes A w
  shows "((\<^bold>\<not> (O {A})) \<^bold>\<and> (\<^bold>\<not> (O {\<^bold>\<not> A}))) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue}Nitpick found a model for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)\color{black}\<close>

  text \<open>The above result shows that, for some action A and world w, we can find a model where A 
        is permissible at w. That's exactly the result we want. If we were to further specify properties
        of A (such as `A is murder' or `A is prohibited') we would want this result to fail.\<close>

  text "Next, we want to see if the formalization allows arbitrary obligations."

lemma arbitrary_obligations:
  fixes A::"t"
  shows "O {A} w"
  nitpick [user_axioms=true, falsify] oops
\<comment>\<open>Nitpick found a counterexample for card i = 1 and card s = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)\<close>

  text \<open>This is exactly the expected result. Any arbitrary action A isn't obligated. A slightly 
        stronger property is ``modal collapse," or whether or not A happens implies A is obligated.\<close>

lemma modal_collapse:
  fixes A w
  shows "A w \<longrightarrow> O {A} w"
  nitpick [user_axioms=true, falsify] oops
\<comment>\<open>Nitpick found a counterexample for card i = 1 and card s = 1:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := True)
    w = $i_1$\<close>

  text "This test also passes. Next, let's try whether or not ought implies can holds. Recall that I 
        showed in section 3.1.2 that ought implies can is a theorem of DDL itself, so it should still hold."

lemma ought_implies_can:
  fixes A w
  shows "O {A} w \<longrightarrow> \<diamond> A w"
  using O_diamond by blast

text "This theorem holds. Now that we have a substitution operation, we also expect that if an action 
      is obligated for a person then it is possible for that person. That should also follow by the 
      axiom of substitution @{cite cresswell}, or if we just replace the `A' in the formula above with 
      `A(p)'"

lemma ought_implies_can_person:
  fixes A w 
  shows "O { A(p)} w \<longrightarrow> \<diamond> (A (p)) w"
  using O_diamond by blast

text "This test also passes. Next, let's explore whether or not Kroy's formalization still allows 
      conflicting obligations."

lemma conflicting_obligations:
  fixes A w
  shows "(O {A} \<^bold>\<and> O {\<^bold>\<not> A}) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>$\color{blue}$Nitpick found a model for card i = 2 and card s = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)$\color{black}$\<close>

  text "Just as with the naive formalization, Kroy's formalization allows for contradictory obligations. 
        Recall earlier that we showed this is a property of DDL itself. This is a good goal to have for 
        my custom formalization. I will also test the stronger property that if two maxims imply a 
        contradiction, they may not be simultaneously willed."

lemma implied_contradiction:
  fixes A B w
  assumes "(A \<^bold>\<rightarrow> (\<^bold>\<not> B))w"
  shows "\<^bold>\<not> (O {A} \<^bold>\<and> O {B}) w"
  nitpick [user_axioms, falsify] oops
\<comment>\<open>$\color{blue}$Nitpick found a counterexample for card i = 2 and card s = 1:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := True, $i_2$  := False)
    B = ($\lambda x. \_$)($i_1$  := True, $i_2$  := False)
    w = $i_2$ $\color{black}$\<close>

  text "Just as with the naive formalization, Kroy's formalization allows implied contradictions because 
        DDL itself allows implied contradictions and, as we explored in Section (applied tests), Kroy's 
        formalization doesn't do anything to remedy this. IS THIS ACTUALLY HOW WE REPRESENT A CONTRADICTION"

lemma ob_perm:
  fixes A w
  shows "(O {A} \<^bold>\<or> (P {A} \<^bold>\<or> O {\<^bold>\<not> A})) w"
  by simp
\<comment>\<open>This is exactly what we expect - an action should be either obligatory, permissible, or prohibited.\<close>

text "(This should be more developed and go at the beginning of this section as a thesis). The combination of these tests shows 
      that while Kroy's formalization is more powerful and more coherent than the naive formalization, it 
      still fails to capture most of the desired properties of the categorical imperative. Some of these 
      problems might be remedied by the fact that Kroy's logic doesn't allow contradictory obligations, 
      and that possibility will be interesting to explore in my own formalization."

subsection "Miscellaneous Test"

text "In this section, I explore tests of properties that Kroy presents in his original paper. These 
tests will not only test the features of the system that Kroy intended to draw out, but they may also 
inspire additional tests and criteria for my own formalization in Chapter 3."

text "Kroy presents a stronger version of the formula of universal law and argues that his formalization
is implied by the stronger version. Let's test that claim."

abbreviation FUL_strong::bool where "FUL_strong \<equiv>  \<forall>w A. ((\<exists>p::s. ((P {A p}) w))  \<longrightarrow>( (( P { \<lambda>x. \<forall>p. A p x}) w)))"

lemma strong_implies_weak:
  shows "FUL_Strong \<longrightarrow> FUL"
  using FUL by blast

text "Kroy's stated stronger version of the FUL is indeed stronger than his original version."

text \<open>The difference between the stronger version and @{abbrev FUL} is subtle. The antecedent of FUL is ``for all people p,
it is permissible that they p." The antecedent of this stronger statement is ``it is permissible that 
everyone p's." In particular, this stronger statement requires that it is permissible for everyone to
 p simultaneously. Kroy immediately rejects this version of the categorical imperative, arguing that 
it's impossible for everyone to be the US president simultaneously, so this version of the FUL prohibits
running for president.

Most Kantians would disagree with this interpretation. Consider the classical example of lying, as presented 
in @{cite kemp} and in @{cite "KorsgaardFUL"}. Lying fails the universalizability test because in a 
world where everyone lied simultaneously, the practice of lying would break down. If we adopt Kroy's 
version, lying is only prohibited if, no matter who lies, lying is impermissible. As argued above, this 
rule circularly relies on some existing prohibition against lying for a particular person, and thus 
fails to show the wrongness of lying. It is tempting to claim that this issue explains why the tests 
above on the wrongness of lying failed. To test this hypothesis, I will check if the stronger version 
of the FUL implies that lying is impermissible. (TODO make this and the written philosophy above coherent)\<close>

lemma strongFUL_implies_lying_is_wrong:
  fixes p
  shows "FUL_strong \<longrightarrow> \<Turnstile>(\<^bold>\<not> P {lie(p)})"
  nitpick[user_axioms, falsify] oops
\<comment>\<open>$\color{blue}$
Nitpick found a counterexample for card i = 1 and card s = 1:

  Free variable:
    p = $s_1$
$\color{black}$\<close>

  text "The test above also fails! This means that not even the stronger version of Kroy's formalization
        of the FUL can show the wrongness of lying. There are two independent errors. The first is the 
        cirularity of the formalization and the second is the assumption that impossible actions are 
        impermissible. The stronger FUL addresses the first error, but the second remains."

  text "Kroy also argues that the FUL gives us recipes for deriving obligations, in addition to deriving
        permissibile actions. Specifically, he presents two principles parallel to FUL and strong FUL, 
        which in his logic are equivalent."

abbreviation obligation_universal_weak::bool where "obligation_universal_weak \<equiv> \<forall>w A. ((\<exists>p::s. ((O {A p}) w))  \<longrightarrow>( (\<forall>p. ( O {A p }) w)))"
abbreviation obligation_universal_strong::bool where "obligation_universal_strong \<equiv> \<forall>w A. ((\<exists>p::s. ((O {A p}) w))  \<longrightarrow>( (( O { \<lambda>x. \<forall>p. A p x}) w)))"
lemma weak_equiv_strong:
  shows "obligation_universal_weak \<equiv> obligation_universal_strong"
  oops
\<comment>\<open>Isabelle is neither able to find a proof nor a countermodel for the statement above, so I can't say 
  if it holds or not without completing a full, manual proof. This entire aside is not super relevant to 
  my project, so I will defer such a proof until later.\<close>

  text \<open>These two statements are not necessarily equivalent in my logic, but are in Kroy's$\footnote{This follows from
        the fact that the Barcan formula holds in Kroy's logic but not in mine, as verified with Nitpick. See 
        Appendix for more.}$ This difference in logics may further explain why tests are not behaving as 
        they should. Nonetheless, Kroy argues that the FUL implies both statements above. Let's test that.\<close>

lemma FUL_implies_ob_weak:
  shows "FUL \<longrightarrow> obligation_universal_weak" oops
\<comment>\<open>Isabelle is neither able to find a proof nor a countermodel for this statement.\<close>

lemma FUL_implies_ob_strong:
  shows "FUL \<longrightarrow> obligation_universal_strong" oops
\<comment>\<open>Isabelle is neither able to find a proof nor a countermodel for this statement.\<close>

  text "Isabelle timed out when looking for proofs or countermodels to the statements above. This may be 
        an indication of a problem that Benzmueller warned me about—mixing quantifiers into a shallow
        embedding of DDL may be too expensive for Isabelle to handle. Not sure what to do about this. "

(*<*)
text "put this in the appendix"
lemma barcan:
  shows "(\<forall>w p. O { A(p) } w) \<equiv> (O {\<lambda>x. \<forall>p. A(p) x} w)"
  nitpick[user_axioms, falsify] oops
\<comment>\<open>$\color{blue} $Nitpick found a counterexample for card 'a = 2, card i = 2, and card s = 1:

  Free variable:
    A = ($\lambda x. \_$)($a_1$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := True), $a_2$ := ($\lambda x. \_$)($i_1$ := True, $i_2$ := False)) $\color{black}$\<close>
(*>*)

  text "Kroy argues that the two statements above are equivalent, but this fails in our logic. "
  text "stuff from Kroy's paper"
(*<*)
lemma hmmm:
  shows "lying_not_possibly_universal \<longrightarrow> (\<forall>w. \<exists>p. (( \<^bold>\<not> (lie(p)))w)) "
  by simp

lemma hmmm2:
  shows "lying_not_possibly_universal \<longrightarrow> \<Turnstile>( \<^bold>\<not> (\<diamond> (\<lambda>w. \<forall>p. (lie(p) w)))) "
  by blast

lemma hellno:
  shows "lying_not_possibly_universal \<longrightarrow> \<Turnstile>(\<box>(\<^bold>\<not>(everyone_lies)))"
  by auto

lemma dammit:
  shows "lying_not_possibly_universal \<longrightarrow> \<Turnstile>(\<box>(\<lambda>w. (\<exists>p. (\<^bold>\<not> (lie(p)) w))))"
  by simp

lemma hm:
  shows "(\<exists>p. \<Turnstile> P {lie(p)}) \<longrightarrow> (\<forall>p. (\<Turnstile> P {lie(p)}))"
  using FUL by blast

lemma wtf:
  shows "(\<Turnstile> (P {lie(p)})) \<longrightarrow> \<Turnstile>(\<diamond> (lie(p)))"
  nitpick[user_axioms] oops
end
(*>*)