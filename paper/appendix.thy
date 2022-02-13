(*<*) theory appendix imports paper224

begin (*>*)

section "Appendix"

subsection \<open>Maxims and Motives \label{maximmotive}\<close>

text \<open>

Kitcher begins with O'Niell's circumstance, act, goal view and expands it to include the motive 
behind performing the maxim @{cite whatisamaxim}. This additional component is read 
as ``In circumstance C, I will do A in order to G because of M," where M may be ``duty" or ``self-love."
Kitcher argues that the inclusion of motive is necessary for the fullest, most general form of a maxim
in order to capture Kant's idea that an action derives its moral worth from being done for the sake of duty itself.
Under this view, the FUL would obligate maxims of the form 
``In circumstance C, I will do A in order to G because I can will that I and everyone else simultaneously
will do A in order to G in circumstance C." In other words, if Kant is correct in arguing that moral 
actions must be done from the motive of duty, the affirmative result of the FUL becomes 
the motive for a moral action.

While Kitcher's conception of a maxim captures Kant's idea of acting for duty's own sake, I will not implement it 
because it is not necessary for putting maxims through the FUL. Indeed, Kitcher acknowledges that 
O'Neill's formulation suffices for the universalizability test, but is not the general notion of a maxim.
In order to pass the maxim through the FUL, it suffices to know the circumstance, act, and goal. The FUL
derives the motive that Kitcher bundles into the maxim, so automating the FUL does not require 
including a motive. The ``input" to the FUL is the circumstance, act, goal tuple. My project takes 
this input and returns the motivation that the dutiful, moral agent would adopt. Additionally, doing
justice to the rich notion of motive requires modelling the operation of practical reason itself, 
which is outside the scope of this project. My work focuses on the universalizability test, but future work that 
models the process of practical reason may use my implementation of the FUL as a ``library." Combined 
with a logic of practical reason, an implementation of the FUL can move from evaluating a maxim to 
evaluating an agent's behavior, since that's when ``acting from duty" starts to matter.\<close>

(*<*)
subsection "Conjunctions in DDL"

\<comment> \<open>Assume that O\{A \wedge B\} \iff O\{A\} \wedge O\{B\}. This implies the following theorem:\<close>

lemma contradictory_obligations:
  assumes "\<Turnstile>(O {(A \<^bold>\<and> B)} \<^bold>\<equiv> (O {A} \<^bold>\<and> O {B}))"
  shows "\<Turnstile>(\<^bold>\<not> ((O {A}) \<^bold>\<and> (O {\<^bold>\<not> A})))"
  nitpick[user_axioms]
  oops
\<comment> \<open>What is the cause of the above strangeness?\<close>
\<comment> \<open>This very intuitive theorem holds in my logic but not in BFP's\<close>
\<comment> \<open>It's clear that this theorem results in the strange results above.\<close>
\<comment> \<open>Conclusion: There is a bug in my embedding\<close>
\<comment>\<open>Nitpick found a counterexample for card i = 2:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)\<close>


text "Sidebar: the above theorem is really intuitive - it seems like we wouldn't want 
contradictory things to be obligatory in any logic. But for some reason, not only is it not
a theorem of Carmo and Jones' logic, it actually implies some strange conclusions, including 
that everything is either permissible or obligatory. It's not clear to me from a semantic 
perspective why this would be the case. In fact this theorem seems like a desirable 
property. Potential avenue for exploration"(*>*)

subsection \<open>Kroy's Formalization\label{kroydetails}\<close>

text \<open>This section contains a formalization of the categorical imperative introduced by Moshe Kroy in 
1976 \citep{kroy}. Kroy used Hinktikka's deontic logic to formalize the Formula of Universal Law and
the Formula of Humanity. I will first import the additional logical tools that Hintikka's logic contains 
that Kroy relies on, then examine the differences between his logic and DDL, and finally implement 
and test both of Kroy's formalizations.\<close>

subsubsection \<open>Logical Background \label{sec:kroy_logical_background}\<close>

text \<open>Kroy's logic relies heavily on some notion of identity or agency. The logic must be capable of 
expressing statements like ``x does action", which I can write as ``x is the subject of the sentence
 `does action.'" This requires defining a subject.\<close>

typedecl s \<comment>\<open>s is the type for a ``subject," i.e. the subject of a sentence\<close>

text \<open>Kroy also defines a substitution operator\footnote{See page 196 in Kroy's original paper @{cite kroy}.}. $P (d/e)$ is read in his logic as ``P with e substituted 
for d." DDL has no such notion of substitution, so I will define a more generalized notion of an ``open 
sentence." An open sentence takes as input a subject and returns a complete or ``closed" DDL formula by, 
in effect, binding the free variable in the sentence to the input. For example, 
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

text \<open>Once again, the notion of permissibility will be useful here. Recall that an action can either be 
obligated, permissible, or prohibited. A permissible action is acceptable (there is no specific prohibition 
against it), but not required (there is no specific obligation requiring it).\<close>

abbreviation ddl_permissible::"t\<Rightarrow>t" ("P {_}")
  where "P {A} \<equiv> \<^bold>\<not> (O {\<^bold>\<not> A})"
abbreviation os_permissible::"os\<Rightarrow>os" ("\<^emph>P {_}")
  where "\<^emph>P {A} \<equiv> \<lambda>x. P {A(x)}"


text_raw \<open>\textbf{Differences Between Kroy's Logic (Kr) and DDL}\<close>


text \<open>There is potential for complication because Kroy's original paper uses a different logic than DDL. 
His custom logic is a slight modification of Hintikka's deontic logic @{cite hintikka}. In this section, 
I will determine if some of the semantic properties that Kroy's logic (which I will now call Kr) requires 
hold in DDL. These differences may become important later and can explain differences in my results and 
Kroy's.\<close>

text_raw \<open>\emph{Deontic alternatives versus the neighborhood semantics}\<close>

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
 deontic alternatives. Even if one believes that permissible 
statements should be true at some deontic alternative, it's not clear that permissible statements
 must be realized at some world. In some ways, this also coheres with our understanding of obligation. There 
are permissible actions like ``Lavanya buys a red folder" that might not happen in any universe.

An even stricter version of the semantics that Kr requires is that if something is permissible at a world, 
then it is obligatory at some world. This is a straightforward application of the Kripke semantics. Let's
test this proposition.\<close>

lemma permissible_semantics_strong:
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

  text_raw \<open>\emph{Obligatory statements should be permissible}\<close>

text \<open>Kr includes the intuitively appealing theorem that if a statement is obligated at a world, then it 
is permissible at that world\footnote{This follows straightforwardly from the Kripke semantics. If proposition $A$ is 
obligated at world $w$, this means that at all of $w$'s neighbors, $O A$ holds. Therefore, 
$\exists w'$ such that $w$ sees $w'$ and $O A$ holds at $w'$ so $A$ is permissible at $w$.}. Let's see 
if that also holds in DDL.\<close>

lemma ob_implies_perm:
  fixes A w
  shows "O {A} w \<longrightarrow> P {A} w"
  nitpick [user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 2:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)\color{black}\<close>

  text \<open>Intuitively, it seems untenable for any ethical theory to not include this principle. My 
formalization should add this as an axiom.\<close>

(*<*)text\<open>axiomatization where permissible_prepreq_ob: "\<Turnstile> (O {A} \<rightarrow> P {A})"\<close> (*>*)


subsubsection \<open>The Categorical Imperative \label{sec: kroy_ful}\<close>

text \<open>I will now implement Kroy's formalization of the Formula of Universal Law. Recall that the FUL says
``act only in accordance with that maxim which you can at the same time will a universal law" @{cite groundwork}.
Kroy interprets this to mean that if an action is permissible for a specific agent, then it must be permissible for everyone.
This formalizes the moral intuition prohibiting free-riding. According to the categorical imperative, no one is a moral exception.
Formalizing this interpretation requires using open sentences to handle the notion of substitution.\<close>
abbreviation FUL::"bool" where "FUL \<equiv> \<forall>w A. ((\<exists>p::s. ((P {A p}) w))  \<longrightarrow>( (\<forall>p.( P {A p}) w))) "

\<comment>\<open>In English, this statement roughly means that, if action $A$ is 
permissible for some person $p$, then, for any person $p$, action $A$ must be permissible. The notion of ``permissible $for$" 
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


  subsubsection \<open>Application Tests\label{sec:app_tests_kroy}\<close>

  text \<open>In the following sections, I will use the application and metaethical tests presenting in Sections \ref{sec:app_tests_naive} and \ref{sec:meta_tests_naive}
        to tease out the strengths and weaknesses of Kroy's formalization. While the formalization is considerably
        stronger than the naive formalization, it still fails many of these tests. Some of these failures 
        are due to the differences between Kroy's logic and my logic mentioned in Section \ref{sec:kroy_logical_background}, but some 
        reveal philosophical problems with Kroy's interpretation of what the formula of universal law means. 
        I will analyze these problems in the context of philosophical scholarship explicating the content 
        of the formula of universal law. The findings in these sections will inform milestones for my
        custom formalization of the categorical imperative. They also serve as an example of how formalized
        and automated ethics can reveal philosophical strengths and weaknesses of an ethical theory. \<close>

  text\<open>\textbf{Murder}\<close>

  text \<open>In Section \ref{sec:app_tests_naive}, I began by testing the naive interpretation's ability to show that murder 
is wrong. I started by showing the morally dubious proposition that if murder is possibly wrong, then 
it is actually wrong.\<close>

consts M::"t"
\<comment>\<open>Let the constant $M$ denote murder. I have defined no features of this constant, except that it is 
of the type term, which can be true or false at a set of worlds. Indeed, this constant as-is has no 
semantic meaning and could be replaced with any symbol, like `Q' or `Going to Target.' This constant 
will begin to take on features of the act of murder when I specify its properties. In the tests below, 
I specify its properties as the antecedents of lemmas. For example, the test below specifies that 
it is possible that murder is prohibited at the current world. This pattern will hold for most constants 
defined in Isabelle—they have no meaning until I program a meaning.\<close>

lemma wrong_if_possibly_wrong:
  shows "((\<diamond> (O {\<^bold>\<not> M})) cw) \<longrightarrow>  (\<forall>w. (O {\<^bold>\<not> M}) w)"
  by simp
\<comment>\<open>This sentence reads: ``If it is possible that murder is prohibited at world cw, then murder is prohibited 
at all worlds.\<close>

text \<open>This is the same result we got in Section \ref{sec:app_tests_naive}—if murder is possibly wrong at some world, it is wrong at
every world. The result is incredible strong—the mere possibility of wrongness at some world is sufficient
to imply prohibition at $\text{every world}$. 

Kroy's formalization shouldn't actually imply this property. Recall that this property held in the 
naive interpretation because it universalized a proposition across worlds (using the necessity operator).
Kroy, on the other hand, interprets the FUL as universalizing across $\text{people}$, not worlds. 
In other words, Kroy's formulation implies that if murder is wrong for someone, then it is wrong for 
everyone. 

The fact that this strange lemma holds is actually a property of DDL itself, not a property
of Kroy's formalization. Indeed, repeating this experiment in DDL, with no
additional axioms that represent the categorical imperative shows that, in DDL, if something is 
possibly wrong, it is wrong at every world. This implies that this is not a useful example to test any formulation. 
If a lemma is true in the base logic, without any custom axioms added, then it will hold for any set of  
custom axioms. Testing whether or not it holds as we add axioms tells us nothing, since it held in 
the base logic itself. Interesting cases are ones that fail (or are indeterminate) in the base logic, 
but become true as we add axioms. \<close>

text "To adapt the murder wrong axiom to capture the spirit of Kroy's formulation, I will modify if 
to state that if murder is wrong for one person, it is wrong for everyone."

consts M_kroy::"os"
\<comment>\<open>This time, murder is an open sentence, so that I can substitute in different agents.\<close>

lemma wrong_if_wrong_for_someone:
  shows "(\<exists>p. \<Turnstile> O {\<^bold>\<not>(M_kroy p)}) \<longrightarrow> (\<forall>p. \<Turnstile> O {\<^bold>\<not>(M_kroy p)})"
  proof 
    assume "(\<exists>p. \<Turnstile> O {\<^bold>\<not>(M_kroy p)})"
    show "(\<forall>p. \<Turnstile> O {\<^bold>\<not>(M_kroy p)})"
      using FUL \<open>\<exists>p. \<Turnstile>\<^emph>O{\<^emph>\<not>M_kroy} p\<close> by blast
  qed

  text \<open>This lemma gets to the heart of Kroy's formulation of the categorical imperative. If murder is prohibited
for a specific person $p$, then it must be prohibited for all people\footnote{This test case also revealed a 
bug in my original implementation of Kroy's formulation of the FUL, demonstrating the power of such 
automated tests and precise formulations to find bugs in ethical theories.}.\<close>

  text \<open>\textbf{Lying}\<close>

  text "For the naive implementation, I also tested the stronger proposition that if not 
everyone can simultaneously lie, then lying is prohibited. This is the equivalent of claiming that 
if lying fails the universalizability test, it is prohibited."

  text\<open>I want to represent the sentence``At all worlds, it is 
      not possible that everyone lies simultaneously." This requires the following two abbreviations. \<close>

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
\<comment>\<open>Armed with @{abbrev everyone_lies}, it's easy to represent the desired sentence. The abbreviation above 
reads, ``At all worlds, it is not possible that everyone lies."\<close>

text "Now that I have defined a sentence stating that lying fails the universalizability test, I can 
      test if this sentence implies that lying is impermissible."

lemma lying_prohibited:
  shows "lying_not_possibly_universal \<longrightarrow>  ( \<Turnstile>(\<^bold>\<not> P {lie(p)}))"
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 1 and card s = 2:

  Free variables:

    $\text{lying\_not\_possibly\_universal}$ = True

    $p = s_1$ \color{black}\<close>

  text \<open>Kroy's formulation fails this test, and is thus not able to show that if lying is not possible 
      to universalize, it is prohibited for an arbitrary person. To understand why this is happening, I 
      will outline the syllogism that I $\emph{expect}$ to prove that lying is prohibited.\<close>

  text_raw\<open>\begin{enumerate}
        \item \text{At all worlds, it is not possible for everyone to lie. (This is the assumed lemma lying\_not\_possibly\_universal)}
        \item At all worlds, there is necessarily someone who doesn't lie. (Modal dual of (1))
        \item If A is permissible for subject p at world w, A is possible for subject p at world w. (Modified Ought Implies Can)
        \item If A is permissible at world w for any person p, it must be possible for everyone to A at w. (FUL and (3)) 
        \item Lying is impermissible. (Follows from (4) and (1)) \end{enumerate}\<close>

text "Armed with this syllogism, I can figure out why this test failed."

lemma step2:
  shows "lying_not_possibly_universal \<longrightarrow> \<Turnstile>( (\<box> (\<lambda>w. \<exists>p. (\<^bold>\<not> (lie(p)) w)))) "
  by simp
\<comment>\<open>Step 2 holds.\<close>

lemma step3: 
  fixes A p w
  shows "P {A(p)} w \<longrightarrow> (\<diamond> (A(p)) w)"
  nitpick [user_axioms, falsify] oops
\<comment>\<open>$\color{blue}$ Nitpick found a counterexample for card `a = 1, card i = 1, and card s = 1:

  Free variables:
    A = ($\lambda x. \_$)($a_1$ := ($\lambda x. \_$)($i_1$ := False))
    p = $a_1$ $\color{black}$\<close>

  text \<open>As we see above, the syllogism fails at Step 3, explaining why the lemma doesn't 
        hold as expected. Kroy explicitly states\footnote{See footnote 19 on p. 199} that this lemma holds in his logic.

        The success of this lemma in Kroy's logic and the emptiness of his formalization of the FUL are 
        two errors that contribute to the failure of this test. First, the statement expressed in Step 3
        should not actually hold. Impossible actions can be permissible (do I need a citation?). For example, 
        imagine I make a trip to Target to 
        purchase a folder, and they offer blue and black folders. No one would claim that it's impermissible
        for me to purchase a red folder, or, equivalently, that I am obligated to not purchase a red folder.\<close>

  text \<open>
        The second issue is that Kroy's interpretation of the formula of universal law is circular.
        His formalization interprets the FUL as prohibiting A if there is someone for whom 
        $A$'ing is not permissible. This requires some preexisting notion of the permissibility of $A$, and 
        is thus circuar. The categorical imperative is supposed to be the complete,
        self-contained rule of morality @{cite groundwork}, but Kroy's version of the FUL prescribes obligations 
        in a self-referencing manner. The FUL is supposed to define what is permissible and what isn't, 
        but Kroy defines permissibility in terms of itself.
        
        Neither of these errors are obvious from Kroy's presentation of his formalization of 
        the categorical imperative. This example demonstrates the power of formalized ethics. Making
        Kroy's interpretation of the categorical imperative precise demonstrated a philosophical problem 
        with that interpretation.\<close>

  subsubsection \<open>Metaethical Tests \label{sec:meta_tests_kroy}\<close>

  text "In addition to testing specific applications of the theory, I am also interested in 
        metaethical properties, as in the naive interpretation. First, I will test if permissiblility
        is possible under this formalization."

lemma permissible:
  fixes A w
  shows "((\<^bold>\<not> (O {A})) \<^bold>\<and> (\<^bold>\<not> (O {\<^bold>\<not> A}))) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue}Nitpick found a model for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False)\color{black}\<close>

  text \<open>The above result shows that, for some action $A$ and world $w$, Nitpick can find a model where $A$
        is permissible at $w$. This means that the logic allows for permissible actions. If I further specify 
        properties of $A$ (such as `$A$ is murder'), I would want this result to fail.\<close>

  text "Next, I will test if the formalization allows arbitrary obligations."

lemma arbitrary_obligations:
  fixes A::"t"
  shows "O {A} w"
  nitpick [user_axioms=true, falsify] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 1 and card s = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False) \color{blue}\<close>

  text \<open>This is exactly the expected result. Any arbitrary action $A$ isn't obligated. A slightly 
        stronger property is ``modal collapse," or whether or not `$A$ happens' implies `$A$ is obligated'.\<close>

lemma modal_collapse:
  fixes A w
  shows "A w \<longrightarrow> O {A} w"
  nitpick [user_axioms=true, falsify] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 1 and card s = 1:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := True)
    w = $i_1$ \color{black}\<close>

  text \<open>This test also passes. Next, I will test if not ought implies can holds. Recall that I 
        showed in Section $\ref{sec:meta_tests_naive}$ that ought implies can is a theorem of DDL itself, so it should still hold.\<close>

lemma ought_implies_can:
  fixes A w
  shows "O {A} w \<longrightarrow> \<diamond> A w"
  using O_diamond by blast

text "This theorem holds. Now that I have a substitution operation, I also expect that if an action 
      is obligated for a person, then it is possible for that person. That should follow by the 
      axiom of substitution @{cite cresswell} which lets me replace the `A' in the formula above with 
      `A(p)'"

lemma ought_implies_can_person:
  fixes A w 
  shows "O { A(p)} w \<longrightarrow> \<diamond> (A (p)) w"
  using O_diamond by blast

text "This test also passes. Next, I will explore whether or not Kroy's formalization still allows 
      conflicting obligations."

lemma conflicting_obligations:
  fixes A w
  shows "(O {A} \<^bold>\<and> O {\<^bold>\<not> A}) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue} Nitpick found a model for card i = 2 and card s = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True) \color{black}\<close>

  text "Just as with the naive formalization, Kroy's formalization allows for contradictory obligations. 
        Testing this lemma in DDL without the FUL shows that this is a property of DDL itself. This is a good goal to have in mind when 
        developing my custom formalization. 

        Next, I will test the stronger property that if two maxims imply a
        contradiction, they may not be simultaneously willed."

lemma implied_contradiction:
  fixes A B w
  assumes "((A \<^bold>\<and> B) \<^bold>\<rightarrow> \<^bold>\<bottom>) w"
  shows "\<^bold>\<not> (O {A} \<^bold>\<and> O {B}) w"
  nitpick [user_axioms, falsify] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 2 and card s = 1:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := True, $i_2$  := False)
    B = ($\lambda x. \_$)($i_1$  := True, $i_2$  := False)
    w = $i_2$ \color{black}\<close>

  text \<open>  Just as with the naive formalization, Kroy's formalization allows implied contradictions because 
        DDL itself allows implied contradictions and Kroy's 
        formalization doesn't do anything to remedy this. 

      Next, I will test that an action is either obligatory, permissible, or 
      prohibited.\<close>

lemma ob_perm_or_prohibited:
  fixes A w
  shows "(O {A} \<^bold>\<or> (P {A} \<^bold>\<or> O {\<^bold>\<not> A})) w"
  by simp
\<comment>\<open>This test passes.\<close>

text \<open>I also expect obligation to be a strictly stronger property than permissibility. Particularly, 
if A is obligated, then A should also be permissible.\<close>
lemma obligated_then_permissible:
  shows "(O {A} \<^bold>\<rightarrow> P {A}) w"
  nitpick[user_axioms] oops
\<comment>\<open>This test fails in Kroy's interpretation!
\color{blue}Nitpick found a counterexample for card i = 2 and card s = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)\color{black}\<close>
(*<*)
lemma test:
  shows "(O {A} \<^bold>\<and> O {\<^bold>\<not>A}) \<^bold>\<rightarrow> (\<^bold>\<not> (O {A} \<^bold>\<rightarrow> P {A})) w"
  by simp
(*>*)
text "These tests show that, while Kroy's formalization is more powerful and more coherent than the naive formalization, it 
      still fails to capture most of the desired properties of the categorical imperative. Some of these 
      problems may be remedied by the fact that Kroy's logic doesn't allow contradictory obligations, 
      and that possibility will be interesting to explore in my own formalization."

subsubsection \<open>Miscellaneous Tests \label{sec: misc_tests_kroy}\<close>

text "In this section, I explore tests of properties that Kroy presents in his original paper. These 
tests not only test the features of the system that Kroy intended to highlight, but they may also 
inspire additional tests and criteria for my own formalization in Chapter 3. These tests further underscore 
the circularity of Kroy's formalization and the differences between my logic and his."

text "First, Kroy presents a stronger version of the formula of universal law and argues that his formalization
is implied by the stronger version. Let's test that claim."

abbreviation FUL_strong::bool where "FUL_strong \<equiv>  \<forall>w A. ((\<exists>p::s. ((P {A p}) w))  \<longrightarrow>( (( P { \<lambda>x. \<forall>p. A p x}) w)))"

lemma strong_implies_weak:
  shows "FUL_Strong \<longrightarrow> FUL"
  using FUL by blast
\<comment>\<open>This lemma holds, showing that Kroy is correct in stating that this version of the FUL is stronger than his original
   version.\<close>

text \<open>The difference between the stronger version and @{abbrev FUL} is subtle. The consequent of FUL is ``for all people $p$,
it is permissible that they $A$." The consequent of this stronger statement is ``it is permissible that 
everyone $A$." In particular, this stronger statement requires that it is permissible for everyone to
 $A$ simultaneously. Kroy immediately rejects this version of the categorical imperative, arguing that 
it's impossible for everyone to be the US president simultaneously, so this version of the FUL prohibits
running for president.

Most Kantians would disagree with this interpretation. Consider the classical example of lying, as presented 
in @{cite kemp} and in @{cite "KorsgaardFUL"}. Lying fails the universalizability test because in a 
world where everyone lied simultaneously, the practice of lying would break down. If we adopt Kroy's 
version, lying is only prohibited if, no matter who lies, lying is impermissible. As argued above, this 
rule circularly relies on some existing prohibition against lying for a particular person, and thus 
fails to show the wrongness of lying. It is tempting to claim that this issue explains why the tests 
above failed. To test this hypothesis, I will check if the stronger version 
of the FUL implies that lying is impermissible.\<close>

lemma strongFUL_implies_lying_is_wrong:
  fixes p
  shows "FUL_strong \<longrightarrow> \<Turnstile>(\<^bold>\<not> P {lie(p)})"
  nitpick[user_axioms, falsify] oops
\<comment>\<open>\color{blue}
Nitpick found a counterexample for card i = 1 and card s = 1:

  Free variable:
    p = $s_1$
\color{black}\<close>

  text "The test above also fails! This means that not even the stronger version of Kroy's formalization
        of the FUL can show the wrongness of lying. As mentioned earlier, there are two independent errors. The first is the 
        the assumption that impossible actions are impermissible and the second is the circularity of the 
        formalization. The stronger FUL addresses the second error, but the first remains."

  text "Kroy also argues that the FUL gives us recipes for deriving obligations, in addition to deriving
        permissible actions. Specifically, he presents the following two principles, which are equivalent 
        in his logic. These sentences parallel FUL and strong FUL."

abbreviation obligation_universal_weak::bool where "obligation_universal_weak \<equiv> \<forall>w A. ((\<exists>p::s. ((O {A p}) w))  \<longrightarrow>( (\<forall>p. ( O {A p }) w)))"
abbreviation obligation_universal_strong::bool where "obligation_universal_strong \<equiv> \<forall>w A. ((\<exists>p::s. ((O {A p}) w))  \<longrightarrow>( (( O { \<lambda>x. \<forall>p. A p x}) w)))"
\<comment>\<open>Just as with FUL and FUL strong, the weaker version of the above statement has the consequent, ``For all people, 
A is obligated." The stronger consequent is ``A is obligated for all people simultaneously."\<close>

lemma weak_equiv_strong:
  shows "obligation_universal_weak \<equiv> obligation_universal_strong"
  oops
\<comment>\<open>Isabelle is neither able to find a proof nor a countermodel for the statement above, so I can't say 
  if it holds or not without completing a full, manual proof. This aside is not very relevant to 
  my project, so I will defer such a proof.\<close>

  text \<open>These two statements are not necessarily equivalent in my logic, but are in Kroy's$\footnote{This follows from
        the fact that the Barcan formula holds in Kroy's logic but not in mine, as verified with Nitpick. See 
        Appendix for more.}$ This difference in logics may further explain why tests are not behaving as 
        they should. Nonetheless, Kroy argues that the FUL implies both statements above.\<close>

lemma FUL_implies_ob_weak:
  shows "FUL \<longrightarrow> obligation_universal_weak" oops
\<comment>\<open>Isabelle is neither able to find a proof nor a countermodel for this statement.\<close>

lemma FUL_implies_ob_strong:
  shows "FUL \<longrightarrow> obligation_universal_strong" oops
\<comment>\<open>Isabelle is neither able to find a proof nor a countermodel for this statement.\<close>

  text "Isabelle timed out when looking for proofs or countermodels to the statements above. This may be 
        an indication of a problem that Benzmueller warned me about—mixing quantifiers into a shallow
        embedding of DDL may be too expensive for Isabelle to handle. Not sure what to do about this. "

end(*>*)