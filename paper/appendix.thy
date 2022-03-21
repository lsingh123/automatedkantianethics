(*<*) theory appendix imports paper224

begin (*>*)


section \<open>Alternate Definitions of a Maxim \label{maximmotive}\<close>

subsection \<open>Korsgaard's Act-Goal View\<close>

text \<open>I adopt O'Niell's definition of a maxim, which builds on Korsgaard's weaker interpretation of 
a maxim as an act, goal pair. She interprets Kant's example meanings as having the form ``to-do-this-act-for-
the-sake-of-this-end,'' which could be formalized as a pair of an act and goal \citep{actingforareason}.
For example, under this view, one example maxim might be, ``Falsely promise to repay a loan in order
to get some easy cash.'' 

O'Niell's view only differs from this view in the inclusion of the circumstances
on which the agent acts. This inclusion creates a representation of a maxim that is strictly more expressive than 
Korsgaard's interpretation; every (circumstance, act, goal) tuple can be represented as an (act, goal) pair
by simply dropping the circumstances, but the same (act, goal) pair could correspond to many different
(circumstance, act, goal) tuples, all with varying moral statuses. Because my representation of a maxim
is more expressive than Korsgaard's, my results are stronger than those that would be achieved with 
Korsgaard's view. Thus, proponents of Korsgaard's view could simply ignore the circumstances in my
representation of a maxim and still achieve their desired results. 

One issue with Korsgaard's view is that an actionable maxim will necessarily
require some circumstances built-in because the agent will need to know when to act on the maxim. For example,
the falsely promising maxim bakes in the circumstances that the actor has access to lender, needs money, 
and that the lender will expect their money back. At an even more granular level, this maxim implicitly includes
a definition of a lender and of falsely promising, both of which are circumstantial. Given that all
maxims necessarily include some circumstances, O'Niell's view makes these implicit circumstances
explicit. This precision is a benefit; so long as my circumstances are not so finely grained that they
are uninterpretable, they render O'Niell's maxims more precise than Korsgaard's maxims. 
\<close>

subsection \<open>Kitcher's View on Motives\<close>

text \<open>Kitcher begins with O'Niell's 
circumstance, act, goal view and expands it to include the motive for a maxim \citep{whatisamaxim}. 
This additional component is read as ``In circumstance C, I will do A in order to G because of M,'' 
where M may be ``duty'' or ``self-love.'' Kitcher argues that the inclusion of motive is necessary 
for the fullest, most general form of a maxim in order to capture Kant's idea that an action derives 
its moral worth from being done for the sake of duty itself. Under this view, the FUL would obligate maxims of the form 
``In circumstance C, I will do A in order to G because I can will that I and everyone else simultaneously
will do A in order to G in circumstance C.'' In other words, if Kant is correct in arguing that moral 
actions must be done from the motive of duty, the affirmative result of the FUL becomes 
the motive for a moral action.

While Kitcher's conception of a maxim captures Kant's idea of acting for duty's own sake, I will not implement it 
because it is not necessary for putting maxims through the FUL. Kitcher acknowledges that 
O'Niell's formulation suffices for the universalizability test, but merely argues that it is not the most general form of a maxim.
In order to pass the maxim through the FUL, it suffices to know the circumstance, act, and goal. The FUL
derives the motive that Kitcher bundles into the maxim, so automating the FUL does not require 
including a motive. The ``input'' to the FUL is a circumstance, act, goal tuple. My project takes 
this input and returns the motivation that the dutiful, moral agent would adopt, which is ``because this
maxim is morally worthy.'' Additionally, doing
justice to the rich notion of motive requires modelling the operation of practical reason itself, 
which is outside the scope of this project. My work focuses on the universalizability test, but future work that 
models the process of practical reason may use my implementation of the FUL as a ``library.'' Combined 
with a logic of practical reason, an implementation of the FUL can move from evaluating a maxim to 
evaluating an agent's behavior, since that's when acting from duty starts to matter.

\newpage
\<close>

section \<open>Kroy's Formalization\label{kroydetails}\<close>

text \<open>In this appendix, I implement a formalization of the categorical imperative introduced by Moshe Kroy in
1976 \citep{kroy}. Kroy used Hinktikka's deontic logic to formalize the Formula of Universal Law and
the Formula of Humanity. I will first import the additional logical tools that Hintikka's logic contains, 
then examine the differences between his logic and DDL, and finally implement 
and test Kroy's formalization of the FUL\<close>

subsection \<open>Implementing Kroy's Formalization \label{sec:kroy_logical_background}\<close>

text \<open>In this section, I present necessary logical background, working my way up to implementing Kroy's
formalization by the end of the section. First, Kroy's logic requires the notion of a subject, 
which I define as a new type, just as I did for my implementation.\<close>

typedecl s \<comment>\<open>s is the type for a ``subject," i.e. the subject of a sentence\<close>

text \<open>Kroy also defines a substitution operator.\footnote{See page 196 in \citet{kroy}.}
$P (d/e)$ is read in his logic as ``P with e substituted 
for d.'' DDL has no such notion of substitution, so I will use the more generalized notion of an ``open 
sentence,'' as I did for my formalization. An open sentence takes as input a subject and returns a 
complete or ``closed'' DDL formula by binding the free variable in the sentence to the input. For example, 
``does action'' is an open sentence that can be instantiated with a subject. \<close>

type_synonym os = "(s \<Rightarrow> t)"
\<comment>\<open>``$P$ sub $(d/e)$'' can be written as ``$S(e)$'', where $S(d) = P$.\<close>
\<comment>\<open>The terms that we substitute into are instantiations of an open sentence, and substitution 
re-instantiates the open sentence with a different subject.\<close>

text \<open>\noindent \textbf{New Operators}

Because Isabelle is strongly typed, I define new operators to handle open sentences. These operators 
are similar to DDL's original operators and will simplify notation. \<close>

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

text \<open>\noindent \textbf{Differences Between Kroy's Logic (Kr) and DDL}\<close>

text \<open>There is potential for complication because Kroy's original paper uses a different logic than DDL. 
His custom logic is a slight modification of Hintikka's deontic logic \citep{hintikka}. In this brief interlude, 
I examine if the semantic properties that Kroy's logic (which I abbreviate to Kr) requires 
hold in DDL. These differences may explain limitations of Kroy's formalization (including failed tests), but I argue that 
the alternative properties of DDL cohere better with moral intuition. Thus, even if Kroy's formalization
would pass more tests if it were implemented using Hintikka's logic, the logic itself would be less 
morally plausible than DDL, and would thus remain a worse implementation of automated Kantian ethics.  \<close>

text \<open>Many of the differences between Kr and DDL can be explained by a difference in their semantics. The most 
faithful interpretation of Kr is that if $A$ is permissible in a context, then 
it must be true at some world in that context. Kr operates under the ``deontic alternatives'' or Kripke semantics, 
summarized by Solt as follows: ``A proposition of the sort $O A$ is true at the actual world $w$ if and
only if $A$ is true at every deontic alternative world to $w$''  \citep{solt}. Under this view, permissible propositions
are obligated at some deontic alternatives, or other worlds in the system, but not at all of them. This
property does not hold in DDL.\<close>

lemma permissible_semantics:
  fixes A w
  shows "(P {A}) w \<longrightarrow> (\<exists>x. A(x))"
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False) \color{black}\<close>

text \<open>DDL uses neighborhood semantics, not the deontic alternatives view, which is why this
 proposition fails in DDL. In DDL, the $ob$ function abstracts away the notion of
 deontic alternatives. Even if one believes that permissible 
statements should be true at some deontic alternative, it's not clear that permissible statements
 must be realized at some world. This also coheres with our understanding of obligation. There 
are permissible actions like ``Lavanya buys a red folder'' that might not happen in any universe.

An even stricter version of the semantics that Kr requires is that if something is permissible at a world, 
then it is obligatory at some world. This is a straightforward application of the Kripke semantics. This
also fails in DDL.\<close>

lemma permissible_semantics_strong:
  fixes A w
  shows "P {A} w \<longrightarrow> (\<exists>x. O {A} x)"
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False) \color{black}\<close>

  text \<open>This also doesn't hold in DDL because DDL uses neighborhood semantics instead of the deontic 
alternatives or Kripke semantics. This also seems to cohere with our moral intuitions. The statement 
``Lavanya buys a red folder'' is permissible in the current world, but it's hard to see why it would 
be oblgiatory in any world.

Another implication of the Kripke semantics is that Kr disallows ``vacuously permissible statements.'' In 
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
prohibited somewhere, but this makes permissibility impossible, which is clearly undesirable. \<close>

(*<*)
text_raw \<open>\noindent \emph{Obligatory statements should be permissible}\<close>

text \<open>Kr includes the intuitively appealing theorem that if a statement is obligated at a world, then it 
is permissible at that world\footnote{This follows straightforwardly from the Kripke semantics. If proposition $A$ is 
obligated at world $w$, this means that at all of $w$'s neighbors, $O A$ holds. Therefore, 
$\exists w'$ such that $w$ sees $w'$ and $O A$ holds at $w'$ so $A$ is permissible at $w$.}. This theorem
does not hold in DDL.\<close>

lemma ob_implies_perm:
  fixes A w
  shows "O {A} w \<longrightarrow> P {A} w"
  nitpick [user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 2:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)\color{black}\<close>

  text \<open>Intuitively, it seems untenable for any ethical theory to not include this principle. My 
formalization should add this as an axiom.\<close>

text\<open>axiomatization where permissible_prepreq_ob: "\<Turnstile> (O {A} \<rightarrow> P {A})"\<close> (*>*)

text \<open>\noindent \textbf{Kroy's formalization of the FUL \label{sec: kroy_ful}}\<close>

text \<open>I now implement Kroy's formalization of the Formula of Universal Law. Recall that the FUL reads
``act only in accordance with that maxim which you can at the same time will a universal law'' \citep[34]{groundwork}.
Kroy interprets this to mean that if an action is permissible for a specific agent, then it must be permissible for everyone.
This formalizes the moral intuition prohibiting free-riding. According to the categorical imperative, 
no one is a moral exception.
\<close>

abbreviation FUL::"bool" where "FUL \<equiv> \<forall>w A. ((\<exists>p::s. ((P {A p}) w))  \<longrightarrow>( (\<forall>p.( P {A p}) w))) "
\<comment>\<open>If action $A$ is permissible for some person, then, for any person $p$, action $A$ must be 
permissible for $p$. The notion of ``permissible for'' 
is captured by the substitution of $x$ for $p$.\<close>

text \<open>This formalization does not hold in DDL, the base logic. This means that Kroy's formalization
already passes one test, and that adding it as an axiom will strengthen the logic.\<close>

lemma FUL:
  shows FUL
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card s = 2 and card i = 2:

  Skolem constants:
    A = ($\lambda x. \_$)($s_1$ := ($\lambda x. \_$)($i_1$ := True, $i_2$ := True), $s_2$ := ($\lambda x. \_$)($i_1$ := False, $i_2$ := False))
    
p = $s_1$
    
x = $s_2$\color{black}\<close>

axiomatization where FUL: FUL

text "Now that I have added Kroy's formalization of the FUL as an axiom, I will check that it is 
consistent by looking for a model that satisfies it and all the other axioms of DDL."

lemma True nitpick[user_axioms, satisfy, card=1] oops
\<comment>\<open>\color{blue} 
Nitpick found a model for card i = 1:

  Empty assignment\color{black}\<close>

  text "This completes my implementation of Kroy's formalization of the first formulation of the 
categorical imperative. I defined new logical constructs to handle Kroy's logic, studied the differences
between DDL and Kr, implemented Kroy's formalization of the Formula of Universal Law, and showed 
that it is both non-trivial and consistent."

  subsection \<open>Testing Kroy's Formalization\<close>

  text \<open>In this section, I use my testing framework to evaluate Kroy's formalization. I find that, while 
        the formalization is considerably
        stronger than the naive formalization, it still fails many of these tests. Some of these failures 
        are due to the differences between Kroy's logic and my logic mentioned in Section \ref{sec:kroy_logical_background}, but some 
        reveal philosophical problems with Kroy's interpretation of what the formula of universal law means.

\noindent \textbf{Obligations Universalize Across People}
I already showed above that Kroy's formalization is stronger than DDL. Next, I test whether or
not obligations universalize across people. This test passes, perhaps trivially, due to the fact that 
this property is definitionally the basis of Kroy's formalization; his formalization states, intuitively, 
that obligations must hold across all people. \<close>

lemma obligation_universalizes:
  shows "\<forall>w. (\<exists>p. O {A p} w) \<longrightarrow> (\<forall>p. O {A p} w)"
  nitpick[user_axioms, falsify=true] oops

  text \<open>\noindent \textbf{Obligations Universalize Across People} The next test verifies that obligations 
cannot contradict. Kroy's formalization fails this test
because Nitpick can find a model in which $A$ and $\neg A$ are both obligated.\<close>

lemma conflicting_obligations:
  fixes A w
  shows "(O {A} \<^bold>\<and> O {\<^bold>\<not> A}) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue} Nitpick found a model for card i = 2 and card s = 1:

  Free variable:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True) \color{black}\<close>

  text "Recall the stronger version of this property: if two maxims imply a
        contradiction, they may not be simultaneously obligated. This test also fails for Kroy's formalization.  "

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

  text \<open>\noindent \textbf{Distributive Property for Obligations} Next, I test the closely related 
distributive property for obligations. As expected, this property also fails, since it is a derivative 
of contradictory obligations.\<close>

lemma distributive_property:
  fixes A B w
  shows "O {A \<^bold>\<and> B} w \<equiv> O {A} \<^bold>\<and> O {B} w"
  nitpick [user_axioms, falsify] oops
\<comment>\<open>\color{blue}Nitpick found a counterexample for card i = 2 and card s = 1:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := False, $i_2$ := True)
    B = ($\lambda x. \_$)($i_1$ := True, $i_2$ := False) \color{black}
\<close>

  text\<open>\noindent \textbf{Prohibits Actions That Are Impossible to Universalize} Next, I test if Kroy's
formalization is strong enough to prohibit actions that are impossible to universalize. As when running
this test for my formalization, I need to define some logical background to run this test. I 
use lying as a toy example of an action that is impossible to universalize.  

To run this test, I epresent the sentence ``At all worlds, it is 
not possible that everyone lies simultaneously,'' in Kroy's logic. This requires the following abbreviations. \<close>

consts lie::os 
\<comment>\<open>This is an empty constant to represent the act of lying, which is an open sentence. Unlike Chapter 
\ref{applications}, I do not specify any properties of lying, so this could be replaced with any 
action that is impossible to universalize. \<close>

abbreviation everyone_lies::t where "everyone_lies \<equiv> \<lambda>w. (\<forall>p. (lie(p) w))"
\<comment>\<open>This represents the term ``all people lie".\<close>
\<comment>\<open>The term above is true for a set of worlds $i$ such that, at all the worlds $w$ in $i$, all people 
at $w$ lie.\<close>

abbreviation lying_not_possibly_universal::bool where "lying_not_possibly_universal \<equiv> \<Turnstile>(\<^bold>\<not> (\<diamond> everyone_lies))"
\<comment>\<open>Armed with @{abbrev everyone_lies}, it's easy to represent the desired sentence. The abbreviation above 
reads, ``At all worlds, it is not possible that everyone lies."\<close>

text "With this logical background, I can test if lying not being possible to universalize implies 
that it is prohibited. Surprisingly, Kroy's formalization fails this test."

lemma lying_prohibited:
  shows "lying_not_possibly_universal \<longrightarrow>  ( \<Turnstile>(\<^bold>\<not> P {lie(p)}))"
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue} Nitpick found a counterexample for card i = 1 and card s = 2:

  Free variables:

    $\text{lying\_not\_possibly\_universal}$ = True

    $p = s_1$ \color{black}\<close>

  text \<open>Kroy's formalization is not able to show that if lying is not possible 
      to universalize, it is prohibited. This is unexpected—Kroy's formalization seemingly hinges
on universalizability, so it seems as though it should pass this test. To understand this, I 
  outline the syllogism that one might $\emph{expect}$ to prove that lying is prohibited and 
test each component of this syllogism in Isabelle.\<close>

  text\<open>\begin{enumerate}
        \item At all worlds, it is not possible for everyone to lie. \emph{(This is the assumed sentence.)}
        \item At all worlds, there is necessarily someone who doesn't lie. \emph{(Modal dual of (1))}
        \item If A is permissible for subject p at world w, A is possible for subject p at world w. \emph{(Modified Ought Implies Can)}
        \item If A is permissible at world w for any person p, it must be possible for everyone to A at w. \emph{(FUL and (3))}
        \item Lying is impermissible. \emph{(Follows from (4) and (1))} \end{enumerate}\<close>

  text "I now test each step of this syllogism to determine where Kroy's formalize deviates from the
expected results. Step 1 holds by assumption, and Step 2 holds as shown below, but the syllogism breaks down
at Step 3."

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

  text \<open>The above lemma shows that the syllogism fails at Step 3, explaining why the lemma doesn't 
        hold as expected. Kroy explicitly states\footnote{See footnote 19 on p. 199 of \citet{kroy}} that 
        Step 3 holds in his logic, so this failure may be explained by this difference in Kr and DDL.
        However, upon reflection, it is not clear that the statement expressed in Step 3 should actually hold.
        Step 3 states that all permissible actions must be possible, but this implies that impossible
        actions are not permissible, so they must be prohibited, which seems silly. For example, 
        imagine I make a trip to Target to purchase a folder, and they offer blue and black folders. 
        Even though it is impossible for me to purchase a red folder, it doesn't seem impermissible
        for me to purchase a red folder.

        A deeper issue inspired by this test is that Kroy's interpretation of the FUL is 
        empty in a circular way. His formalization interprets the FUL as prohibiting $A$ if there is someone for whom 
        $A$'ing is not permissible. This requires some preexisting notion of the permissibility of $A$, and 
        is thus circuar. The categorical imperative is supposed to be the complete,
        self-contained rule of morality, but Kroy's version of the FUL prescribes obligations 
        in a self-referencing manner. The FUL is supposed to define what is permissible and what isn't, 
        but Kroy defines permissibility in terms of itself.
        
        Neither of these errors are obvious from Kroy's presentation of his formalization of 
        the categorical imperative. This is another example of the power of computational ethics. Making
        Kroy's interpretation of the categorical imperative precise demonstrated philosophical problems
        with that interpretation.\<close>

  text\<open>\noindent \textbf{Remaining Tests} It is clear that Kroy's formalization does not encode a robust conception of a maxim, as it
simply evaluates actions. Moreover, the emptiness discussed above implies that Kroy's formalization 
cannot actually generate \emph{any} obligations from scratch, and so the formalization automatically
fails to prohibit conventional or natural acts. 

Thus, this completes my testing of Kroy's formalization. While Kroy's formalization represents
some progress over the control group (it passes the first two tests), it is clear that many limitations
remain. My implementation passes all of the tests that Kroy's formalization fails, and thus represents
significant progress.
\<close>

  text \<open>\noindent \textbf{Miscellaneous Tests} I conclude my examination of Kroy's formalization by presenting
one more test specific to Kroy's formalization. In addition to his formalization of the FUL, Kroy also
presents a formalization of a stronger version of the FUL and argues that his formalization is implied
by the stronger version. I can test that claim by formalizing this stronger formalization as well. \<close>

abbreviation FUL_strong::bool where "FUL_strong \<equiv>  \<forall>w A. ((\<exists>p::s. ((P {A p}) w))  \<longrightarrow>( (( P { \<lambda>x. \<forall>p. A p x}) w)))"

lemma strong_implies_weak:
  shows "FUL_Strong \<longrightarrow> FUL"
  using FUL by blast
\<comment>\<open>This lemma holds, showing that Kroy is correct in stating that this version of the FUL is stronger than his original
   version.\<close>

text \<open>The difference between the strong and weak versions of the FUL is subtle. The consequent of FUL is ``for all people $p$,
it is permissible that they $A$." The consequent of this stronger statement is ``it is permissible that 
everyone $A$." This stronger statement requires that it is permissible for everyone to
$A$ simultaneously. Kroy immediately rejects this version of the categorical imperative, arguing that 
it's impossible for everyone to be the US president simultaneously, so this version of the FUL prohibits
running for president.

Most Kantians would disagree with this interpretation. Consider the classical example of lying, as presented 
in @{cite kemp} and in @{cite "KorsgaardFUL"}. Lying fails the universalizability test because in a 
world where everyone lies simultaneously, the practice of lying would break down. If we adopt Kroy's 
version, lying is only prohibited if, no matter who lies, lying is impermissible. As argued above, this 
rule circularly relies on some existing prohibition against lying for a particular person, and thus 
fails to show the wrongness of lying. 

This misunderstanding is actually related to another weakness of Kroy's formalization: it lacks
a robust conception of a maxim. Consider Kroy's example of the maxim of running for president. If the 
action being evaluated is, ``I will be president of the United States,'' as Kroy interprets it, then 
it is clearly not universalizable for the reason he argued. However, using the most robust circumstance,
act, tuple representation of a maxim, the maxim of action would be something like, ``When I believe 
that I would make a good president, I will launch a presidential campaign to become president.'' This 
more nuanced maxim is universalizable: it is clearly possible for all people who believe they would
make good presidents to run for president. Under this more sophisticated representation of a maxim, 
Kroy's stronger version of the FUL is actually correct.

It is tempting to claim that this issue explains why the tests above failed. To test this hypothesis, 
I check if the stronger version of the FUL implies that lying is impermissible. Sadly, even the stronger
version of the FUL fails this test.\<close>

lemma strongFUL_implies_lying_is_wrong:
  fixes p
  shows "FUL_strong \<and> lying_not_possibly_universal \<longrightarrow> \<Turnstile>(\<^bold>\<not> P {lie(p)})"
  nitpick[user_axioms, falsify] oops
\<comment>\<open>\color{blue}
Nitpick found a counterexample for card i = 1 and card s = 1:

  Free variable:
    p = $s_1$
   Skolem constant:
    $\lambda y$. p = ($\lambda x. \_$)($i_1$ := $s_2$)
\color{black}\<close>

  text \<open>The failure of this test implies that not even the stronger version of Kroy's formalization
        of the FUL can show the wrongness of lying. As mentioned earlier, there are two independent errors. The first is the 
        the assumption that impossible actions are impermissible and the second is the circularity of the 
        formalization. The stronger FUL addresses the second error, but the first remains, and so the
        stonger formalization of the FUL still fails this test.

        \newpage
\<close>
(*<*)
end(*>*)