(*<*) theory appendix imports paper224

begin (*>*)

section "Appendix"

subsection \<open>Maxims and Motives \label{maximmotive}\<close>

text \<open>
$\emph{Exclusion of Motive}$

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
property. Potential avenue for exploration"


end(*>*)