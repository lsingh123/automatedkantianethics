(*<*) theory appendix imports paper224

begin (*>*)

section "Appendix"

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


end