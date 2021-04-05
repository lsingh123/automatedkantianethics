theory categorical_imperative_1 imports carmojones_DDL_completeness

begin

section "The Categorical Imperative"

subsection "Simple Formulation of the Kingdom of Ends"

text "This is my first attempt at formalizing the concept of the Kingdom of Ends"
text "NOTE: this attempt revealed a bug in my embedding. I've included it as an artifact, but none of these theorems hold anymore (hence the oops)."

abbreviation ddlpermissable::"t\<Rightarrow>t" ("P_")
  where "(P A) \<equiv> (\<^bold>\<not>(O {\<^bold>\<not>A}))"
\<comment> \<open>This operator represents permissibility\<close>
\<comment> \<open>Will be useful when discussing the categorical imperative\<close>
\<comment> \<open>Something is permissible if it is not prohibited\<close>
\<comment> \<open>Something is prohibited if its negation is obligatory\<close>


lemma kingdom_of_ends_1:
  shows "\<Turnstile> ((O {A}) \<^bold>\<rightarrow> (\<box> (P A)))"
  oops
\<comment> \<open>One interpretation of the categorical imperative is that something is obligatory only if it is permissible in every ideal world\<close>
\<comment> \<open>This formulation mirrors the kingdom of ends.\<close>
\<comment> \<open>This formulation is already a theorem of carmo and jones' DDL!.\<close>
\<comment> \<open>It can be shown using the O diamond rule, which just says that obligatory things must be possible.\<close>
\<comment> \<open>There are two possibilities: either the logic is already quite powerful OR this formulation is ``empty".\<close>


lemma kingdom_of_ends_2:
  shows "\<Turnstile> ((\<box> (P A)) \<^bold>\<rightarrow> (O {A}))"
  oops

\<comment> \<open>Notice also that ideally, this relationship does not hold in the reverse direction.\<close>
\<comment> \<open>Plenty of things are necessarily permissible (drinking water) but not obligatory.\<close>
\<comment> \<open>Very strange that this is a theorem in this logic.....\<close>
\<comment> \<open>That being said, Isabelle seems quite upset with this proof and is very slow to resconstruct it\<close>
\<comment> \<open>I am struggling to recreate this proof on paper\<close>


lemma permissible_to_ob:
  shows "\<Turnstile> ((P A) \<^bold>\<rightarrow> (O {A}))"
  oops
\<comment> \<open>Uh-oh.....this shouldn't be true...\<close>
\<comment> \<open>Not all permissable things are obligatory.....\<close>

lemma weaker_permissible_to_ob:
  shows "\<Turnstile> ((\<diamond> (P A)) \<^bold>\<rightarrow> O {A})"
    oops
\<comment> \<open>Makes sense that this follows from the reverse kingdom of ends.\<close>
\<comment> \<open>Obligation and necessity/possibility are separated in this logic\<close>
\<comment> \<open>Both the dyadic obligation and necessity operator are world agnostic\<close>

lemma contradictory_obligations:
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

text "Did some debugging. What was the problem? A misplaced parentheses in the definition 
of ax5b that led to a term being on the wrong side of an implication. Computer Science :( "

text "After the debugging, all of this is no longer true! On to the next attempt :)"

end







