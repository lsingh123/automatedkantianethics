theory categorical_imperative_1 imports carmojones_DDL_completeness

begin

section "The Categorical Imperative"

subsection "Simple Formulation of the Kingdom of Ends"

text "This is my first attempt at formalizing the concept of the Kingdom of Ends"

abbreviation ddlpermissable::"t\<Rightarrow>t" ("P_")
  where "(P A) \<equiv> (\<^bold>\<not>(O {\<^bold>\<not>A}))"
\<comment> \<open>This operator represents permissibility\<close>
\<comment> \<open>Will be useful when discussing the categorical imperative\<close>
\<comment> \<open>Something is permissible if it is not prohibited\<close>
\<comment> \<open>Something is prohibited if its negation is obligatory\<close>


\<comment> \<open>lemma kingdom_of_ends_1:
  shows "$\vdash$ ((O {A}) $\longrightarrow$ (\<box> (P A)))"
  by (metis O_diamond ax_5b)

One interpretation of the categorical imperative is that something is obligatory only if it is permissible in every ideal world
This formulation mirrors the kingdom of ends.
This formulation is already a theorem of carmo and jones' DDL!.
It can be shown using the O diamond rule, which just says that obligatory things must be possible.
There are two possibilities: either the logic is already quite powerful OR this formulation is ``empty".


lemma kingdom_of_ends_2:
  shows $\vdash ((\square (P A)) \longrightarrow (O A))$
  by (metis O_diamond ax_5a ax_5b ax_5c)

Notice also that ideally, this relationship does not hold in the reverse direction.
Plenty of things are necessarily permissible (drinking water) but not obligatory.
Very strange that this is a theorem in this logic.....
That being said, Isabelle seems quite upset with this proof and is very slow to resconstruct it
I am struggling to recreate this proof on paper


lemma permissible_to_ob:
  shows $\vdash ((P A) (O A))$
proof -
have "ob $\top$ ($\sim$ A) $\vee$ ob $\top$ A"
using kingdom_of_ends_2 by presburger
  then show ?thesis
by meson
qed
Uh-oh.....this shouldn't be true...
Not all permissable things are obligatory.....

lemma weaker_permissible_to_ob:
  shows "$\vdash ((\diamond (P A)) \longrightarrow O A)$"
  using kingdom_of_ends_2 by auto
Makes sense that this follows from the reverse kingdom of ends.
Obligation and necessity/possibility are separated in this logic
Both the dyadic obligation and necessity operator are world agnostic

lemma contradictory_obligations:
  shows "$\vdash(\sim ((O A) \wedge (O (\sim A))))$"
  by (metis ax_5a ax_5b)
What is the cause of the above strangeness?
This very intuitive theorem holds in my logic but not in Benzmuller Parent's
It's clear that this theorem results in the strange results above.
Conclusion: There is a bug in my embedding \<close>


text "Sidebar: the above theorem is really intuitive - it seems like we wouldn't want 
contradictory things to be obligatory in any logic. But for some reason, not only is it not
a theorem of Carmo and Jones' logic, it actually implies some strange conclusions, including 
that everything is either permissible or obligatory. It's not clear to me from a semantic 
perspective why this would be the case. In fact this theorem seems like a desirable 
property. Potential avenue for exploration"

text "Did some debugging. What was the problem? A misplaced parentheses in the definition 
of ax5b that led to a term being on the wrong side of an implication. Computer Science "

text "After the debugging, all of this is no longer true! On to the next attempt"

end







