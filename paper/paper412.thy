theory paper412 imports paper41

begin


subsection "Application Tests"

text \<open>As with the naive formalization and Kroy's formalization, I will apply my testing framework to 
my custom formalization of the FUL. I will begin with some basic application tests. In these tests, 
I specify particular maxims as constants with no properties and gradually add properties to understand 
how the system handles different kinds of maxims. \<close>

text \<open>I will show that the maxim, ``When strapped for cash, falsely promise to pay your friend back
to get some easy money." is prohibited. This example is due to Korsgaard and she uses it to highlight 
the strength of her preferred interpretation of the FUL, the practical contradiction interpretation \cite{KorsgaardFUL}.
There are two possible readings of this maxim, and I will show that my formalization can handle both. 
Under the first reading, the act of falsely promising is read as
as entering a pre-existing, implicit, social system of promising with no intention of upholding your 
promise. Under the second reading, the act of falsely promising is equivalent to uttering the worlds 
``I promise X" without intending to do X. The differences between these readings lies in the difference 
between promising as an act with meaning in a larger social structure and the utterance ``I promise."

Under the first reading, the maxim fails because falsely promising is no longer possible in a world where 
everyone everyone does so. This is how the logical contradiction interpretation reads this maxim—falsely 
promising is no longer possible when universalized because the institution of promising breaks down. 
The practical contradiction view also prohibits this maxim because if falsely promising is not longer 
possible, then it is no longer an effective way to achieve the end of getting some money. Below I 
define some logical tools to formalize this reading of this maxim. \<close>

consts when_strapped_for_cash::t
\<comment>\<open>Constant representing the circumstances ``when strapped for cash." Recall that the type of circumstances 
is a term because circumstances can be true or false at a world.\<close>
consts falsely_promise::os
\<comment>\<open>Constant representing the act ``make a false promise to pay a loan back." Recall that the type of
an act is an open sentence because the sentence ``subject s performs act a" can be true or false at a world.\<close>
consts to_get_easy_cash::t
\<comment>\<open>Constant representing the goal ``to get some money." Recall that the type of a goal 
is a term because a goal can be true or false at a world depending on whether it is achieved or not.\<close>

abbreviation false_promising::maxim where 
"false_promising \<equiv> (when_strapped_for_cash, falsely_promise, to_get_easy_cash)"
\<comment>\<open>Armed with the circumstances, act, and goal above, I can define the example maxim as a tuple.\<close>

text \<open>The logical objects above are ``empty," in the sense that I haven't specified any of their 
relevant properties. I will define these properties as assumptions and will show that, if the maxim 
above satisfies the assumed properties, it is prohibited.\<close>

abbreviation everyone_can't_lie where 
"everyone_can't_lie \<equiv> \<forall>w. \<not> (\<forall>s. falsely_promise(s) w) "
\<comment>\<open>Under this reading, the problem with this maxim is that everyone can't
falsely promise simultaneously because the institution of promising will break down. It's probably 
possible to say something stronger than this (i.e. that if enough but not necessarily all people
falsely promise promising is no longer possible), but for my purposes this will suffice. The above 
formula reads, ``At all worlds, it is not the case that everyone falsely promises." \<close>

abbreviation circumstances_hold where 
"circumstances_hold \<equiv> \<forall>w. when_strapped_for_cash w"
\<comment>\<open>This assumption narrows our scope of consideration to worlds where the circumstances of 
being strapped for cash hold. This is important because, at worlds where the circumstances do not hold, 
a maxim is trivially effective (since it's never acted on) and thus trivially universalizable. This 
assumption also makes practical sense; when evaluating a maxim, an agent would care about it specifically
at worlds where the circumstances hold, since these are the worlds where the maxim actually prescribes action.\<close>

abbreviation example_is_well_formed where 
"example_is_well_formed \<equiv> \<forall>s. \<Turnstile> (well_formed false_promising s)"
\<comment>\<open>This assumption states that the maxim of falsely promising is well-formed. This breaks down into
two individual assumptions. First, being strapped for cash can't imply falsely promising, which is plausible
because many people won't falsely promise under conditions of poverty. Second, being strapped for cash
can't imply getting ready cash, which is also plausible because people often fail to secure cash even 
when they need it.\<close>

text \<open>Putting it all together, I want to show that if the three assumptions justified above hold, then 
the constructed maxim is prohibited. Below is the proof\<close>

lemma lying_bad_1:
  assumes everyone_can't_lie
  assumes circumstances_hold
  assumes example_is_well_formed
  shows "\<forall>s. \<Turnstile> (prohibited false_promising s)"
proof-
  have "\<forall>s. not_universalizable false_promising s"
    by (simp add: assms(1) assms(2))
\<comment>\<open>I manually broke the proof into this intermediate lemma and the conclusion, and then Sledgehammer 
automatically found a proof.\<close>
  thus ?thesis
    using FUL assms(3) by blast 
qed

text \<open>Under the second reading of this maxim, the act ``falsely promising" refers to uttering the 
sentence ``I promise to do X" with no intention of actually doing X\footnote{Note that under this 
reading, the maxim isn't prohibited under the logical contradiction interpretation because making an 
utterance is still possible even if eveyrone else makes that utterance. I will discuss this in detail 
later in this section in the context of the difference between natural and conventional acts.}. 
Under this reading, the practical contradiction interpretation prohibits this maxim because, in a world 
where false promising is universalized, no one believes promises anymore, so the utterance is no longer 
an effective way to get money. Below I formalize this reading of this maixm.\<close>

consts believed::os 
abbreviation false_promising_not_believed where 
"false_promising_not_believed \<equiv> \<forall>w s. (falsely_promise(s) w \<longrightarrow> \<not> believed(s) w)"
\<comment>\<open>This abbreviation formalizes the idea that if everyone falsely promises, then no one is believed
when promising.\<close>

abbreviation need_to_be_believed where 
"need_to_be_believed \<equiv> \<forall>w s. (\<not> believed(s) w \<longrightarrow> \<^bold>\<not>((falsely_promise s) \<^bold>\<rightarrow> to_get_easy_cash)w)"
\<comment>\<open>This abbreviation formalizes the idea that if a promise is not believed, then it is not an effective
way of getting easy cash.\<close>

lemma falsely_promising_bad_2:
  assumes false_promising_not_believed
  assumes need_to_be_believed
\<comment>\<open>The above two assumptions are specific to this reading and justified above.\<close>
  assumes circumstances_hold
  assumes example_is_well_formed
\<comment>\<open>These two assumptions applied to the first reading as well and were justified there.\<close>
  shows "\<forall>s. \<Turnstile> (prohibited false_promising s)"
proof-
  have "\<forall>s. not_universalizable false_promising s"
    using assms(1) assms(2) assms(3) by auto
  thus ?thesis
    using FUL assms(4) by blast
qed
\<comment>\<open>With some help, Isabelle is able to show that the maxim is prohibited under this reading as well.\<close>

text \<open>This example demonstrates that my formalization is able to correctly prohibit this maxim, regardless
of its reading. This is additionally important because the two readings of this maxim represent reading 
the act as either a conventional or natural action, so my intrepretation can correctly handle both kinds
of actions. Korsgaard draws a distinction between conventional acts and natural acts. Conventional acts 
exist within a practice, which is "comprised of certain rules, and its existence (where it is not embodied in 
an institution with sanctions) consists in the general acknowledgement and following of those rules" 
\cite[10]{KorsgaardFUL}. For example, promising is a conventional act because it only exists as a 
practice. Murder, on the other hand, is an example of a natural act because its existence only depends
on the laws of nature\cite[11]{KorsgaardFUL}.

This distinction is important because Korsgaard argues that only the practical contradiction view can 
satisfactorily explain the wrongness of certain natural acts like murder\footnote{For more discussion 
of Korsgaard's argument for the practical contradiction view, see Section Philosophical Writing}. 
The practical contradiction view is thus stronger than the logical contradiction view because it can 
explain the wrongness of both conventional and natural acts. 

The fact that my interpretation can correctly show the wrongness of both conventional and natural acts
is evidence for its correctness as a formalization of the practical contradiction interpretation. 
The first reading of the example maxim reads the act 
``making a false promise" as entering into an agreement within a socially established system of promising. 
This is clearly a conventional act, and because it is a conventional act, it is not just contradictory
when universalized but literally impossible because the practice breaks down. I capture this idea in the 
assumption @{abbrev everyone_can't_lie}, which states that, at all worlds, not everyone can falsely promise since 
otherwise the practice of promising would break down. The second reading, on the other hand, reads the 
act of making a false promise as uttering the statement ``I promise to pay you back," while never intending 
to fulfill this promise. This is a natural act because the act of uttering a sentence does not rely 
on any conventions, merely the laws of nature governing how your mouth and vocal cords behave\footnote{
Linguistic relativists may take issue with this claim and may argue that if the English language had 
never developed, then making this utterance would be impossible. Even if this is true, the laws of 
nature itself would not prohibit making the sounds corresponding to the English pronounciation of 
this phrase, so the act would still not be impossible in the way that a conventional act can be.} 

I show above that my formalization shows the wrongness of this maxim under both readings. Under the 
first reading, promising becomes impossible, so both the logical and 
practical contradiction interpretations prohibit the maxim. Under the second reading, promising is still
possible, but becomes ineffective because people no longer interpret the utterance as creating a commitment.
Under this view, only the practical contradiction interpretation succeeds in prohibiting the maxim. Thus, 
not only does my formalization likely capture the practical contradiction interpretation (as opposed to 
the teleological or logical contradiction interpretations), it also adequately handles both natural 
and conventional acts. \<close>

text\<open>I can also use Isabelle to confirm that the two readings are different. If they were the same, 
we would expect the assumptions corresponing to each to be equivalent. The RHS of the lemma below represents 
the second reading and the LHS represents the first reading.\<close>

lemma readings_are_equivalent:
  shows "false_promising_not_believed \<and> need_to_be_believed \<equiv> everyone_can't_lie"
  nitpick[user_axioms] oops
\<comment>\<open>Nitpick finds a counterexample, showing that the two readings are different.
\color{blue}
Nitpick found a counterexample for card i = 1 and card s = 1:

  Empty assignment
\color{black}
\<close>

  text \<open>This completes the application tests for my formalization. I showed that my formalization correctly 
handles an example from Korsgaard with two possible interpretations and also sufficiently handles both 
conventional and natural acts.\<close>

subsection "Metaethical Tests"

text \<open>Recall that metaethical tests test formal properties of the system that apply to any maxim, not 
just those specified in the application tests. In this section I adapt the metaethical tests developed 
in previous sections to my formalization of the categorical imperative. I preserved the philosophical 
goal of each test but modified them to test the stronger, richer notion of a maxim.

The first set of tests consider how obligation generalizes, first across worlds and then across
people. As expected, the tests below show that both wrongness (prohibition) and rightness (obligation)
generalize across both worlds and people. In other words, if something is obligated at some world, it 
is obligated at every world and if something is obligated for some person, then it is obligated for 
every person. 

Generalization across worlds is a consequence of the fact that my interpretation does not make use of the 
modal nature of DDL. In particular, I do not use any property of the world when prescribing obligations 
at that world. \<close>

lemma wrong_if_wrong_for_someone:
  shows "\<forall>w. \<forall>c::t. \<forall>g::t. \<exists>s::s. O{\<^bold>\<not> (W (c, M, g) s) | c} w \<longrightarrow> (\<forall>p.  O{\<^bold>\<not> (W (c, M, g) p) | c} w) "
  by blast

lemma right_if_right_for_someone:
  shows "\<forall>w. \<forall>c::t. \<forall>g::t. \<exists>s::s. O{W (c, M, g) s | c} w \<longrightarrow> (\<forall>p.  O{W (c, M, g) p | c} w) "
  by blast

lemma wrong_if_wrong_somewhere:
  shows "\<forall>c g. \<exists>w1. O{\<^bold>\<not> (W (c, M, g) s) | c} w1 \<longrightarrow> (\<forall>w2.  O{\<^bold>\<not> (W (c, M, g) s) | c} w2)"
  by blast

lemma right_if_right_somewhere:
  shows "\<forall>c g. \<exists>w1. O{W (c, M, g) s | c} w1 \<longrightarrow> (\<forall>w2.  O{W (c, M, g) s | c} w2)"
  by blast

text \<open>As expected, obligation generalizes across people and worlds. In the next set of tests, I will 
analyze basic properties of permissibility, obligation, and prohibition. 

First, I verify that the logic allows
for permissible maxims, as this is a problem that prior iterations ran into. Below, I use Nitpick to 
find a model in which there is a circumstance, act, goal tuple that is permissible but not 
obligated at some world. \<close>

lemma permissible:
  shows "((\<^bold>\<not> (O{(W (c, a, g) s) | c})) \<^bold>\<and> (\<^bold>\<not> (O{\<^bold>\<not> (W (c, a, g) s) | c}))) w"
  nitpick [user_axioms, falsify=false] oops
\<comment>\<open>\color{blue}Nitpick found a model for card i = 1 and card s = 1:

  Free variables:
    a = ($\lambda x. \_$)($s_1$ := ($\lambda x. \_$)($i_1$ := False))
    c = ($\lambda x. \_$)($i_1$ := False)
    g = ($\lambda x. \_$)($i_1$ := False)
    s = $s_1$\color{black}
Recall that Nitpick is a model checker that finds models making certain formulae true or false. In this 
case, Nitpick finds a model satisfying the given formula (which simply requires that the sentence 
``s wills (c, a, g)'' is permissible but not obligator). This model consists of the above specifications 
of a, c, g, and s. \<close>

  text \<open>I also expect that any arbitrary maxim should be either permissible or prohibited, since all 
acts are either permissible or prohibited. \<close>

lemma perm_or_prohibited:
  shows "((permissible (c, a, g) s) \<^bold>\<or> (prohibited (c, a, g) s)) w"
  by blast
\<comment>\<open>This simple test passes immediately by the definitions of  permissible and prohibited.\<close>

text \<open>Obligation should be strictly stronger than permissibility. In other words, if a maxim is 
obligated at a world, it should be permissible at that world. Below I test this property.\<close>

lemma obligated_then_permissible:
  shows "(O{W(c, a, g) s|c} \<^bold>\<rightarrow> ((permissible (c, a, g) ) s)) w "
  using no_contradictions by auto
\<comment>\<open>This test passes and Isabelle is able to find a proof for the fact that all obligatory maxims are 
also permissible.\<close>

text \<open>The above test failed under Kroy's formalization of the categorical imperative and is thus evidence 
that my formalization improves upon Kroy's. Interestingly, this new test passes because of the additional
added axiom that prohibits contradictory obligations (recall that Kroy's formalization allowed contradictory
obligations). \<close>

  text "Next, I will test if the formalization allows for vacuous obligations or modal collapse. These 
tests are sanity checks confirmed that the obligation operator is doesn't collapse. First, I will check 
that any arbitrary term isn't obligated. "

lemma arbitrary_obligations:
  fixes c A::"t"
  shows "O{A|c} w"
  nitpick [user_axioms=true, falsify] oops
\<comment>\<open>This test passes—Nitpick finds a model where A isn't obligated in circumstances c.
\color{blue} Nitpick found a counterexample for card i = 1 and card s = 2:

  Free variables:
    A = ($\lambda x. \_$)($i_1$ := True)
    c = ($\lambda x. \_$)($i_1$ := False) \color{blue}
Previous iterations of this test used the monadic obligation operator, which tests the term in the 
context ``True" (equivalently the set of all worlds since True holds everywhere). In this iteration, 
I test the term in a context c, because my formalization uses the dyadic obligation operator and must 
thus specify circumstances.\<close>

  text \<open>This is exactly the expected result. Any arbitrary action $A$ isn't obligated. A slightly 
        stronger property is ``modal collapse," or whether or not `$A$ happens' implies `$A$ is obligated'. 
The proposition below should be falsifiable.\<close>

lemma modal_collapse:
  shows "((W (c, a, g) s) w) \<longrightarrow> O{W (c, a, g) s|c} w"
  nitpick [user_axioms=true, falsify] oops
\<comment>\<open>Nitpick finds a counterexample, so willing doesn't imply obligation, so this test passes. 
\color{blue}Nitpick found a counterexample for card i = 1 and card s = 2:

  Free variables:
    a = ($\lambda x. \_$)($s_1$ := ($\lambda x. \_$)($i_1$ := False), $s_2$ := ($\lambda x. \_$)($i_1$ := False))
    c = ($\lambda x. \_$)($i_1$ := False)
    g = ($\lambda x. \_$)($i_1$ := False)
    s = $s_2$
    w = $i_1$\color{black}
Once again, I modify this test to use the dyadic obligation operator instead of the monadic operator. \<close>

  text \<open>The final set of tests deal with ought implies can and conflicting obligations. Recall that I 
specifically added an axiom in my formalization to disallow contradictory obligations, so I expect 
these tests to pass. Kroy's formalization fails these tests, so this is another area of improvement 
over Kroy's formalization. \<close>

lemma ought_implies_can:
  shows "O{W (c, a, g) s|c} w \<longrightarrow> (\<diamond> W (c, a, g) s) w"
  using O_diamond by blast
\<comment>\<open>This test is a lemma of DDL itself, so it's no surprise that this test passes.\<close>

lemma conflicting_obligations:
  shows "\<not> (O{W (c, a, g) s|c} \<^bold>\<and> O{\<^bold>\<not>(W (c, a, g) s)| c}) w"
  using no_contradictions by blast
\<comment>\<open>This test passes immediately by the new axiom prohibited contradictory obligations.\<close>

lemma implied_contradiction:
  assumes "(((W (c1, a1, g1) s) \<^bold>\<and> (W (c2, a2, g2) s)) \<^bold>\<rightarrow> \<^bold>\<bottom>) w"
  shows "\<^bold>\<not> (O{W(c1, a1, g1) s|c} \<^bold>\<and> O{W(c2, a2, g2) s|c}) w"
  using assms no_contradictions by blast
\<comment>\<open>Recall that the we also expect the stronger property that the combination of obligatory maxims can't
 imply a contradiction. The added axiom also makes this test pass. \<close>

lemma distribution:
  assumes "\<Turnstile> (O {A} \<^bold>\<and> O {B})"
  shows "\<Turnstile> O {A \<^bold>\<and> B}"
  using assms no_contradictions by fastforce 

text \<open>The metaethical test suite ran on both Kroy's formalization and my formalizaion show two clear 
improvements. First, my formalization shows that obligatory maxims are permissible, whereas Kroy's 
paradoxically does not. Second, my formalization doesn't allow contradictory maxims, but Kroy's does. 
Both of these improvements are derived from the new axiom I added in my formalization that disallows 
contradictory obligations. Additionally, my formalization also improves on Kroy's by staying faithful to the 
strongest interpretation of the FUL, Korsgaard's practical contradiction interpretation. (maybe stick 
philosophical writing here or above?) \<close>

subsection "Formalization Specific Tests" 

text \<open>In this section, I explore tests specific to my formalization of the categorical imperative. First, 
in my previous (buggy) implementation of DDL, prohibiting contradictory obligation led to the strange 
result that all permissible actions are obligatory. I will test if this bug appears in this implementation 
as well.\<close>

lemma bug:
  shows "permissible (c, a, g) s w \<longrightarrow> O{W(c, a, g) s | c} w"
  nitpick[user_axioms] oops
\<comment>\<open>\color{blue}
Nitpick found a counterexample for card i = 1 and card s = 2:

  Free variables:
    a = ($\lambda x. \_$)($s_1$ := ($\lambda x. \_$)($i_1$ := False), $s_2$ := ($\lambda x. \_$)($i_1$ := False))
    c = ($\lambda x. \_$)($i_1$ := False)
    g = ($\lambda x. \_$)($i_1$ := False)
    s = $s_2$
    w = undefined
\color{black}
This strange result does not hold; good!\<close>

(*<*)
  text \<open>This is a formulation of the FUL in which, assuming every maxim is universalized at some
world (this is the axiom imagination works), at that world (or other worlds like it), if the maxim is 
not effective for the agent, then it is prohibited at the current world cw. Couple of optimizations 
necessary to get Nitpick able to handle this:
(1) Couldn't use the effective and will functions becuase they made Nitpick time out. Is there a way 
to have a purely syntactic version of these functions? They'll make notation prettier? Like an 
abbreviation with free variables?

(2) If I quantify over the maxim's components, then Nitpick times out. If I specify a 
single maxim as a constant, then it can handle everything just fine. I could try, every 
time I'm working with an example, specifying properties of these constants. The downside is that if I want 
to work with 2 maxims at once, then I have to add more constants and add the FUL as an axiom again for each of these maxims. This might not 
be too annoying in practice (I don't think I'll need that many maxims), but there's something theoretically
unsatisfying about it. I guess one theoretical explanation is that the system can only handle small models?
Which is maybe not a huge problem?


One worry is the order of the universal quantifier and the $\vDash$ or derivability symbol. In this 
representation, the universal quantifier is tightly bound to the left hand side of the equation, so it 
only quantifies into the statement ``All p will maxim M at any world." We can imagine an alternate
representation that quantifies over the sentence $\vDash W M p \longrightarrow \sim E M s$. This is 
a sentence of type $s \longrightarrow bool$, since it accepts a subject ($p$) as input and returns 
a boolean (the result of $p$ substituted into the sentence.) Thus, applying the universal quantifier 
$\forall p$ to this sentence results in a boolean that tracks the universalizability (or lack thereof) 
of the maxim. I chose my representation because it tracks the intuitive meaning of the universalizability 
test better: ``IF (the maxim is universalized) THEN (it is no longer effective)".

It's not clear to me if there's any intuitive difference between these two representations, but the lemmas 
below (using simplified versions of the representations) show that my representation is weaker than 
the representation where the quantifier has larger scope. This seems promising—the representation in 
lemma test\_2 is likely too strong because the quantifier quantifies into $M a$ as well. It really 
doesn't seem like this should make a difference, since $p$ never appears on the RHS expression. Let's
see if Prof. Amin has insight.\<close>

text \<open>axiomatization where imagination_works:"$\forall$M::maxim.  (not_contradictory M) \<longrightarrow>  (imagine_a_world M)"\<close>
\<comment>\<open>This axiom says, effectively, that our imagination works. In other words, for every maxim, if it 
isn't contradictory, there is some (imagined) world where it is universalized. This guarantees that the 
FUL can't be vacuously true, since there is some world where the universalizability test is carried out.\<close>

text \<open>To fix this, I return to the text of @{cite KorsgaardFUL}$\footnote{p. 20}$, in which she describes the universalizability 
test as taking place in an ``imagined" world where the maxim is universalized. In other words, the test
does not require that the maxim is actually universalized in reality in the current universe. Instead, 
we imagine that it is universalized in some parallel universe and study that alternate universe to 
understand what our obligations are in the real world. Under this reading, the maxim should be universalized
at some other world, and then we should decide whether or not it is obligatory at the current world. 

To formalize this, I will first add as an axiom the idea that every non-contradictory maxim is 
universalized at some world. In order for the test to actually be able to find a world where the 
maxim is universalized, we need to imagine that such a world exists. Practically, this axiom asserts
that we are able to successfully imagine a world where the maxim is universalized. Notice that this 
axiom can only hold for non-contradictory maxims, else we would have a world where a contradiction holds 
and the logic would become inconsistent! This coheres with basic moral intuitions as well—asking if 
a contradictory maxim is morally prohibited is, in effect, asking an incoherent question. Garbage in, garbage out!\<close>

abbreviation imagine_a_world::"maxim\<Rightarrow>bool" where 
"imagine_a_world \<equiv> \<lambda>M. (\<exists>w. (\<forall>p. (W M p) w))"
\<comment>\<open>This abbreviation formalizes the idea that, for any maxim, some world where exist where the maxim 
is universally willed.\<close>

abbreviation not_contradictory::"maxim\<Rightarrow>bool" where 
"not_contradictory \<equiv> \<lambda>(c, a, g). (\<forall>p w. \<not> ((c \<^bold>\<and> (a p)) \<^bold>\<rightarrow> \<^bold>\<bottom>) w)"
end