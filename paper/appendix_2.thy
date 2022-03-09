
(*<*) theory appendix_2 imports paper41

begin (*>*)
section \<open>Testing Actions That Are Impossible to Universalize \label{weirdtests}\<close>

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

section \<open>Computational Academic Ethics\<close>
text \<open>
There are two potential sources of the value of academic philosophy: the ethical truths uncovered and 
the process of a philosopher discovering these truths. Under the first view, academic philosophy is 
valuable because it facilitates the discovery of new ethical theories. If truths are valuable and 
computers can generate truths more efficiently than humans, then ethics should be fully automated. 
Ethical disputes often linger unresolved indefinitely, but every now and then, 
a theory emerges as a new classic, such as Rawls’ veil of ignorance. Some academic philosophy also 
impacts social phenomena, like Locke’s impact on global democracy. Academic philosophy often works its 
way into household ethics, as seen in the impact of critical race theory. This view parallels the 
view that ordinary ethics is valuable for its insights alone, and thus
similarly implies that totally automated ethics is not only permissible, but also desirable. If 
ethical truths are important for their impact on society, this value is not contingent on whether a 
human or a computer produced these truths. If possible, computers should produce ethical theories 
to maximize these truths’ value for society. 

Another set of theories locates the value of academic ethics in the process itself and thus requires 
human-computer symbiosis. Just as mathematics is fun and creative for the mathematician, so is ethics 
for the philosopher. Many philosophers enjoy reading and writing philosophy papers. The study of 
philosophy builds critical thinking skills and makes philosophers more reflective. Computational ethics 
doesn’t necessarily sacrifice any of these benefits. These 
benefits would be lost by fully automated ethics, but human-computer symbiotic ethics amplifies them. 
If a computer functions like a tool in the process of philosophical discovery, like a conversation 
with a colleague or a search for counterexamples, then it preserves the joy of philosophy. Moreover, 
computational ethics amplifies this joy by forcing ethicists to make their ideas more precise, a major 
goal of academic philosophy. The rigid syntax of a computer program demands much more precision than a 
conversation or a paper. Computational tools also offer ethicists new perspective by forcing a return to 
first, formal principles often avoided in ordinary philosophical inquiry. Formal ethics has been a 
subject of interest among ethicists, but the logical background necessary has prevented the field 
from taking off. If computers can automate away the tedium of formal ethics, then this precision 
will be accessible to all ethicists, not just logicians. Such work has begun in metaphysics, and 
recent research used computational tools to find an inconsistency in Godel’s ontological argument 
for the existence of God \citep{godelincon}. The power of computational tools to force precision, perform 
consistency checks, and make assumptions explicit means that computers can serve as tools to 
help philosophers perform philosophy better.

If ethical truths offer some value to society at-large, perhaps we cannot sacrifice this value merely 
to preserve human philosophers’ fun. A more compelling argument against fully automated 
ethics is that the existence of human academic philosophers offers value even to non-philosophers. 
People derive joy and wonder from knowing that human beings produced great ethics. Plato’s \emph{Apology} 
is not only a profound and insightful text, but it is also wonderous that a human being produced such 
a work. We derive joy from knowing that our fellow humans are capable of the kind of thought that 
great philosophers accomplish, just as an unimaginably beautiful work of art is more wonderous 
because a human being painted it. We watch the Olympics because we derive wonder and joy from human 
excellence. Even when admiring computational achievements, such as Google’s recent success in protein 
folding, we admire the human who programmed the machine, not the machine itself. We can relate to 
humans, so the mere knowledge that great people are doing great things enriches our lives. This 
knowledge is part of the attraction for the thousands of tourists who visit Harvard Yard every year; 
this is a place where of great human achievement.\footnote{Is this too like, yay Harvard}

An even stronger argument for human-computer symbiotic ethics instead of fully automated ethics is 
that ethics is an inherently human subject. We study ethics because, as argued above, we 
have no choice but to reflect on how to live. Because reflection is such a fundamental part of being 
human, a world in which all ethical inquiry is automated is undesirable. Academic philosophers are 
professional reflectors who are partners in the human experience with us, so their ethical inquiry 
carries unique weight. They teach us, inspire us, and serve as examples of the kind of reflection 
that is constitutive of being human. Moreover, an ethical theory produced entirely by a computer is, 
at best, a secondary perspective; it is a computer’s attempt to describe how human beings should live. 
Without a human component, it cannot serve as a rich and sophisticated guide for humans. If ethics is 
most meaningful when it is the product of human reflection, totally automated ethics destroys the field 
entirely but human-computer symbiosis does not. Human beings should debate the most pressing questions 
of human existence, and computers can serve as our aids. Thus, computational tools must supplement 
human ethical reasoning but cannot replace it.

\<close>


end(*>*)