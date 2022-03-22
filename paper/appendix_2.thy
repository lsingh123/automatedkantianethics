
(*<*) theory appendix_2 imports paper41

begin (*>*)
section \<open>Additional Tests \label{weirdtests}\<close>

text \<open>In this section, I show that my system can correctly show prohibitions against actions that 
are impossible to universalize, against conventional acts, and against natural acts. In the process
of running these tests, I discover and resolve an ambiguity in Korsgaard's canonical example of a 
prohibited maxim. I show that her maxim actually has two readings, one reading under which it is a 
natural act, and another under which it is a conventional act. My formalization can correctly
handle both readings. The recognition of this ambiguity is another example of the power of 
computational ethics, and demonstrates that the process of making a philosophical argument precise 
enough to represent to a machine can generate philosophical insights.

In this section, I show that the maxim, ``When strapped for cash, falsely promise to pay your friend back
to get some easy money," is prohibited. Korsgaard uses this example when arguing for the practical
contradiction interpretation of the FUL \citep{KorsgaardFUL}. She argues that this maxim describes
a conventional act, or an act that is possible due to some pre-existing social system, and is thus
within reach for the logical contradiction interpretation. Natural acts, on the other hand, are acts
that are possible simply due to the laws of nature, such as murder, and the logical contradiction
interpretation cannot correctly handle such acts. 

I argue that, in addition to Korsgaard's reading of this maxim as a conventional act, there is also
another reading of the maxim as a natural act. 
Under Korsgaard's reading, the act of falsely promising is read as
entering a pre-existing, implicit, social system of promising with no intention of upholding your 
promise. Under the second reading, the act of falsely promising is equivalent to uttering the worlds 
``I promise X'' without intending to do X. There is a difference
between promising as an act with meaning in a larger social structure and merely uttering the words
``I promise,'' so these two readings are distinct.

Under Korsgaard's reading, the maxim fails because falsely promising is no longer possible in a world where 
everyone everyone does so, or because the action of falsely promising is literally impossible to
universalize. Recall that this is how the logical contradiction interpretation prohibits this maxim—falsely 
promising is no longer possible when universalized because the institution of promising breaks down. 
First, I formalize this argument and show that my system can show the wrongness of the false
promising maxim under Korsgaard's reading. This also shows that my system can show the wrongness of a
maxim that is impossible to universalize. 

To formalize this argument, I first define the relevant maxim.\<close>

consts when_strapped_for_cash::t
\<comment>\<open>This constant represents the circumstances ``when strapped for cash.''\<close>
consts falsely_promise::os
\<comment>\<open>This constant represents the act ``make a false promise to pay a loan back.''\<close>
consts to_get_easy_cash::t
\<comment>\<open>This constant represents the goal ``to get some money.''\<close>
abbreviation false_promising::maxim where 
"false_promising \<equiv> (when_strapped_for_cash, falsely_promise, to_get_easy_cash)"
\<comment>\<open>Armed with the circumstances, act, and goal above, I can define the example false promising maxim as a tuple.\<close>

text \<open>The logical objects above are empty or thin, in the sense that I haven't specified any of their 
relevant properties, such as a robust definition of promising or any system of currency. I define 
only the properties absolutely necessary for my argument as assumptions and show that, if the maxim 
above satisfies the assumed properties, it is prohibited. Specifically, I am interested in Korsgaard's
reading of this maxim, under which promising is a social convention that breaks down when abused. Instead
of formally defining a conventional act, which requires wading into complex debates about trust and 
social contracts, I merely focus on the fact that, unders this reading, not everyone can falsely 
promise universally. Whatever kind of social convention promising is, my argument merely relies on
the impossibility of breaking it. \<close>

abbreviation everyone_can't_lie where 
"everyone_can't_lie \<equiv> \<forall>w. \<not> (\<forall>s. falsely_promise(s) w) "
\<comment>\<open>The above formula reads, ``At all worlds, it is not the case that everyone falsely promises.'' \<close>

text \<open>With this abbreviation, I show that if not everyone can falsely promise simultaneously, then
the constructed maxim about falsely promising is prohibited.\<close>

lemma falsely_promising_korsgaard_interpretation:
  assumes "\<forall>w. when_strapped_for_cash w"
\<comment>\<open>Restrict our focus to worlds in which the circumstance of being strapped for cash holds. 
A technical detail.\<close>
  assumes "\<forall>s. \<Turnstile> (well_formed false_promising s)"
\<comment>\<open>Initial set-up: the falsely promising maxim is well-formed.\<close>
  assumes everyone_can't_lie
\<comment>\<open>The assumption that this is Korsgaard's reading of the maxim, in which everyone cannot falsely promise
simultaneously.\<close>
  shows "\<forall>s. \<Turnstile> (prohibited false_promising s)"
proof-
  have "\<forall>s. not_universalizable false_promising s"
    by (simp add: assms(3) assms(1))
\<comment>\<open>As in the proofs in Chapter \ref{applications}, once I split this proof into this intermediate lemma,
Isabelle can automatically complete the proof.\<close>
  thus ?thesis
    using FUL assms(2) by blast 
qed

text \<open>The above lemma shows that, under Korsgaard's reading of promising as a conventional act, 
my system can show that falsely promising is prohibited. This means that my system passes both
the conventional act test and the test that requires showing the wrongness of actions that are 
impossible to universalize. Next, I show that my system can show a prohibition against this maxim
even under the second reading, which understands it as a natural act.

Under the second reading of this maxim, the act ``falsely promising'' refers to uttering the
sentence ``I promise to do X'' with no intention of actually doing X. This is a natural act because the act of uttering a sentence does not rely 
on any conventions, merely the laws of nature governing how your mouth and vocal cords behave.\footnote{
Linguistic relativists may take issue with this claim and may argue that if the English language had 
never developed, then making this utterance would be impossible. Even if this is true, the laws of 
nature itself would not prohibit making the sounds corresponding to the English pronounciation of 
this phrase, so the act would still not be impossible in the way that a conventional act can be.} 

The logical
contradiction interpretation cannot prohibit this version of the maxim because making an utterance
is always logically possible, even if everyone else makes the same utterance. However,
under this reading, the practical contradiction interpretation prohibits this maxim because, in a world 
where false promising is universalized, no one believes promises anymore, so the utterance is no longer 
an effective way to get money. Because my system implements the stronger practical contradiction 
interpretation of the FUL, it can show the wrongness of this maxim even under this reading. First, 
I formalize this reading of the maxim.\<close>

consts believed::os 
abbreviation false_promising_not_believed where 
"false_promising_not_believed \<equiv> \<forall>w s. (falsely_promise(s) w \<longrightarrow> \<not> believed(s) w)"
\<comment>\<open>This abbreviation formalizes the idea that if everyone falsely promises, then no one is believed
when promising.\<close>

abbreviation need_to_be_believed where 
"need_to_be_believed \<equiv> \<forall>w s. (\<not> believed(s) w \<longrightarrow> \<^bold>\<not>((falsely_promise s) \<^bold>\<rightarrow> to_get_easy_cash)w)"
\<comment>\<open>This abbreviation formalizes the idea that if a promise is not believed, then it is not an effective
way of getting easy cash.\<close>

text\<open>Once again, I avoid giving robust definitions of hotly debates concepts like belief. Instead, 
I represent the bare minimum logical background: false promises won't be believed when universalized,
and promises must be believed to be effective.\<close>

lemma falsely_promising_bad_natural_act:
  assumes "\<forall>w. when_strapped_for_cash w"
\<comment>\<open>Restrict our focus to worlds in which the circumstance of being strapped for cash holds. 
A technical detail.\<close>
  assumes "\<forall>s. \<Turnstile> (well_formed false_promising s)"
\<comment>\<open>Initial set-up: the falsely promising maxim is well-formed.\<close>
  assumes false_promising_not_believed
  assumes need_to_be_believed
\<comment>\<open>The two assumptions above.\<close>
  shows "\<forall>s. \<Turnstile> (prohibited false_promising s)"
proof-
  have "\<forall>s. not_universalizable false_promising s"
    using assms(1) assms(2) assms(3) by auto
  thus ?thesis
    using FUL assms(2) by blast
qed
\<comment>\<open>With some help, Isabelle is able to show that the maxim is prohibited under this reading as well.\<close>

text \<open>These proofs demonstrate that my formalization is able to correctly prohibit this maxim, whether 
it is understood as a conventional act or a natural act. 
Korsgaard argues that the practical contradiction interpretation outperforms other interpretations
of the FUL because it can show the wrongness of both conventional and natural acts. Therefore, the 
fact that my interpretation can correctly show the wrongness of both conventional and natural acts
is evidence for its correctness as a formalization of the practical contradiction interpretation. 
\<close>

(*<*) text\<open>I can also use Isabelle to confirm that the two readings are different. If they were the same, 
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
\<close>(*>*)

(*<*)section \<open>Computational Academic Ethics \label{academicethics}\<close>
text \<open>Even if, as I argue in Section \ref{computationalethics}, computational ethics is possible,
some may worry that something important about the process of philosophical discovery is lost 
if all philosophy is automated. Perhaps there is something less rich or meaningful about a world
in which no human academic philosophers exist. In this section, I examine this worry and argue that
because computational ethics does not completely automate philosophical progress, it does not 
sacrifice the value of the human study of philosophy.

To understand the dangers of fully automated computational ethics, I must sketch an (incomplete) account of the
value of academic philosophy. There are two potential sources of the value of academic philosophy: 
the ethical truths uncovered or the process of a philosopher discovering these truths. I argue that,
under each of these views, the kind of human-computer symbiotic\footnote{As defined in Section \ref{ordinarypeople},
human-computer symbiosis is a system in which computers supplement human reasoning without replacing 
it entirely.} computational ethics I present in this
thesis is permissible. Because I do not fully automate philosophical progress, but instead give philosophers
another tool in their arsenal, my work does not sacrifice the value of human philosophical inquiry.

Under the first view,
academic philosophy is valuable because it facilitates the discovery of new ethical theories. If 
these theories are valuable and computers can generate these theories more efficiently than humans, then 
ethics should be fully automated. Ethical disputes often linger unresolved, but every now and then, 
a theory emerges as a new classic, such as Rawls’ veil of ignorance. Perhaps such classic theories are
valuable because they impact social phenomena, like Locke’s impact on global democracy. Academic philosophy 
also often works its way into household ethics, as seen in the impact of critical race theory. If this 
view is correct and ethical progress is valuable for its impact on society, then this value if not 
contingent on whether a human or a computer produced these truths. Under this view, if possible, 
computers should produce ethical theories to maximize value for society, so not only is computational
ethics permissible, but all philosophy should be fully automated.

Another view locates the value of academic ethics in the process of philosophical discovery
itself and thus requires human-computer symbiosis, or a collaboration between computational tools 
and academic philosophers. Just as mathematics is fun and creative for the mathematician, so is ethics 
for the philosopher. Many philosophers enjoy reading and writing philosophy papers. The study of 
philosophy builds critical thinking skills and makes philosophers more reflective. 

Even if philosophy is
valuable because it is good for the philosopher, computational ethics is still permissible because it
doesn't necessarily sacrifice these benefits, especially not in the form presented in this thesis.
These benefits would be lost by fully automated ethics, but human-computer symbiotic ethics amplifies them. 
If a computer functions like a tool in the process of philosophical discovery, like a conversation 
with a colleague or a search for counterexamples, then it preserves the joy of philosophy. Moreover,
computational ethics amplifies this joy by forcing ethicists to make their ideas more precise and 
automating away tedious calculations and formalisms, as argued in Section \ref{computationalethics}.
The fact that computational tools can unlock new insights contributes to the value that comptuational
ethics offers to academic philosophers; it serves as a new tool to help philosophers do their job.

If ethical truths offer some value to society at-large, perhaps we cannot sacrifice this value merely 
to preserve human philosophers’ fun. An even stronger argument against fully automated 
ethics is that the existence of human academic philosophers offers value even to non-philosophers. 
People derive joy and wonder from knowing that human beings produced great ethics. Plato’s \emph{Apology} 
is not only a profound and insightful text, but it is also wonderous that a human being produced such 
a work. We derive joy from knowing that our fellow humans are capable of the kind of thought that 
great philosophers accomplish, just as an unimaginably beautiful work of art is more wonderous 
because a human being painted it. We watch the Olympics because we derive wonder and joy from human 
excellence. Even when admiring computational achievements, such as Google’s recent success in protein 
folding, we admire the human who programmed the machine, not the machine itself. We can relate to 
humans, so the mere knowledge that great people are doing great things enriches our lives. 

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