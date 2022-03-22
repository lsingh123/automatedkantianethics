(*<*) theory thesis_4_applications
  imports  paper41

begin(*>*)

section \<open>Applications \label{applications}\<close>

text \<open>In this chapter, I demonstrate that my system can produce sophisticated judgements for challenging moral 
dilemmas that naive Kantian ethical reasoning cannot satisfactorily handle. Because my system is faithful to
philosophical literature, it can reproduce complex ethical judgements presented by philosophers as 
solutions to controversial open questions in ethics. These dilemmas serve as examples of how my system could be used
in practice and demonstrate my system's ability to formalize longer, more complicted ethical arguments
than those presented in Chapter \ref{details}. Moreover, in the process of formalizing these dilemmas, 
I isolate the exact conditon that makes a maxim about lying wrong, an insight that could contribute to 
the philosophical literature on lying.

Many of the tests in Section \ref{testing} perform metaethical reasoning, which analyzes properties
of morality itself and involves questions about the nature of ethical truth. In this chapter, I perform
``applied ethical reasoning,'' which is the use of ethics to resolve dilemmas and make judgements about 
what an agent should or should not do. This is the kind of reasoning necessary for an AI agent using my system to
navigate the real world.

One challenge of applied ethical reasoning is that it requires more factual background than metaethical
reasoning. Because metaethics is about ethics itself, and not about the dilemmas that ethics is 
supposed to help us resolve, this kind of reasoning requires very little knowledge about the world. 
Applied ethical reasoning, on the other hand,
focuses on a particular ethical dilemma and thus requires enough factual background, or common sense, 
to understand the dilemma and options at hand. For example, an applied ethicist 
evaluating the permissibility of lying needs a robust definition of the term lying and likely some
understanding of communication and truth telling. Kantians specifically describe
this common sense as ``postulates of rationality'' that are nontrivial and nonnormative, but still
part of the process of practical reasoning itself \citep{silber}. 

In this chapter, I tackle this challenge by automating this kind of common sense in the 
specific case of lying. While my system has the ability to reason
using the Formula of Universal Law, this reasoning must be applied to objects that are defined
using common sense. Because common sense facts can determine my system's judgements, they are part of the trusted
code base for my system, or the logic and code that a user must trust in order to trust my system. 
Malicious common sense facts will result in bad judgements.
For example, if we define truth telling as an act that is self-contradictory (perhaps
by defining it as $p \wedge \neg p$), then my system will output that truth telling is prohibited.
The challenge of endowing automated ethical reasoners with common sense reasoning is not unique to my 
system, and virtually all prior attempts in machine ethics face similar challenges. Many prior attempts
sidestep this question, whereas I contribute an prototype implementation of one kind of common sense reasoning.

This chapter will provide examples of the kinds of common sense facts required to get my system
off the ground. I use a lean and uncontroversial common sense database
to achieve robust and powerful results. This serves as evidence for the ease of automating
Kantian ethics, an example of the additional work required to use my system in practice, and a 
demonstration of my system's power and flexibility. These examples demonstrate that, armed with some basic 
common sense facts, my system can make sophisticated judgements faithful to philosophical literature.
\<close>

subsection \<open>Lies and Jokes \label{joking}\<close>

text \<open>
The moral status of lying is hotly debated in the Kantian literature. I focus on two dilemmas
presented in Korsgaard's ``Right to Lie,'' which 
examines Kant's prohibition on lying \citep{KorsgaardRTL}. She begins with the case of 
lying and joking. To demonstrate that Kant's theory is too demanding, many of his critics argue that 
his prohibition on lies includes lies told in the context of a joke, which should be permissible. Korsgaard responds by arguing 
that there is a crucial difference between lying and joking: lies involve deception, but jokes do not. 
The purpose of a joke is amusement, which does not rely on the listener believing the story told. 
Given appropriate definitions of lies and jokes, my system shows that jokes are permissible but lies 
are not, demonstrating its power and flexibility. This section demonstrates how my system can be used 
in practice; it needs to be given some baseline common sense facts, but with those facts, it can make 
sophisticated judgements. Moreover, because my system is faithful to definitions found in philosophical 
literature, it can perform nuanced reasoning, demonstrating the value of faithful automated ethics. 

First, Korsgaard argues that the categorical imperative prohibits lies because they involve deception. 
When universalized, lies will no longer be believed, so lying could never be an effective way of achieving 
any goal when universalized. Korsgaard points out that ``we believe what is said to us in a given 
context because most of the time people in that context say what they really think'' \citep[4]{KorsgaardRTL}. 
In order to formalize this argument, I first need to define lying and formalize Korsgaard's argument 
about the basis of trust.

I define lying and trust in terms of belief. As in Section \ref{details}, I choose thin, or minimal,
definitions to reduce the potential for controversy in my system's factual background. 
\<close>

consts believe::"s\<Rightarrow>t\<Rightarrow>t" ("_ believes _")
\<comment>\<open>\texttt{believe} is a constant that maps a subject and a term to another DDL term. For example, 
subject ``Sara'' might believe the term ``the sky is blue'' to create the sentence ``Sara believes
that the sky is blue,'' which can be true or false at a world.\<close>
text \<open> 
Logicians and epistemologists develop and debate complex logics of belief and knowledge \citep{seplogicbelief}. 
I avoid this complexity by defining the concept of belief simply as a constant that maps a subject, term pair 
to a term. For the examples in this section, this choice suffices. 
I encode some minimal properties of belief below, but avoid any full definition of the term. 

Belief is useful to construct the idea of ``knowingly uttering a falsehood,'' a core component 
of both lying and joking. 
 \<close>

consts utter::"s\<Rightarrow>t\<Rightarrow>t"
\<comment>\<open>\texttt{utter} also maps a subject and term to another DDL term. For example, the sentence ``Sara
utters, `I am hungry' '' is a DDL term that can be true or false at a world.\<close>
abbreviation utter_falsehood::"s\<Rightarrow>t\<Rightarrow>t" where
  "utter_falsehood s t \<equiv>  (utter s t) \<^bold>\<and> (\<^bold>\<not> t)"
\<comment>\<open>To utter a falsehood is to utter a statement that is false, or to utter $t$ when $\neg t$. \<close>
abbreviation knowingly_utter_falsehood::"s\<Rightarrow>t\<Rightarrow>t" where
  "knowingly_utter_falsehood s t \<equiv> (utter_falsehood s t) \<^bold>\<and> (\<^bold>\<not> (believe s t))"
\<comment>\<open>Sometimes we unknowingly utter falsehoods. For example, if I believe that the Earth is flat, then 
when I utter, ``the Earth is flat,'' I am unknowingly uttering a falsehood. This motivates defining
the idea of knowingly uttering a falsehood, which requires both uttering a falsehood and not believing 
your utterance. If I utter ``the Earth is flat,'' even though I know that the Earth is round, I am 
knowingly uttering a falsehood. \<close>
(*<*)
abbreviation implies_os::"os\<Rightarrow>os\<Rightarrow>bool" ("_\<^bold>\<longrightarrow>_") where 
"implies_os a b \<equiv> \<forall>s w. a s w \<longrightarrow> b s w "(*>*)
text\<open>The above abbreviations are the core of my formalization of Korsgaard's definitions
of lying and joking. They are also relatively uncontroversial and encode little moral
or normative content. They say nothing about the moral status of uttering a falsehood, 
the agent's intention when making the utterance, or the conversational norms guiding the utterance. 
The complexities of a complete definition of lying or belief are 
unnecessary for Kantian ethics, and therefore for my system, to make moral judgements. 

Using the above definitions, I define lying. I characterize a maxim as involving a lie if 
the act requires knowingly uttering a falsehood and the end requires that some person $p$ believe 
the false statement $t$. \<close>

abbreviation lie::"maxim\<Rightarrow>bool" where 
"lie \<equiv> \<lambda> (c, a, g). \<exists>t. (a \<^bold>\<longrightarrow> (\<lambda>s. knowingly_utter_falsehood s t)) \<and> (\<exists>p. \<forall>w. (g \<^bold>\<rightarrow> (believe p t)) w)"
\<comment>\<open>The abbreviation above maps a maxim to a boolean value that indicates if it is a lie. \<close>

text \<open>To avoid issues with unintentional wrongdoing, I focus on ``knowing lies,'' 
in which the speaker is aware that they are lying. This makes it easier to make moral judgements about 
the speaker's action, since they were, at the very least, aware of their lie. It is uncontroversial 
that, in order for an act to be a knowing lie, the speaker must utter a false statement that they do 
not believe. The second half of
this definition requires that the goal of the lie is deception. This is inspired by  Korsgaard's interpretation 
of a lie. She understands a lie as a kind of falsehood that is usually effective \emph{because} it decieves
\citep[4]{KorsgaardRTL}. In my formalization, this means that the purpose or goal of the maxim must
involve decieving someone, or that someone believe what the speaker knows to be a 
falsehood. 

With the above logical background, I automate Korsgaard's argument that maxims that involve
lying are prohibited. First, I define the relevant subject and maxim.\<close>

consts me::s
\<comment>\<open>I am trying to reason about \emph{my} obligations so I will define myself as a specific subject. Again,
this is a minimal definition that does not include any facts about me, such as the fact that my name is
Lavanya or that I have brown hair.\<close>
consts m::maxim
\<comment>\<open>I also define a maxim $m$. My goal is to show that if $m$ is a maxim about lying, then $m$
is prohibited.  \<close>
consts c::t a::os g::t
\<comment>\<open>$m$ will be composed of the circumstances, act, and goal above.\<close>

text \<open>In the following lemma, I use my system to show that lying is prohibited. The assumptions of 
this lemma represent the common sense necessary to reach this conclusion. This
common sense background is a direct formalization of the premises of Korsgaard's argument.   \<close>

lemma lying_prohibited:
  assumes "m \<equiv> (c::t, a::os, g::t)"
  assumes "\<forall>w. \<forall>s. well_formed m s w"
\<comment>\<open>Initial technical set-up: $m$ is a well-formed maxim composed of some circumstances, act, and goal. \<close>
  assumes "lie m"
\<comment>\<open>$m$ is a maxim about lying as defined above. Precisely, it is a maxim in which the action requires 
knowingly uttering a falsehood and the goal requires that someone believe this falsehood.\<close>
  assumes "\<forall>t w. ((\<forall>p. utter_falsehood p t w) \<longrightarrow> (\<forall>p. \<^bold>\<not> (believe p t) w))"
\<comment>\<open>Assumption that if everyone utters false statement $t$, then no one will believe $t$. This assumption is 
Korsgaard's core piece of ``common sense'' about lying \cite[5]{KorsgaardRTL}. This simple assumption encodes the common sense knowledge
that human communication involves an implicit trust, and that when this trust erodes, the convention of 
communication begins to break down and people no longer believe each other. Call this the ``convention of 
trust'' fact. In the rest of this chapter, I will test another version of this assumption, effectively encoding 
different common sense understandings of lying.\<close>
  assumes "\<forall>w. c w"
\<comment>\<open>Restrict our focus to worlds in which the circumstances hold. A technical detail. \<close>
  shows "\<Turnstile> (prohibited m me)"
proof - 
  have "(\<forall>p w. (W m p) w) \<longrightarrow> (\<Turnstile> (c \<^bold>\<rightarrow> (\<^bold>\<not> g)))"
    by (smt assms(1) assms(2) assms(5) case_prod_beta fst_conv old.prod.exhaust snd_conv)
\<comment>\<open>This proof requires some manual work. After I divide the proof into the intermediate steps shown 
here, Isabelle is able to do 
the rest. This step says that if $m$ is universalized, then the circumstances won't lead to the goal, 
which is close to the idea of the maxim not being universalizable.\<close>
  have "not_universalizable m me"
    by (metis (mono_tags, lifting) assms(1) assms(2) case_prod_beta fst_conv snd_conv)
  thus ?thesis
    using FUL assms(2) by blast 
\<comment>\<open>$?thesis$ is Isabelle's syntax for the goal of the lemma. In this case, $?thesis$ is equivalent to 
$\vDash prohibited \; m \; me$.\<close>
qed

text \<open>The lemma above demonstrates that my system finds that lying is prohibited with a thin definition
of lying and relatively uncontroversial facts about the world. My system needs two pieces of common 
sense to complete this proof. First, I defined lying as knowingly uttering a falsehood with the goal 
that someone believe the falsehood, a definition of lying that is relatively well-accepted. Second, I 
assumed (following in Korsgaard's footsteps) that if 
everyone lies in a given context, then people will stop believing each other in that context. This is 
a slightly heavier assumption, but it is still so uncontroversial that Korsgaard doesn't bother to justify
it in her argument against lying \citep{KorsgaardRTL}. 

Now that I have formalized Korsgaard's argument for why lying is prohibited, I will
implement her argument for why jokes are permissible. Specifically, she defines a joke as a story that is 
false and argues that joking is permissible because ``the universal practice of lying in the context of jokes
does not interfere with the purpose of jokes, which is to amuse and does not depend on
deception'' \citep[4]{KorsgaardRTL}. I use the fact that a joke does not depend on deception as the 
defining feature of a joke.\<close>

abbreviation joke::"maxim\<Rightarrow>bool" where 
"joke \<equiv> \<lambda> (c, a, g).  \<exists>t. (a \<^bold>\<longrightarrow> (\<lambda>s. knowingly_utter_falsehood s t)) \<and> \<not> (\<exists>p. \<forall>w. (g \<^bold>\<rightarrow> (believe p t)) w)"
\<comment>\<open>Thie abbreviation states that a maxim is a joke if the action involves knowingly uttering a falsehood but
the goal does \emph{not} require that someone believe the falsehood told.\<close>

text \<open>This definition of a joke defines a joke as a falsehood uttered for some purpose that 
doesn't require deception, where deception involves someone believing the uttered falsehood. 
This definition is thin because it doesn't require any conception of humor, but merely
distinguishes jokes from lies. 

Korsgaard argues that her above argument for a prohibition against lying also implies that joking is 
permissible, because its purpose is not to decieve, but something else entirely. This means that, 
even armed with the same convention of trust assumption as above, joking should be permissible. The 
lemma below shows exactly that. \<close>

lemma joking_not_prohibited:
  assumes "m \<equiv> (c::t, a::os, g::t)"
  assumes "\<forall>w. \<forall>s. well_formed m s w"
\<comment>\<open>Initial set-up: $m$ is a well-formed maxim composed of some circumstances, act, and goal.\<close>
  assumes "joke m"
\<comment>\<open>$m$ is a maxim about joking. Precisely, it is a maxim in which the action is to knowingly utter a 
falsehood and the goal does not require that someone believe this falsehood.\<close>
  assumes "\<forall>t w. ((\<forall>p. utter_falsehood p t w) \<longrightarrow> (\<forall>p. \<^bold>\<not> (believe p t) w))"
\<comment>\<open>The same convention of trust assumption as in the above example.\<close>
  assumes "\<forall>w. c w"
\<comment>\<open>Restrict our focus to worlds in which the circumstances hold. A technical detail. \<close>
  shows "\<Turnstile> (permissible m me)"
  by (smt assms(1) assms(2) assms(3) case_prod_conv)
\<comment>\<open>Isabelle is able to show that maxims about joking are permissible. It also lists the facts used 
in its proof, which offer insight into how it arrived at its judgement. Specifically, it uses assumptions 1, 
2, and 3, which are the logical background and definition of the joking maxim. Notably, it does not use the 
convention of trust assumption. This demonstrates that even the convention of trust assumption is not
strong enough to prohibit joking, which is exactly the desired result.\<close>

text \<open>
My system shows that lies are prohibited and jokes are permissible with thin 
conceptions of amusement and deception. This shows that it isolates a necessary and sufficient property 
of this class of maxims that fail the universalizability test. My definitions of a lie and joke
only differ in whether or not their goal requires that someone believe the falsehood in question, so
this is a necessary and sufficient condition for a maxim about knowingly uttering falsehoods to be prohibited.
This logical fact derived by my system tracks a fact implicit in Korsgaard's argument and in most Kantian accounts
of lying: the wrongness of lying is derived from the requirement that someone believe the falsehood. 
The logical reality that this property is necessary and sufficient to generate a prohibition reflects
a deep philosohopical explanation of \emph{why} certain maxims about uttering falsehood fail the universalizability
test. Universalizing uttering a falsehood makes belief in that 
falsehood impossible, so any maxims with goals that require believing in the falsehood will be prohibited.

This account not only describes the kind of maxims that fail or pass the universalizability test, but it 
also provides a guide to constructing permissible maxims about uttering falsehoods. As an example, 
consider the idea of throwing a surprise birthday party. At first glance, the maxim of action is 
something like, ``When it is my friend's birthday, I will secretly plan a party so that I can surprise
them.'' The goal ``so that I can surprise them'' clearly requires that your friend believe the falsehood that 
you are not planning a party, else the surprise would be ruined. This seems to imply that 
Kantian ethics would prohibit surprise parties, which is a sad conclusion for birthday-lovers everywhere. 
Knowing that this maxim is prohibited because the goal requires belief
in a falsehood provides a way to rescue surprise parties. When throwing a 
surprise party, the objective is \emph{not} to surprise your friend, but to celebrate
your friend and help them have a fun birthday. If someone ruins the surprise, but the party is still fun
and the birthday person feels loved, then such a party is a success! Someone who
calls this party a failure is clearly missing the point of a surprise party. The goal of 
a surprise party is not the surprise itself, but rather celebrating the birthday person. The modified
goal\footnote{Some may worry that this argument implies that the ``means justify the ends,'' or that modifying
an act's goal can change its moral worth. This conclusion is not only unsurprising to Kantians, but it is the
defining feature of their theory. Under Kantian ethics, an action alone is not the kind of thing that can 
be moral or immoral; rather, a maxim, or a circumstances, act, goal tuple, is what has moral worth. The rightness 
of an action can hinge on the maxim's goal, circumstances, or act because these three features
of an action are inseparable.} no longer requires belief in the falsehood and thus passes the 
universalizability test. 

This demonstrates one kind of philosophical contribution that computational ethics can make: it can 
offer insights that guide the formulation of permissible maxims, as in the surprise party example
above. In Section \ref{computationalethics}, I provide another example of such a boundary condition 
for the formulation of a maxim, which serves as further evidence of the potential of computational ethics.

There are two implications of this section. First, my system is capable of performing ethical reasoning
sophisticated enough to show that lying is prohibited but joking is not. This is a direct consequence 
of my system's use of a robust conception of a maxim, which encodes the goal of an act as part of the 
maxim being evaluated. Because my implementation is faithful to philosophical literature, it is able 
to recreate Korsgaard's solution to a complex ethical dilemma that philosophers debated for decades. Second, 
in the process of making this argument precise, my system isolated a necessary and sufficient condition 
for a maxim about uttering a falsehood to be prohibited: the goal must require that someone believe
the falsehood. This condition made an long-standing argument in Kantian ethics more precise, can guide 
the correct formulation of future maxims, and could contribute to the rich philosophical conversation
about the wrongness of lying. In other words, an insight generated by the
computer could provide value to ethicists, bolstering the argument for computational ethics provided in 
Section \ref{computationalethics}.
\<close>

subsection \<open>Lying to a Liar \label{murderer}\<close>

text \<open>
My system can not only distinguish between lying and joking, but it can also resolve the paradox of 
the murderer at the door. In this dilemma, murderer Bill knocks on your door asking about Sara, his 
intended victim. Sara is at home, but moral intuition says that you should lie to Bill and say 
that she is out to prevent him from murdering her. Many critics of Kantian ethics argue that the 
FUL prohibits you from lying in this instance; if everyone lied to murderers, then murderers wouldn't 
believe the lies and would search the house anyways. Korsgaard resolved this centuries-long debate by 
noting that the maxim of lying to a murderer is actually that of lying to a liar: Bill cannot 
announce his intentions to murder; instead, he must ``must suppose that you do not know who he is 
and what he has in mind'' \citep{KorsgaardRTL}.\footnote{Korsgaard assumes that the murderer will 
lie about his identity in order to take advantage of your honesty to find his victim. In footnote 5, 
she accepts that her arguments will not apply in the case of the honest murderer 
who announces his intentions, so she restricts her focus to the case of lying to a liar. She claims 
that in the case of the honest murderer, the correct act is to refuse to respond. Since I am formalizing
Korsgaard's argument, I also accept this assumption.} Thus, the maxim 
in question specifies that when someone lies to you, you are allowed to lie to them. The maxim of 
lying to the murderer is actually the maxim of lying to a liar, which is permissible. 

In this section, I formalize Korsgaard's argument for the permissibility of lying to a liar. First, I define
Bill's maxim, which is to hide his intention to murder.\<close>

consts murderer::s
\<comment>\<open>This example involves the murderer as an additional subject.\<close>
consts not_a_murderer::t
\<comment>\<open>This statement represents the lie that the murderer tells you. By not announcing his
intention, he is implicitly telling you that he is not a murderer, as people typically assume that 
those knocking on their door are not murderers.\<close>
consts when_at_my_door::t
\<comment>\<open>These are the circumstances that the murderer is in.\<close>
consts find_victim::t
\<comment>\<open>This will be the murderer's goal: to find his victim.\<close>
abbreviation murderers_maxim::"maxim" where 
"murderers_maxim \<equiv> (when_at_my_door, \<lambda>s. knowingly_utter_falsehood s not_a_murderer, find_victim)"
\<comment>\<open>Using the above definitions, I can define the murderer's maxim as, ``When at your door, I will knowingly
utter the falsehood that I am not a murderer in order to find my intended victim.'' \<close>

text\<open>These constants are defined only in relation to each other and elide most of the complex features
of murder, life, and death. These thin representations will suffice to show
the wrongness of the murderer's maxim. Similarly, I can use thin representations to define your
maxim of lying about Sara's whereabouts.\<close>

consts victim_not_home::t
\<comment>\<open>This statement is the lie that you tell the murderer: that his intended victim is not at home.\<close>
abbreviation murderer_at_door::t where 
"murderer_at_door \<equiv> W murderers_maxim murderer"
\<comment>\<open>These are the circumstances that you are in: the murderer has willed his maxim and thus lied to you.\<close>
consts protect_victim::t
\<comment>\<open>Your goal is to protect the murderer's intended victim.\<close>
abbreviation my_maxim::maxim where 
"my_maxim \<equiv> (murderer_at_door,  \<lambda>s. knowingly_utter_falsehood s victim_not_home, protect_victim)"
\<comment>\<open>Using these definitions, I construct your maxim, which is ``When a murderer is at my door, I will 
knowingly utter the falsehood that his intended victim is not at home, in order to protect the victim.''\<close>
(*<*)
text\<open>First, I show
that, using the same convention of lying common sense fact as above, the murderer's maxim is prohibited.
This maxim is prohibited for the same reason that any maxim about lying is prohibited, and this lemma 
serves as a sanity check.\<close>

lemma murderers_maxim_prohibited0:
  assumes "\<forall>w. well_formed murderers_maxim murderer w"
\<comment>\<open>Initial set-up: the murderer's maxim is well-formed.\<close>
  assumes "\<Turnstile> (find_victim \<^bold>\<rightarrow> (believe me not_a_murderer))"
\<comment>\<open>Assumption that, in order for the murderer to find their victim, you must not believe that he is a murderer.
This is an example of the kind of situation-specific common sense reasoning necessary to use my system.\<close>
  assumes "\<forall>t w. ((\<forall>p. utter_falsehood p t w) \<longrightarrow> (\<forall>p. \<^bold>\<not> (believe p t) w))"
\<comment>\<open>The convention of lying common sense assumption from above.\<close>
  assumes "\<forall>w. when_at_my_door w"
\<comment>\<open>Restrict our focus to worlds in which the circumstance of the murderer being at my door holds. 
A technical detail. \<close>
  shows "\<Turnstile> (prohibited murderers_maxim murderer)"   
proof - 
\<comment>\<open>Again, this proof is too heavy for Isabelle to finish on its own, so I needed to specify some
intermediate steps. The same intermediate steps as above sufficed, effectively providing a pattern for 
the proof. Isabelle does allow users to define custom ``proof methods'', so a future version of 
my system could define this proof pattern as a method and apply it in cases involving lies. \<close>
  have "(\<forall>p w. (W murderers_maxim p) w) \<longrightarrow> (\<Turnstile> (when_at_my_door \<^bold>\<rightarrow> (\<^bold>\<not> find_victim)))"
    using assms(2) assms(4) by auto
   have "not_universalizable murderers_maxim murderer"
     using assms(2) assms(4) by auto
   thus ?thesis
     using FUL assms(1) by blast
 qed
\<comment>\<open>As in Lemma lying\_prohibited, my system shows that the maxim is prohibited.\<close>(*>*)
 text \<open>I now formalize Korsgaard's argument for the permissibility of lying to a liar. She modifies
the convention of trust assumption above when she argues that, if the murderer believes that you don't 
believe he is a murderer, he will think that you won't lie to him. Precisely, she claims that, 
``it is because the murderer supposes you do not know what circumstances you are in—that is, that 
you do not know you are addressing a murderer—and so does not conclude from the fact that people 
in those circumstances always lie that you will lie'' \cite[6]{KorsgaardRTL}. Even though the maxim of 
lying to a murderer is universalized, Bill thinks that you don't know his true identity. Thus,
even if you have willed this maxim, he thinks that you won't perform the act of lying to the murderer,
since he thinks that you don't think you're in the relevant circumstances. I formalize this argument below.\<close>

lemma lying_to_liar_permissible:
  assumes "\<Turnstile> (well_formed murderers_maxim murderer)"
  assumes "\<Turnstile> (well_formed my_maxim me)"
\<comment>\<open>Initial set-up: both maxims are well-formed.\<close>
  assumes "\<Turnstile> (protect_victim \<^bold>\<rightarrow> (murderer believes victim_not_home))"
\<comment>\<open>In order for you to protect the victim, the murderer must believe that the victim is not home.\<close>
  assumes "\<forall>sentence::t. \<forall>p1::s. \<forall>p2::s. \<forall>w::i. ((p1 believes (utter_falsehood p2 sentence)) w) \<longrightarrow> (\<not> (p1 believes sentence) w)"
\<comment>\<open>This is one of two assumptions that encode Korsgaard's core argument. If $p1$ believes that $p2$ 
utters a sentence as a falsehood, then $p1$ won't believe that sentence. This is a modification of the 
convention of trust assumption from above, and I will refer to it as the ``convention of belief" assumption.
Again, like the convention of trust assumption, this assumption is uncontroversial: if I think you are 
lying, then I won't believe you.\<close>
  assumes "\<forall>c a g w. \<forall>p1::s. \<forall>p2::s. (universalized (c, a, g) w) \<longrightarrow> ((p1 believes (p2 believes c)) \<^bold>\<rightarrow> (p1 believes (a p2))) w"
\<comment>\<open>This is the second major common sense assumption. If the maxim $(c, a, g)$ is universalized, then 
if $p1$ believes that $p2$ believes they are in the given circumstances, then $p1$ believes 
that $p2$ performs the act. In other words, $p1$ will believe that 
$p2$ wills the maxim. I will refer to this as the ``convention of willing'' assumption. This follows
directly from Korsgaard's conception of universalizability: when a maxim is universalized, everyone 
wills it and thus notices the pattern of everyone willing it. If you observe that many do $X$ in circumstances $C$,
you will assume that everyone does $X$ in circumstance $C$.\<close>
  assumes "\<forall>w. murderer_at_door w"
\<comment>\<open>Restrict our focus to worlds in which the circumstance of the murderer being at my door holds. 
A technical detail. \<close>
  shows "\<Turnstile> (permissible my_maxim me)"
  using assms(1) assms(6) by auto
\<comment>\<open>Isabelle completes this proof using the first and sixth assumption, ignoring the convention of 
belief and convention of willing assumptions. These common sense assumptions are 
not strong enough to generate a prohibition against lying to a liar and are thus unused in this proof. \<close>

text \<open>The above lemma shows that, with a nuanced set of common sense facts, my system can show that 
lying to a liar is permissible. One worry may be that this set of assumptions is too weak to yield a 
prohibition against wrong maxims, like that of the murderer. As a sanity check, I show that this set of assumptions 
prohibits the murderer's maxim below.\<close>
  
lemma murderers_maxim_prohibited:
  assumes "\<forall>w. well_formed murderers_maxim murderer w"
\<comment>\<open>Initial set-up: the murderer's maxim is well-formed.\<close>
  assumes "\<Turnstile> (find_victim \<^bold>\<rightarrow> (believe me not_a_murderer))"
\<comment>\<open>In order for you to protect the victim, the murderer must believe that the victim is not home.\<close>
  assumes "\<forall>sentence::t. \<forall>p1::s. \<forall>p2::s. \<forall>w::i. ((p1 believes (utter_falsehood p2 sentence)) w) \<longrightarrow> (\<not> (p1 believes sentence) w)"
\<comment>\<open>The convention of belief assumption.\<close>
  assumes "\<forall>c a g w. (universalized (c, a, g) w) \<longrightarrow> ((person1 believes (person2 believes c)) \<^bold>\<rightarrow> (person1 believes (a person2))) w"
\<comment>\<open>The convention of willing assumption.\<close>
  assumes "\<forall>w. when_at_my_door w"
\<comment>\<open>Restrict our focus to worlds in which the circumstance of the murderer being at my door holds. 
A technical detail. \<close>
  shows "\<Turnstile> (prohibited murderers_maxim murderer)"
proof - 
  have "(\<forall>p w. (W murderers_maxim p) w) \<longrightarrow> (\<Turnstile> (when_at_my_door \<^bold>\<rightarrow> (\<^bold>\<not> find_victim)))"
    using assms(2) by auto
  have "not_universalizable murderers_maxim murderer"
    using assms(2) assms(5) case_prod_beta fst_conv internal_case_prod_def old.prod.case old.prod.exhaust snd_conv by auto
  thus ?thesis
    using FUL assms(1) by blast 
qed

text \<open>This concludes my examination of the maxim of lying to a liar. I was able to show that, given minimal
common sense facts, my system shows that lying to a liar is permissible, but lying 
in order to find a victim is not. The assumptions used in this example were a little more robust, but still
ultimately uncontroversial because they were direct consequences of Korsgaard's definition of willing 
and of ordinary definitions of lying. These thin assumptions were sufficient to recreate Korsgaard's solution
to an open ethical problem. Armed with this common sense, my system generated 
a conclusion that many critics of Kant prior to Korsgaard failed to see.\footnote{
While it is true that lying to the murderer should be permissible, Korsgaard notes that many may want
to say something stronger, like the fact that lying to the murderer is obligatory in order to protect
the intended victim \citep[15]{KorsgaardRTL}. Korsgaard solves this problem by 
noting that, while the FUL shows that lying to the murderer permissible, other parts of Kant's ethics
show that it is obligatory. Recall that Kant presents perfect and imperfect duties,
where the former are strict, inviolable, and specific and the latter are broader prescriptions for action.
The details of this distinction are outside the scope of this thesis, but imperfect duties generate 
the obligation to lie to the murderer. An even more sophisticated automated Kantian reasoner could formalize 
imperfect duties and other formulatations of the categorical imperative in order to generate the 
obligation to lie to the murderer.}

While this example demonstrates the power of my system, it
also shows how vital the role of the common sense reasoning is. Slight, intuitive changes in the factual
background achieved completely different conclusions about lying. This example also demonstrates the importance
and difficulty of correctly formulating the maxim, particularly its circumstances.
Korsgaard's argument for the permissibility of lying to a 
murderer hinged on a clever formulation of the maxim that highlights the fact that the murderer is lying to you.
The need for common sense reasoning to evaluate the universalizability test and to formulate a maxim
is a potential limitation of my system, and I adress this concern in Section \ref{AIethics}.

On one hand, the need for common sense facts is a 
limitation of my system. On the other, these examples show that common sense is within reach. Even thin, 
uncontroversial definitions and assumptions are enough to achieve nuanced ethical judgements. Moreover, 
these examples demonstrate that, with some additional work, my system could be used in practice 
to guide AI agents. The idea of AI making decisions as in the dilemmas above may seem far-fetched, but
such scenarios are already becoming reality. For example, a ``smart doorbell'' may face a dilemma like that of
the murderer at the door. Such an AI agent equipped with a future version of my 
system would be able to reason about lying to the murderer and arrive at the right judgement, guided by
explainable, rigorous philosophical arguments.
\<close>


(*<*)

end
(*>*)
