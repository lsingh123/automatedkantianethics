(*<*) theory paper_pretty_2
  imports  paper41

begin(*>*)

section \<open>Applications \label{sec:applications}\<close>

text \<open>In this chapter, I 
demonstrate my system's ability to formalize longer, more complicated ethical arguments and present 
the additional capabilities necessary to use my system in practice. In Chapter 2
and Chapter 3, I performed metaethical reasoning while testing different formalizations of the FUL. Metaethical
reasoning analyzes properties of moral thought itself and involves questions about the nature of ethical
truth. This kind of reasoning contrasts with ``applied 
ethical reasoning," which is the use of ethics to resolve dilemmas and make judgements about 
what an agent should or should not do. Applied ethical reasoning is relevant with respect to an agent's
particular situation, not just to an ethical theory as an abstract entity. In previous chapters' application tests,
I performed some toy examples of applied ethical reasoning, but this chapter is an extended exploration of
my system's ability to perform applied ethical reasoning. Metaethical reasoning is most interesting to philosophers 
who are trying to formulate the ``best" theory of ethics. Applied ethical reasoning, on the other hand, 
is useful to ordinary people who are trying to decide how to live their lives. In order for automated 
ethics to guide AI agents, it must perform applied ethical reasoning. 

One challenge of applied ethical reasoning is that it requires more common sense knowledge than metaethical
reasoning. Because metaethics is about ethics itself, and not about the dilemmas that ethics is 
supposed to help us resolve, this kind of reasoning requires very little knowledge about the world. 
In previous chapters, I perform metaethical reasoning using my system (which formalizes an 
ethical theory) and basic logical facts and objects. Applied ethical reasoning, on the other hand,
focuses on a particular ethical dilemma and thus requires enough 
``common sense" to understand the dilemma and options at hand. For example, an applied ethicist 
evaluating the permissibility of lying needs some robust definition of the term lying and likely some
understanding about the activities of communication and truth telling. Kantians specifically describe
this common sense as ``postulates of rationality" that are nontrivial and nonnormative, but still
part of the process of practical reasoning itself \citep{silber}. \citet{powers} notes that common sense 
is a hurdle for an automated Kantian ethical agent. In this chapter, I attempt to tackle this challenge and
endow my system with this kind of common sense in the specific case of lying. In order for my 
system to be used to perform applied ethical reasoning, it will need to be equipped with a database
of common sense facts and definitions as I present in this chapter. My system will contribute the core
reasoning about the Formula of Universal Law, but this reasoning must be applied to objects that are defined
in this common sense database. In this chapter, I try to understand what this common sense reasoning looks like
for the specific example of lying. 

Because these common sense facts can determine my system's judgements, they are part of the trusted
code base for my system. In order for someone to trust my system's judgements, they must trust that the
common sense database is correct becase changing these common sense facts will change the judgements 
that my system makes. For example, if we define truth telling as an act that is self-contradictory (perhaps
by defining it as $p \wedge \neg p$), then my system will output that truth telling is prohibited.
Malicious common sense facts and definitions will result in bad ethical judgements. In other words, garbage in, 
garbage out. This common sense reasoning is also not a part of the system I contribute here—in order for my
system to be used, future work must develop a common sense database for the particular situation at hand. 
The challenge of endowing automated ethical reasoners with common sense reasoning is not unique to my 
system, and virtually all prior attempts in machine ethics face similar challenges.\footnote{See Section
Related Work for a survey of the common sense required in prior work.} Most prior attempts
sidestep this question, whereas I contribute an prototype implementation of one kind of common sense reasoning.

The specific kind of common sense reasoning required appears to be a challenge 
for automating Kantian ethics, and may imply that consequentialist or virtue ethical automated
agents are within closer reach for automation. Ultimately, Kantian ethics is still
easiest to automate because it will require fewer, less controversial common sense facts than other ethical
systems. As the examples in this section demonstrate, Kantian ethics requires a definition of lying (which any other 
theory would also requires) and the knowledge that if everyone lies in a given context, no one will believe 
each other in that particular context. This latter fact may not be required for every ethical theory, 
but is relatively uncontroversial. It is a kind of intuition about human behavior that is generally accepted. 
Neither a definition of lying nor this property of lying seem like unreasonable prerequisites for ethical reasoning. 

Consequentialism, on the other hand, would require much more specific data about the consequences of 
a lie, perhaps for the specific person's credibility, for the victim of the lie, for the third-parties 
watching the lie unfold. Consequentialism requires more numerous and specific judgements, all of which are 
likely to be more controversial than the two outlined above for Kantian ethics. Similarly, virtue ethics
would likely require information about the actor's entire moral character, including their attitude
towards the lie and their moral history. Virtue ethics would also require robust definitions of the 
relevant virtues, in addition to a definition of lying. Thus, while Kantian ethics requires some 
common sense reasoning, it requires fewer and less controversial background facts than other ethical theories.

The extended examples presented in this section also demonstrate the difficulty of formulating a 
maxim to pass as input to my implementation of the FUL. A large part of the challenge of applied Kantian
ethics is formulating a maxim that accurately captures an agent's principle of action, so a totally
automated agent using my system will need some way to formulate these maxims well. In this section,
I manually implement Korsgaard's formulation of certain maxims, and I will later argue that manual formulation
of maxims is, at present, the way forward. 

This chapter will provide additional examples of the kinds of common sense facts and maxim formulation required to get my system
off the ground. I will aim to use a lean and uncontroversial common sense database
to achieve robust and powerful results. This serves as evidence for the ease of automating
Kantian ethics, an example of what additional work my system requires, and a demonstration of the contributions
that I make. These examples demonstrate that nuanced common sense facts and maxims can cause my system to contribute 
nuanced judgements faithful to philosophical literature. On one hand, this means that my system can perform
sophisticated ethical reasoning, but on the other, the quality of this reasoning is heavily reliant on 
the common sense database and the input maxim. Thus, my system \emph{could} make smart ethical judgements 
in practice, but getting to that point will require a robust, trusted common sense database and maxim
formulator.

In this paper, I contribute an implementation of the Formula of Universal Law that, when equipped with 
relatively thin common sense facts, can performed nuanced, sophisticated ethical reasoning. When given 
as input a maxim in the format specified in Chapter 3, my system can show that the maxim is permissible, 
obligatory, or prohibited. It can provide a verifiable proof of its judgement and a human-readable list
of the facts or axioms it used to reach its conclusion. My system is faithful to philosophical literatire
on Kantian ethics and serves as the first step towards a fully or partially automated ethical AI agent. 
It also establishes the power and potential of computational ethics, or the use of computational tools
for ethical investigation, as explored in this section's Applied Ethical reasoning. 

\emph{Stick a bit here about the philosophical work that will go in this section} \<close>

subsection \<open>Simple Lying Examples \label{sec:lyingprelim}\<close>

text \<open>This chapter focuses on the example of lying because this case is hotly debated in the Kantian
literature. I draw on examples of ethical reasoning as presented in Korsgaard's ``Right to Lie," which 
examines exactly how strict Kant's prohibition on lying is. She picks up a long-running debate in the 
literature through the example of someone who shows up at your door and asks, ``Is Sara home?" Unbeknownst to them, 
you know that they want to know Sara's location in order to murder her. Ordinary moral intuition 
prescribes that, if Sara is home, you should lie and say that she is not in order to 
protect her from the murderer, but the categorical imperative seems to prohibit lying in all 
circumstances. In this section, I will formalize Korsgaard's treatment of lying and joking under the 
categorical imperative, focusing on the common sense assumptions necessary to achieve her conclusions. 
In the next section, I will formalize the core of Korsgaard's argument that the categorical imperative
coheres with ordinary intuition and does not prohibit lying to the murderer to protect Sara.

First, Korsgaard argues that the categorical imperative appears to prohibit all lies because, when universalized, 
lies will no longer be believed. Thus, lying could never be an effective way of achieving any goal when universalized.
Korsgaard points out that ``we believe what is said to us in a given context because most of the time 
people in that context say what they really think" \citep[4]{KorsgaardRTL}. In order to formalize this argument,
I first need to define the relevant terms.\<close>

consts believe::"s\<Rightarrow>t\<Rightarrow>t" ("_ believes _")
\<comment>\<open>Person s::subject believes sentence t::term. The concept of belief will play a crucial role both in 
the arguments for lying being prohibited and for the maxim of lying to the murderer being permissible. 
Logicians and epistemologists have developed robust, complex logics of belief and knowledge \citep{seplogicbelief}. For the 
sake of this project, I avoid this complexity by merely defining the concept of belief as an empty
constant that maps a subject, term pair to a term. For the examples in this section, this choice suffices, 
as my common sense beliefs encode enough properties of belief for my purposes. Future work could
integrate a much more complex logic of belief into my system. \<close>

consts utter::"s\<Rightarrow>t\<Rightarrow>t"
\<comment>\<open>Person s::subject utters sentence t::term.\<close>
abbreviation utter_falsehood::"s\<Rightarrow>t\<Rightarrow>t" where
"utter_falsehood s t \<equiv>  (utter s t) \<^bold>\<and> (\<^bold>\<not> t)"
\<comment>\<open>Person s utters falsehood t if and only if s utters t and t is false. \<close>
abbreviation knowingly_utter_falsehood::"s\<Rightarrow>t\<Rightarrow>t" where
"knowingly_utter_falsehood s t \<equiv> (utter_falsehood s t) \<^bold>\<and> (\<^bold>\<not> (believe s t))"
\<comment>\<open>Person s::subject knowingly utters a falsehood t, if they both utter t as a falsehood and don't
believe t. This and the above abbreviations are the core of my formalization of Korsgaard's definition
of lying. They are also relatively uncontroversial and have little normative content. \<close>

(*<*)
abbreviation implies_os::"os\<Rightarrow>os\<Rightarrow>bool" ("_\<^bold>\<longrightarrow>_") where 
"implies_os a b \<equiv> \<forall>s w. a s w \<longrightarrow> b s w "(*>*)

abbreviation lie::"maxim\<Rightarrow>bool" where 
"lie \<equiv> \<lambda> (c, a, g). \<exists>t. (a \<^bold>\<longrightarrow> (\<lambda>s. knowingly_utter_falsehood s t)) \<and> (\<exists>p. \<forall>w. (g \<^bold>\<rightarrow> (believe p t)) w)"
\<comment>\<open>Using the above definitions, I can characterize a maxim as a lie if 
    (a) the act requires knowingly uttering a falsehood and,
    (b) the end requires that some person $p$ believe the false statement $t$.\<close>

text \<open>To avoid unintentional wrongdoing, I focus on ``knowing lies," 
in which the speaker is aware that they are lying. It is uncontroversial that, in order for an act to be
a knowing lie, the speaker must utter a false statement that they do not believe. The second half of 
this definition requires that the goal of the lie is deception and is inspired by  Korsgaard's interpretation 
of a lie. She understands a lie as a kind of falsehood that is usually effective \emph{because} it decieves
\citep[4]{KorsgaardRTL}. In my formalization, this means that the purpose or goal of the maxim must
involve decieving someone, or, in other words, that someone believe the falsehood told. \<close>

text \<open>With the above logical background, I can now automate Korsgaard's argument that maxims that involve
lying are prohibited. First, I define the subject and maxim at hand.\<close>

consts me::s
\<comment>\<open>I am trying to reason about \emph{my} obligations so I will define myself as a specific subject.\<close>
consts m::maxim
\<comment>\<open>I also define a maxim $m$. My goal is to show that if $m$ is a maxim about lying, then $m$
is prohibited.  \<close>
consts c::t a::os g::t
\<comment>\<open>$m$ will be composed of the circumstances, act, and goal above.\<close>

text \<open>In the following lemma, I use my system to show that lying is prohibited. The assumptions of 
this lemma represent the logical and common sense background necessary to reach this conclusion. This
common sense background is a direct formalization of the premises of Korsgaard's argument. Using these
relatively ``thin" premises about individual behavior, my system can derive a prohibition against lying.  \<close>

lemma lying_prohibited:
  assumes "m \<equiv> (c::t, a::os, g::t)"
  assumes "\<forall>w. \<forall>s. well_formed m s w"
\<comment>\<open>Initial technical set-up: m is a well-formed maxim composed of some circumstances, act, and goal. \<close>
  assumes "lie m"
\<comment>\<open>m is a maxim in which the action requires knowingly uttering a falsehood and the goal requires 
that someone believe this falsehood.\<close>
  assumes "\<forall>t w. ((\<forall>p. utter_falsehood p t w) \<longrightarrow> (\<forall>p. \<^bold>\<not> (believe p t) w))"
\<comment>\<open>The convention of trust assumption that if everyone utters false statement t, then no one will 
believe t. This simple assumption encodes the common sense knowledge that human communication 
involves an implicit trust, and that when this trust erodes, the convention of communication begins 
to break down and people no longer believe each other.\<close>
  assumes "\<forall>w. c w"
\<comment>\<open>Restrict our focus to worlds in which the circumstances hold. A technical detail. \<close>
  shows "\<Turnstile> (prohibited m me)"
proof - 
  have "(\<forall>p w. (W m p) w) \<longrightarrow> (\<Turnstile> (c \<^bold>\<rightarrow> (\<^bold>\<not> g)))"
    by (smt assms(1) assms(2) assms(5) case_prod_beta fst_conv old.prod.exhaust snd_conv)
  have "not_universalizable m me"
    by (metis (mono_tags, lifting) assms(1) assms(2) case_prod_beta fst_conv snd_conv)
  thus ?thesis
    using FUL assms(2) by blast 
qed

text \<open>Now that I have formalized Korsgaard's argument for why lying is prohibited, I will 
implement her argument for why jokes are permissible. Specifically, she defines a joke as a story that is 
false and argues that joking is permissible because ``the universal practice of lying in the context of jokes
does not interfere with the purpose of jokes, which is to amuse and does not depend on
deception" \citep[4]{KorsgaardRTL}. First, I define a joke.\<close>

abbreviation joke::"maxim\<Rightarrow>bool" where 
"joke \<equiv> \<lambda> (c, a, g).  \<exists>t. (a \<^bold>\<longrightarrow> (\<lambda>s. knowingly_utter_falsehood s t)) \<and> \<not> (\<exists>p. \<forall>w. (g \<^bold>\<rightarrow> (believe p t)) w)"

text \<open>This definition of a joke merely defines a joke as a falsehood uttered for some purpose that 
doesn't require deception, where deception involves someone believing the uttered falsehood. Notice 
that this is quite a thin definition of a joke; it doesn't require any conception of humor but merely
distinguishes jokes from lies. As far as common sense reasoning goes, this is a relatively tame proposition. 
I will now demonstrate that this conception of a joke is sufficient to show that joking is permissible.

Korsgaard argues that her above argument for a prohibition against lying also implies that joking is 
permissible, because its purpose is \emph{not} to decieve, but something else entirely. This means that, 
even armed with the same core convention of lying assumption as above, joking must be permissible. The 
lemma below shows exactly that. \<close>

lemma joking_not_prohibited:
  assumes "m \<equiv> (c::t, a::os, g::t)"
  assumes "\<forall>w. \<forall>s. well_formed m s w"
\<comment>\<open>Initial set-up: m is a well-formed maxim composed of some circumstances, act, and goal.\<close>
  assumes "joke m"
\<comment>\<open>m is a maxim about joking. Precisely, it is a maxim in which the action is to knowingly utter a 
falsehood and the goal does not require that someone believe this falsehood.\<close>
  assumes "\<forall>t w. ((\<forall>p. utter_falsehood p t w) \<longrightarrow> (\<forall>p. \<^bold>\<not> (believe p t) w))"
\<comment>\<open>The convention of trust assumption.\<close>
  assumes "\<forall>w. c w"
\<comment>\<open>Restrict our focus to worlds in which the circumstances hold. A technical detail. \<close>
  shows "\<Turnstile> (permissible m me)"
  by (smt assms(1) assms(2) assms(3) case_prod_conv)

text \<open>One potential worry with the above argument is the fact that my definition of joke requires that 
achieving the goal of a joke does not rely on anyone believing the falsehood told in the joke. On its face, 
this is not a complete representation of a joke; the ordinary conception of a joke would be something like 
a false statement uttered with the goal of amusing. I define the goal of the joke as not requiring that 
anyone believe the false statement to distinguish it from lying, which has deception as the goal. I 
intentionally avoid providing robust formalizations of both deception and amusement; instead I present a 
thin conception that relies entirely on the concept of belief. This conception does not require any notion
of humor, satire, intention, or malice, all of which are concepts that may be necessary to define 
amusement and deception completely. 

The fact that my system shows that lies are prohibited and jokes are permissible with these things 
conceptions of amusement and deception shows that my system isolates a necessary and sufficient property 
of a class of maxims that fail the universalizability test. Because my definitions of a lie and joke
only differ in whether or not their goal requires that someone believe the falsehood in question, the
theorems proved in this section show that, in order for a maxim with the act of knowingly uttering a falsehood
to be prohobited, the goal requires that someone believe the falsehood is a necessary and sufficient condition. 
This logical fact derived by my system tracks a fact implicit in Korsgaard's argument and in most Kantian accounts
of lying: the wrongness of lying is derived from the requirement that someone believe the falsehood. 
The logical reality that this property is necessary and sufficient to generate a prohibition reflects
a deep philosohopical explanation of \emph{why} certain maxims about uttering falsehood fail the universalizability
test and why others pass. In simple terms, universalizing uttering a falsehood makes belief in that 
falsehood impossible, so any maxims with goals that require believing in the falsehood will be prohibited.

This account not only describes the kind of maxims that fail or pass the universalizability test, it 
also provides a guide to constructing permissible maxims about uttering falsehoods. As an example, 
consider the idea of throwing a surprise birthday party. At first glance, the maxim of action is 
something like, ``When it is my friend's birthday, I will secretly plan a party so that I can surprise
them." The goal ``so that I can surprise them" clearly requires that your friend believe the falsehood that 
you are not planning a party, else the surprise would be ruined. The analysis above seems to imply that 
Kantian ethics would prohibit surprise parties, which is a sad conclusion for birthday-lovers everywhere. 
Noticing that the problem with this maxim is that the goal requires belief
in a falsehood provides a way to rescue the beloved concept of surprise parties. When throwing a 
surprise party, the ultimate objective is \emph{not} to surprise your friend, but is to celebrate
your friend and help them have a fun birthday. If someone ruins the surprise, but the party is still fun
and the birthday person still feels loved, then we would consider such a party a success! Someone who
called this party a failure clearly would be missing the point of a surprise party. Thus, the goal of 
a surprise party is not the surprise itself, but rather to celebrate the birthday person. Thus modified, 
the goal no longer requires belief in the falsehood and thus passes the universalizability test. 

The implications of this section are twofold. First, my system is capable of performing ethical reasoning
sophisticated enough to show that lying is prohibited but joking is not. The sophistication
necessary to distinguish between lying and joking was a direct consequence of my system's use of a robust
conception of a maxim, which encoded the goal of an act as part of the maxim being evaluated. Second, 
in the process of making this argument precise, my system isolated a necessary and sufficient condition 
of a maxim about uttering a falsehood being prohibited: that the goal require that someone believe
the falsehood. This condition both made an long-standing argument in Kantian ethics more precise
and can guide the correct formulation of future maxims. In other words, an insight generated by the 
computer provides value to ethicists. 

Moreover, all of the reasoning in this chapter required relatively few and uncontroversial common sense facts. The deepest
assumption required was that, if everyone lies about a given statement, no one will believe that 
statement. This assumption is not merely definitional; it does encode some synthetic knowledge about the 
world, but it is relatively uncontroversial. Indeed, it is so well-accepted that Korsgaard does not 
bother to justify it in her argument. These examples showed that, while common sense reasoning 
is an obstacle that must be overcome for my system to be used in practice, it is surmountable.
\<close>

subsection \<open>Lying to a Liar \label{sec:lyingtoliar}\<close>

text \<open>Once Korsgaard completes her preliminary work differentiating between lies and jokes, she begins her main
 argument, which examines the controversial case of the murderer at the door. Recall that the murderer
appears at your door and asks if his intended victim is at home. Ordinary intuition requires that it 
is at the very least permissible (if not obligatory) to lie to the murderer in order to protect the 
victim. Korsgaard notes that a murderer who wishes to find his victim cannot simply announce his
intentions to murder; instead, he must ``must suppose that you do not know who he is and
what he has in mind" \citep[5]{KorsgaardRTL}.\footnote{Korsgaard assumes that the murderer will lie 
about his identity in order to take advantage of your honesty. In footnote 5, she accepts that her 
arguments will not apply in the case of the honest murderer who announces his intentions, so she 
restricts her focus to the case of lying to a liar. She claims that in the case of the honest murderer, the correct act is 
to refuse to respond, but she does not argue for this in this paper.} Thus, she can modify the maxim in 
question to specify that when someone lies to you, you are allowed to lie to them. The maxim of lying 
to the murderer is actually the maxim of lying to a liar, which she argues is permissible. Notice that
her argument hinges on this clever, but ultimately sensical formulation of your maxim. She notes
that there is something relevant and significant about the fact that the person demanding to know Sara's
location is a murderer and that he is trying to take advantage of your honesty. This claim is not
unfounded or wildly controversial, but it does demonstrate the importance of correctly formulating
the maxim to test. In this section, I will formalize her argument for lying to a liar.

As usual, I first define my terms.\<close>

consts murderer::s
\<comment>\<open>This example involves one more subject: the murderer.\<close>
consts not_a_murderer::t
\<comment>\<open>This statement represents the lie that the murderer tells you. By not announcing his
intention, he is implicitly telling you that he is not a murderer, as people normally assume that 
those knocking on their door are not murderers.\<close>
consts when_at_my_door::t
\<comment>\<open>These are the circumstances that the murderer is in.\<close>
consts find_victim::t
\<comment>\<open>This will be the murderer's goal: to find his victim.\<close>
abbreviation murderers_maxim::"maxim" where 
"murderers_maxim \<equiv> (when_at_my_door, \<lambda>s. knowingly_utter_falsehood s not_a_murderer, find_victim)"
\<comment>\<open>Using the above definitions, I can define the murderer's maxim as, ``When at your door, I will knowingly
utter the falsehood that I am not a murderer in order to find my intended victim." Now I will repeat
the same process for your maxim.\<close>

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
knowingly utter the falsehood that his intended victim is not at home in order to protect the victim."\<close>

text \<open>Now that I have defined the maxims at hand, I can begin reasoning about them. First, I will show 
that, using the same convention of lying common sense fact as above, the murderer's maxim is prohibited.
Effectively, this tests that the assumption is indeed strong enough to prohibit lying.\<close>

lemma murderers_maxim_prohibited:
  assumes "\<forall>w. well_formed murderers_maxim murderer w"
\<comment>\<open>Initial set-up: the murderer's maxim is well-formed.\<close>
  assumes "\<Turnstile> (find_victim \<^bold>\<rightarrow> (believe me not_a_murderer))"
\<comment>\<open>Assumption that, in order for the murderer to find their victim, you must not believe that 
he is a murderer.\<close>
  assumes "\<forall>t w. ((\<forall>p. utter_falsehood p t w) \<longrightarrow> (\<forall>p. \<^bold>\<not> (believe p t) w))"
\<comment>\<open>The convention of trust common sense assumption from above.\<close>
  assumes "\<forall>w. when_at_my_door w"
\<comment>\<open>Restrict our focus to worlds in which the circumstance holds. A technical detail. \<close>
  shows "\<Turnstile> (prohibited murderers_maxim murderer)"   
proof - 
  have "(\<forall>p w. (W murderers_maxim p) w) \<longrightarrow> (\<Turnstile> (when_at_my_door \<^bold>\<rightarrow> (\<^bold>\<not> find_victim)))"
    using assms(2) assms(4) by auto
   have "not_universalizable murderers_maxim murderer"
     using assms(2) assms(4) by auto
   thus ?thesis
     using FUL assms(1) by blast
 qed

 text \<open>I will now formalize Korsgaard's argument for the permissibility of lying to a liar. She modifies
the convention of lying assumption above when she argues that, if the murderer believes that you don't 
believe he is a murderer, he will think that you won't lie to him. Precisely, she claims that, 
``it is because the murderer supposes you do not know what circumstances you are in - that is, that 
you do not know you are addressing a murderer - and so does not conclude from the fact that people 
in those circumstances always lie that you will lie" \cite[6]{KorsgaardRTL}. Even though the maxim of 
lying to a murderer is universalized, the murderer thinks that you don't know his true identity. Thus,
even if you have willed this maxim, he thinks that you won't perform the act of lying to the murderer,
since you don't think you're in the relevant circumstances. I formalize this argument below.\<close>

lemma lying_to_murderer_permissible:
  assumes "\<Turnstile> (well_formed murderers_maxim murderer)"
  assumes "\<Turnstile> (well_formed my_maxim me)"
\<comment>\<open>Assume that we're working with well-formed maxims.\<close>
  assumes "\<Turnstile> (protect_victim \<^bold>\<rightarrow> (murderer believes victim_not_home))"
\<comment>\<open>In order for you to protect the victim, the murderer must believe that the victim is not home. \<close>
  assumes "\<forall>sentence::t. \<forall>p1::s. \<forall>p2::s. \<forall>w::i. 
    ((p1 believes (utter_falsehood p2 sentence)) w) \<longrightarrow> (\<not> (p1 believes sentence) w)"
\<comment>\<open>The convention of belief assumption: if person1 believes that person2 utters a sentence as a 
falsehood, then person1 won't believe that sentence.\<close>
  assumes "\<forall>c a g w. (universalized (c, a, g) w) \<longrightarrow> 
            ((person1 believes (person2 believes c)) \<^bold>\<rightarrow> (person1 believes (a person2))) w"
\<comment>\<open>The universalizability assumption: if a maxim is universalized, then if person1 believes person2 
believes they are in the given circumstances, then person1 believes person2 performs the act. \<close>
  assumes "\<forall>w. murderer_at_door w"
\<comment>\<open>Restrict our focus to worlds in which the circumstance holds. A technical detail. \<close>
  shows "\<Turnstile> (permissible my_maxim me)"
  using assms(1) assms(6) by auto
\<comment>\<open>The common sense assumptions given are not strong enough to generate a prohibition against 
lying to a liar, and are thus unused in this proof. \<close>

text \<open>The above lemma shows that, with a more nuanced set of common sense facts, my system can show that 
lying to a liar is permissible. Moreover, I know that this set of assumptions is correct because it 
can also show that the murderer's maxim is prohibited. I show this in the lemma below.\<close>
  
lemma murderers_maxim_prohibited2:
  assumes "\<forall>w. well_formed murderers_maxim murderer w"
\<comment>\<open>The murderer's maxim is a well-formed maxim composed of some circumstances, act, and goal.\<close>
  assumes "\<Turnstile> (find_victim \<^bold>\<rightarrow> (believe me not_a_murderer))"
\<comment>\<open>Assumption that, in order for the murderer to find their victim, you must not believe that they are a murderer.\<close>
  assumes "\<forall>sentence::t. \<forall>p1::s. \<forall>p2::s. \<forall>w::i. ((p1 believes (utter_falsehood p2 sentence)) w) \<longrightarrow> (\<not> (p1 believes sentence) w)"
\<comment>\<open>The convention of belief assumption from above.\<close>
  assumes "\<forall>c a g w. (universalized (c, a, g) w) \<longrightarrow> ((person1 believes (person2 believes c)) \<^bold>\<rightarrow> (person1 believes (a person2))) w"
\<comment>\<open>The convention of willing assumption from above.\<close>
  assumes "\<forall>w. when_at_my_door w"
\<comment>\<open>Restrict our focus to worlds in which the circumstance of the murderer being at my door holds, as 
these are the morally interesting worlds for this example. An irrelevant technical detail. \<close>
  shows "\<Turnstile> (prohibited murderers_maxim murderer)"
proof - 
  have "(\<forall>p w. (W murderers_maxim p) w) \<longrightarrow> (\<Turnstile> (when_at_my_door \<^bold>\<rightarrow> (\<^bold>\<not> find_victim)))"
    using assms(2) by auto
  have "not_universalizable murderers_maxim murderer"
    using assms(2) assms(5) case_prod_beta fst_conv internal_case_prod_def old.prod.case old.prod.exhaust snd_conv by auto
  thus ?thesis
    using FUL assms(1) by blast 
qed

text \<open>This concludes my examination of the maxim of lying to a liar. I was able to show that, by
modifying the common sense facts used, my system can show that lying to a liar is permissible, but lying 
in order to find a victim is not. The assumptions used in this example were a little more robust, but still
ultimately uncontroversial because they were direct consequences of Korsgaard's definition of willing 
and of ordinary definitions of lying. These thin assumptions were sufficient to generate moral conclusions
that Kantian scholars debate robustly. Armed with this common sense, my system generated 
a conclusion that many critics of Kant failed to see.

While it is true that lying to the murderer should be permissible, Korsgaard notes that many will want
to say something stronger, like the fact that lying to the murderer is obligatory in order to protect
the intended victim \citep[15]{KorsgaardRTL}. It seems like we would be doing something wrong if I revealed the victim's
location, knowing that this revelation would cost them their life. Korsgaard solves this problem by 
noting that, while the FUL shows that lying to the murderer permissible, other parts of Kant's ethics
show that it is obligatory. Recall that Kant presents perfect and imperfect duties,
where the former are strict, inviolable, and specific and the latter are broader prescriptions for action.
Perfect duties always supersede imperfect duties when the two conflict.
For example, the duty to not murder is a perfect duty and the duty to give to charity is an imperfect duty. 
The FUL generates perfect duties and Kant's extended theory of virtues generates imperfect duties. The details
of this theory and these distinctions are outside the scope of this paper, but the crucial note is that 
other parts of Kant's ethical theory generate the obligation to lie to the murderer. I chose
to formalize the FUL because it is, in some sense, the strongest of version of the categorical
imperative. An even more sophisticated Kantian reasoner could formalize his theory of virtue and his
other formulatations of the categorical imperative in order to generate the obligation to lie to the murderer, 
but the FUL is the strongest and most foundational of these principles. The fact that my system merely
shows that lying to the murderer is permissible, but not obligatory is consistent with the part of 
Kant's ethical theory that I formalize and demonstrates that I have faithfully implemented the FUL.
\<close>

text \<open>While this example demonstrates the power of my system (when equipped with some common sense), it 
also shows how vital the role of the common sense reasoning is. Slight, intuitive changes in the common
sense facts achieved totally different conclusions about lying. This represents an obstacle to 
fully automated ethical reasoning; such an agent would need a trusted database of common 
sense facts, which is still an unsolved problem. My work is one step towards such an agent, but the 
importance of common sense means that much progress must be made in order to completely automate ethics.

The reasoning of this section also demonstrated one additional place where a Kantian must make vital judgements:
the formulation of the maxim itself. Korsgaard's argument for the permissibility of lying to a 
murderer hinged on a clever formulation of the maxim highlighting a particular facet of the circumstances, 
namely that the murderer is lying to you. Indeed, there is robust debate in the literature on what
circumstances should be considered when formulating a maxim. Some critics of Kant raise the ``tailoring
objection," which is the worry that arbitrarily specific circumstances render any maxim universalizable. For 
example, the maxim ``When my name is Lavanya Singh and I am wearing a purple shirt and it is November 26th, 
I will lie in order to get some easy cash" passes the universalizability test. Even if this maxim is 
willed universally, the circumstances are so specific that lying will not become the general mechanism
for getting easy cash, so the lender will believe my lie and the maxim will remain effective. By tailoring
the circumstances, any maxim can evade universalization.

The Kantian response to this criticism is to require that the circumstances included in the formulation
of the maxim be ``morally relevant." In the example above, my purple shirt and the date clearly have no bearing on 
the moral status of lying. On the other hand, consider the maxim, ``When I am unemployed, I will murder
someone in order to take their job." The circumstances of being unemployed clearly have some bearing on the moral
relevance of the murder in question; they speak to the motivation for the murder. While this view seems 
to track how we actually perform moral reasoning, it leaves open the question of how to determine
which circumstances are morally relevant. Here, O'Niell reminds us that the Formula of Universal Law is 
a ``test of moral worth rather than of outward rightness" \citep[98]{constofreason}. The FUL is a way 
for an agent to decide how they should behave, not for a third-party to judge their behavior. Ethics is 
a personal process for Kant, so the FUL is designed to help agents internally make decisions, not to 
judge others' decisions. Because agents use the FUL to evaluate their own behavior, the test is at its 
best when they make a good faith effort to isolate the \emph{principle} of their action, rather than some
``surface intent" \citep[87]{constofreason}. The FUL is supposed to determine if an agent's principle of action
is universally consistent, so it is at its most effective when an agent accurately formulates the principle
they act on. Circumstances are morally relevant if they accurately reflect the way that the agent is 
thinking about their own action. In the example above, the circumstance of wearing a purple shirt doesn't reflect
the principle of the liar's action. Its inclusion is clearly a disingenous attempt to evade the universalizability
test, but because the FUL is a test of personal integrity, it cannot withstand this kind of mental
gymnastics.

While this account of the formulation of a maxim prescribes how a well-intentioned agent should
decide how to live their life, it poses a challenge for automated ethics. In order for an automated
ethical agent to use the categorical imperative to its fullest extent, the input maxim fed into
my system or any automation of the FUL must be a good-faith attempt to capture the agent's principle
of action. However an action is turned into a maxim for my system to process, whether manually as I do
during these tests or automatically using some kind of input parser, this transformation from action
to maxim has huge bearing on the outcome of the test. The formulation of a maxim must be a good-faith 
attempt to capture the principle of action, and must therefore include only the morally relevant
circumstances, and nothing more. This is a significant judgement that my system does not make, and is 
thus another hurdle that must be overcome in order for my system to be used in practice. I will argue
in Section ?? that this kind of input parsing work should be left to human beings for now, and that
major technical and philosophical progress must be made to automate this portion of the system. 

The formulation of a maxim and the common sense database pose the two greatest challenges to the adoption
of my system in practice. In this chapter, I argued that using manual, human involvement, these challenges
can be overcome in relatively uncontroversial ways. They are also ripe areas for future work.   \<close>

subsection "Philosophical Analysis: Is Automated Ethics a Good Idea?"


(*<*)
text \<open>who do you need to trust?

how is it different from consequentialism if it still requires common sense reasoning?

theory doesn't give guidance on how to make common sense judgements 

only care about universal property 
methodology to classify atoms 

some set of fact axioms that cover some interesting space of things 
obligatory and forbidden things 
how does it compose 
lie and retract

few versions of the fact database
you have an intuition, what do you have to do to make it fit into the theory?

computational ethics and also this is the work you need to do in order to use it in practice 
take a stupid case - axioms that are reasonable and result in bad conclusions 

higher order patterns -> things cancel each other more generally 

prior work -> value 
what is the value? you don't want to
facts can look very similar and one goes to one outcome and one to the other 

FACCT -> send Nada link and think about what to submit 
would it be stronger as a unit 
computational ethics should be a thing 

  \<close>

end
(*>*)
