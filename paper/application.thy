(*<*) theory application
  imports  paper41

begin(*>*)

section \<open>Applications \label{sec:applications}\<close>

text \<open>In this section, I will demonstrate possible applications of my formalization of the FUL. I 
will present two kinds of applications. First, I will formalize a classical ethical dilemma in 
Kantian literature, the case of the murderer at the door. This will demonstrate the utility of computational
ethics in helping philosophers think about ethical dilemmas. Second, I will encode some ``common sense"
facts into the system and then test the results of applying this more powerful system to common
ethical dilemmas. This section will serve as a prototype of the kind of reasoning that this kind of 
computational ethics can do and will demonstrate the utility of computational ethics in performing 
everyday ethical reasoning. This section will also outline what future work is necessary to use an 
ethical reasoner like the one I build in practice. Finally, I will also philosophically analyze the possibility and value of 
applications like these. Specifically, I will consider to what extent humans should let computers do 
ethical reasoning on our behalf. \<close>

subsection \<open>Preliminary Lying Work \label{sec:lyingprelim}\<close>

text \<open>In this section, I draw on examples of ethical reasoning as presented in Korsgaard's right to lie.
She analyzes the example of someone who shows up at your door and asks, "Is Sara home?" Unbeknownst to them, 
you know that they want to know Sara's location in order to murder her. Ordinary moral intuition seems
to imply that in this situation, if Sara is home, you should lie and say that she is not in order to 
protect her from the murderer. However, the categorical imperative seems to prohibit lying in all 
circumstances. More specifically, when universalized, lies will no longer be believed, so it seems 
like lying could never be an effective way of achieving any goal when universalized. Korsgaard points out
that ``we believe what is said to us in a given context because most of the time people in that context 
say what they really think" \citep[4]{KorsgaardRTL}. First, I will formalize this argument.

The first step in formalizing this argument is defining the relevant terms.\<close>

consts believe::"s\<Rightarrow>t\<Rightarrow>t"
\<comment>\<open>Person s::subject believes sentence t::term\<close>
consts utter::"s\<Rightarrow>t\<Rightarrow>t"
\<comment>\<open>Person s::subject utters sentence t::term\<close>
abbreviation utter_falsehood::"s\<Rightarrow>t\<Rightarrow>t" where
"utter_falsehood s t \<equiv>  (utter s t) \<^bold>\<and> (\<^bold>\<not> t)"
abbreviation knowingly_utter_falsehood::"s\<Rightarrow>t\<Rightarrow>t" where
"knowingly_utter_falsehood s t \<equiv> (utter_falsehood s t) \<^bold>\<and> (\<^bold>\<not> (believe s t))"
\<comment>\<open>Person s::subject utters a falsehood t::term if they utter t and t is false.\<close>

(*<*)
abbreviation implies_os::"os\<Rightarrow>os\<Rightarrow>bool" ("_\<^bold>\<longrightarrow>_") where 
"implies_os a b \<equiv> \<forall>s w. a s w \<longrightarrow> b s w "(*>*)

abbreviation lie::"maxim\<Rightarrow>bool" where 
"lie \<equiv> \<lambda> (c, a, g). \<exists>t. (a \<^bold>\<longrightarrow> (\<lambda>s. knowingly_utter_falsehood s t)) \<and> (\<exists>p. \<forall>w. (g \<^bold>\<rightarrow> believe p t) w)"
\<comment>\<open>A maxim is a lie if 
    (a) the act requires knowingly uttering a falsehood 
    (b) the end requires that some person $p$ believe the false statement $t$\<close>

text \<open>To avoid focus on the case of conscious, intentional wrongdoing, I focus on ``knowing lies," 
in which the speaker is aware that they are lying. It is uncontroversial that an act is a knowing lie
if the speaker utters a false statement that they do not believe. The second half of this definition, which 
requires that the goal of the action of lying be to decieve, is inspired by  Korsgaard's interpretation 
of a lie, which understands a lie as a kind of falsehood that is usually effective \emph{because} it decieves
\citep[4]{KorsgaardRTL}. \<close>

text \<open>With the above logical background, I can now show that maxims that involve lying are prohibited.
First, I define the subject and maxim at hand.\<close>

consts me::s
\<comment>\<open>I am trying to reason about my obligations so I will define myself as a specific subject.\<close>
consts m::maxim
\<comment>\<open>I will also define a maxim $m$. My goal is to show that if $m$ is a maxim about lying, then $m$
is prohibited.\<close>

text \<open>The following lemma shows the common sense necessary to determine that lying is prohibited. \<close>

lemma lying_prohibited:
  fixes c
  fixes a
  fixes g
  assumes "m \<equiv> (c::t, a::os, g::t)"
  assumes "\<forall>w. \<forall>s. well_formed m s w"
\<comment>\<open>Initial set-up, m is a well-formed maxim composed of some circumstances, act, and goal.\<close>
  assumes "lie m"
\<comment>\<open>$m$ is a maxim about lying. Precisely, it is a maxim in which the action is to knowingly utter a 
falsehood and the goal requires that someone believe this falsehood.\<close>
  assumes "\<forall>t w. ((\<forall>p. utter_falsehood p t w) \<longrightarrow> (\<forall>p. \<^bold>\<not> (believe p t) w))"
\<comment>\<open>Assumption that if everyone utters false statement t, then no one will believe t.\<close>
  assumes "\<forall>w. c w"
\<comment>\<open>Restrict our focus to worlds in which the circumstances hold, as these are the morally interesting 
worlds for this example. Basically an irrelevant technical detail. \<close>
  shows "\<Turnstile> (prohibited m me)"
proof - 
  have "(\<forall>p w. (W m p) w) \<longrightarrow> (\<Turnstile> (c \<^bold>\<rightarrow> (\<^bold>\<not> g)))"
    by (smt assms(1) assms(2) assms(5) case_prod_beta fst_conv old.prod.exhaust snd_conv)
\<comment>\<open>Unlike many of the other proofs in this project, this proof was a little heavier and required some manual
work to produce. I divided the proof into the intermediate steps shown here, and Isabelle was able to do 
the rest! This step says that if $m$ is universalized, then the circumstances won't lead to the goal, 
which is quite close to the idea of the maxim not being universalizable.\<close>
  have "not_universalizable m me"
    by (metis (mono_tags, lifting) assms(1) assms(2) case_prod_beta fst_conv snd_conv)
  thus ?thesis
    using FUL assms(2) by blast 
qed

text \<open>The above is an example of how my system can perform ``applied ethical reasoning." In Chapter 2
and Chapter 3, I performed metaethical reasoning while testing different formalizations of the FUL. Metaethical
reasoning analyzes properties of moral thought itself \citep{sepme}. Because metaethics is about ethics itself,
and not about the actual dilemmas that ethics is supposed to help us resolve, this kind of reasoning requires
very little additional knowledge beyond that of the ethical theory in question. Indeed, in previous chapters,
I perform metaethical reasoning using my system (which formalizes an ethical theory) and basic logical
facts and objects. This kind of reasoning contrasts with ``applied ethical reasoning," which is the use of
ethics to actually resolve ethical dilemmas and make judgements about what an agent should or should not do.
Applied ethical reasoning is about the situation an agent is in, not about an ethical theory as a whole,
abstract entity. In this section, I expore how my system can perform extended applied ethical reasoning. 
Metaethical reasoning is most interesting to philosophers who are trying to formulate the ``best" or 
most correct theory of ethics. Applied ethical reasoning, on the other hand, is useful to ordinary people
who are trying to decide how to live their lives. These two kinds of reasoning represent the two motivations 
for automated ethics. Metaethical reasoning is more directly a way to perform computational ethics, or use a computer
system to do philosophy. Applied ethical reasoning is also relevant to philosophers (applied ethicists 
generally perform this kind of reasoning), but is also relevant to AI agents or people seeking to navigate the world.
In order for automated ethics to guide AI agents, it must perform applied ethical reasoning. 

One challenge of applied ethical reasoning is that it requires more common sense knowledge than metaethical
reasoning. Applied ethical reasoning focuses on a particular ethical dilemma and thus requires enough 
common sense to understand the dilemma and options at hand. For example, for an applied ethicist to 
evaluate the permissibility of lying, they need some robust definition of the term lying and likely some
understanding about the activities of communication and truth telling. In this section, I attempt to
endow my system with this kind of common sense in the specific case of lying. Indeed, in order for my 
system to be used to perform applied ethical reasoning, it will need to be equipped with a database
of common sense facts and definitions as I present in this section. My system will contribute the core
reasoning about the Formula of Universal Law, but this reasoning must be applied to objects that are defined
in this common sense database. In this section, I try to understand what this common sense reasoning looks like
for the specific example of lying. I will examine how different sets of common sense facts impact the 
judgements that my system comes to. 

Because these common sense facts can entirely determine my system's judgement, they are part of the trusted
code base for my system. In order for someone to trust my system's judgements, they must trust that the
common sense database is correct. This common sense reasoning is also not a part of my system—in order for my
system to be used, someone must develop a common sense database for the particular situation at hand. 
The challenge of endowing automated ethical reasoners with common sense reasoning is not unique to my 
system, and virtually all prior attempts in machine ethics face similar challenges.

The specific kind of common sense reasoning required for automated Kantian ethics appears to be a challenge 
for automating Kantian ethics, and perhaps a reason that consequentialist or virtue ethical automated
agents would be within closer reach for automation. Ultimately, I still argue that Kantian ethics is 
easiest to automate because it will require fewer, less controversial common facts than other ethical
systems. As this example demonstrates, Kantian ethics requires a definition of lying (which any other 
theory would also requires) and the knowledge that if everyone lies in a given context, no one will believe 
each other in that particular context. This latter fact may not be required for every ethical theory, 
but is relatively uncontroversial. Indeed, Korsgaard doesn't even bother to give a justification for 
this fact. It is a kind of intuition about human behavior that is generally accepted. Neither a definition 
of lying nor this property of lying seem like unreasonable prerequisites for ethical reasoning. 

Consequentialism, on the other hand, would require much more specific data about the consequences of 
a lie, perhaps for the specific person's credibility, for the victim of the lie, for the third-parties 
watching the lie unfold. Indeed, consequentialism more numerous and specific judgements, all of which are 
likely to be more controversial than the two outlined above for Kantian ethics. Similarly, virtue ethics
would likely require information about the actor's entire moral character, including their attitude
towards the lie and their moral history. Virtue ethics would also require robust definitions of the 
relevant virtues, in addition to a definition of lying. Thus, while Kantian ethics requires some 
common sense reasoning, it requires fewer and less controversial background facts than other ethical theories.

This section will provide additional examples of the kinds of commons sense required to get my system
off the ground. I will aim to use as lean and uncontroversial of a common sense database as possible
to achieve results as robust and powerful as possible. This serves as evidence for the ease of automating
Kantian ethics, an example of what additional work my system requires, and a demonstration of the contributions
that I make.  \<close>

text \<open>Now that I have formalized Korsgaard's sketch of an argument for why lying is prohibited, I will 
implement her argument for why jokes are permissible. Specifically, she considers a joke a story that is 
false and argues that joking is permissible because ``the universal practice of lying in the context of jokes
does not interfere with the purpose of jokes, which is to amuse and does not depend on
deception" \citep[4]{KorsgaardRTL}. Let's define a joke.\<close>

abbreviation joke::"maxim\<Rightarrow>bool" where 
"joke \<equiv> \<lambda> (c, a, g).  \<exists>t. (a \<^bold>\<longrightarrow> (\<lambda>s. knowingly_utter_falsehood s t)) \<and> \<not> (\<exists>p. \<forall>w. (g \<^bold>\<rightarrow> (believe p t)) w)"

text \<open>This definition of a joke merely defines a joke as a falsehood uttered for some purpose that 
emph{doesn't} require deception, where deception involves someone believing the uttered falsehood. Notice 
that this is quite a thin definition of a joke; it doesn't require any conception of humor but merely
distinguishes jokes from lies. As far as common sense reasoning goes, this is a relatively thin proposition. 
I will now demonstrate that this conception of a joke is sufficient to show that joking is permissible.

I will reuse some of the logical structure from the lying example, namely the maxim $m$ and subject $me$. 
I will also reuse the same assumptions to show that, under the same set of ``common sense" facts, lying is
prohibited but joking is not.\<close>

lemma joking_not_prohibited:
  fixes c
  fixes a
  fixes g
  assumes "m \<equiv> (c::t, a::os, g::t)"
  assumes "\<forall>w. \<forall>s. well_formed m s w"
\<comment>\<open>Initial set-up, m is a well-formed maxim composed of some circumstances, act, and goal.\<close>
  assumes "joke m"
\<comment>\<open>$m$ is a maxim about joking. Precisely, it is a maxim in which the action is to knowingly utter a 
falsehood and the goal does not require that someone believe this falsehood.\<close>
  assumes "\<forall>t w. ((\<forall>p. utter_falsehood p t w) \<longrightarrow> (\<forall>p. \<^bold>\<not> (believe p t) w))"
\<comment>\<open>Assumption that if everyone utters false statement t, then no one will believe t. Recall that this
is the most significant piece of common sense reasoning necessary for this example.\<close>
  assumes "\<forall>w. c w"
\<comment>\<open>Restrict our focus to worlds in which the circumstances hold, as these are the morally interesting 
worlds for this example. Basically an irrelevant technical detail. \<close>
  shows "\<Turnstile> (permissible m me)"
  by (smt assms(1) assms(2) assms(3) case_prod_conv)

text \<open>To summarize, in this section I introduce the role of common sense reasoning in my system and 
demonstrate the kind of common sense facts necessary to show that lying is generally prohibited and 
jokes are permissible. I conclude that this kind of sophisticated ethical reasoning requires relatively
thin common sense facts and robust definitions of the terms involved. Thus, while common sense reasoning 
is an obstacle that must be overcome for my system to be used, it is not insurmountable.  \<close>

subsection \<open>Lying to a Liar \label{sec:lyingtoliar}\<close>

text \<open>Once Korsgaard does some preliminary work differentiating between lies and jokes, she begins the 
meat of her argument, which examines the case of the murderer at the door. Recall that the murderer
appears at your door and asks if their intended victim is at home. Ordinary intuition requires that it 
is at the very least permissible (if not obligatory) to lie to the murderer in order to protect the 
victim. Korsgaard notes that a murderer who wishes to find their victim cannot simply announce their
intentions to murder; instead, he must ``must suppose that you do not know who he is and
what he has in mind" \citep[5]{KorsgaaardRTL}. Thus, she can modify the maxim in question and specifies
that when someone lies to you, you are allowed to lie to them. The maxim of lying to the murderer is 
thus actually the maxim of lying to a liar, which she argues is permissible. In this section, I will 
formalize her argument for lying to a liar.\<close>

consts murderer::s
consts not_a_murderer::t
consts victim_not_home::t
consts when_at_my_door::t
consts find_victim::t
consts protect_victim::t
abbreviation murderers_maxim::maxim where 
"murderers_maxim \<equiv> (when_at_my_door, \<lambda>s. knowingly_utter_falsehood s not_a_murderer, find_victim)"
abbreviation murderer_at_door::t where 
"murderer_at_door \<equiv> W murderers_maxim murderer"
abbreviation my_maxim::maxim where 
"my_maxim \<equiv> (murderer_at_door,  \<lambda>s. knowingly_utter_falsehood s victim_not_home, protect_victim)"

text \<open>First, I will show that using the same common sense reasoning justified above, the murderer's
maxim is prohibited.\<close>

lemma murderers_maxim_prohibited:
  assumes "\<forall>w. well_formed murderers_maxim murderer w"
\<comment>\<open>Initial set-up, the murderer's maxim is a well-formed maxim composed of some circumstances, act, and goal.\<close>
  assumes "\<Turnstile> (find_victim \<^bold>\<rightarrow> (believe me not_a_murderer))"
  assumes "\<forall>t w. ((\<forall>p. utter_falsehood p t w) \<longrightarrow> (\<forall>p. \<^bold>\<not> (believe p t) w))"
\<comment>\<open>Assumption that if everyone utters false statement t, then no one will believe t. Recall that this
is the most significant piece of common sense reasoning necessary for this example.\<close>
  assumes "\<forall>w. when_at_my_door w"
\<comment>\<open>Restrict our focus to worlds in which the circumstance of the murderer being at my door holds, as 
these are the morally interesting worlds for this example. Basically an irrelevant technical detail. \<close>
  shows "\<Turnstile> (prohibited murderers_maxim murderer)"   
proof - 
\<comment>\<open>Again, this proof is too heavy for Isabelle to finish on its own, so I needed to specify some
intermediate steps. The same intermediate steps as above sufficed.\<close>
  have "(\<forall>p w. (W murderers_maxim p) w) \<longrightarrow> (\<Turnstile> (find_victim \<^bold>\<rightarrow> (\<^bold>\<not> find_victim)))"
    using assms(2) assms(4) by auto
   have "not_universalizable murderers_maxim murderer"
     using assms(2) assms(4) by auto
   thus ?thesis
     using FUL assms(1) by blast
 qed


lemma lying_to_liar_permissible:
  assumes "\<Turnstile> (well_formed murderers_maxim murderer)"
  assumes "\<Turnstile> (well_formed my_maxim me)"
  shows True oops

text \<open>
let M be the murderer and me be you.
when M lies to you, you can lie to M. 

when M knowingly utters a falsehood with the goal of you believing the falsehood, you can lie to M.

when M knowingly utters falsehood T with the goal of you believing T, you can knowingly
utter falsehood K with the goal of M believing K.

let circumstances C = when M knowingly utters falsehood T with the goal of you believing T
let A = knowingly utter falsehood K with the goal of M believing K
everyone adopts maxim, "C -> A" 
if everyone adopts maxim "C->A", if they believe you believe C, then won't believe A (specifically K) (modify the universal lying assumption)
M doesn't believe you believe C
so M will believe A (might need to add this as an axiom)


\<close>

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

subsection "Murderer Example"

subsection "Ordinary Ethical Reasoning"

subsection "Philosophical Analysis of Applications"
end
(*>*)
