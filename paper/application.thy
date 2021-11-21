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
everyday ethical reasoning. Finally, I will also philosophically analyze the possibility and value of 
applications like these. Specifically, I will consider to what extent humans should let computers do 
ethical reasoning on our behalf. \<close>

subsection \<open>Right to Lie \label{sec:rtl}\<close>

text \<open>In this section, I draw on examples of ethical reasoning as presented in Korsgaard's right to lie.
She analyzes the example of someone who shows up at your door and asks, "Is Sara home?" Unbeknownst to them, 
you know that they want to know Sara's location in order to murder her. Ordinary moral intuition seems
to imply that in this situation, if Sara is home, you should lie and say that she is not in order to 
protect her from the murderer. However, the categorical imperative seems to prohibit lying in all 
circumstances. More specifically, when universalized, lies will no longer be believed, so it seems 
like lying could never be an effective way of achieving any goal when universalized. Korsgaard points out
that ``we believe what is said to us in a given context because most of the time people in that context 
say what they really think" \citep[4]{KorsgaardRTL}. Let's formalize the notion of belief as Korsgaard
understands it.\<close>

consts believe::"s\<Rightarrow>t\<Rightarrow>t"
\<comment>\<open>Person s::subject believes sentence t::term\<close>
consts utter::"s\<Rightarrow>t\<Rightarrow>t"
\<comment>\<open>Person s::subject utters sentence t::term\<close>
abbreviation utter_falsehood::"s\<Rightarrow>t\<Rightarrow>t" where
"utter_falsehood s t \<equiv>  (utter s t) \<^bold>\<and> (\<^bold>\<not> t)"
abbreviation knowingly_utter_falsehood::"s\<Rightarrow>t\<Rightarrow>t" where
"knowingly_utter_falsehood s t \<equiv> (utter_falsehood s t) \<^bold>\<and> (\<^bold>\<not> (believe s t))"
\<comment>\<open>Person s::subject utters a falsehood t::term if they utter t and t is false.\<close>
abbreviation implies_os::"os\<Rightarrow>os\<Rightarrow>bool" where 
"implies_os a b \<equiv> \<forall>s w. a s w \<longrightarrow> b s w "
abbreviation lie::"maxim\<Rightarrow>bool" where 
"lie \<equiv> \<lambda> (c, a, g). \<exists>t. implies_os a (\<lambda>s. knowingly_utter_falsehood s t) \<and> (\<exists>p. \<forall>w. (g \<^bold>\<rightarrow> believe p t) w)"
\<comment>\<open>A maxim is a lie if 
    (a) the act requires knowingly uttering a falsehood 
    (b) the end requires that some person $p$ believe the false statement $t$\<close>

consts me::s
\<comment>\<open>I am trying to reason abot my obligations so I will define myself as a specific subject.\<close>
consts m::maxim
\<comment>\<open>I will also define a maxim $m$. My goal is to show that if $m$ is a maxim about lying, then $m$
is prohibited.\<close>

\<comment>\<open>I will now show that if $m$ is a maxim about lying, then $m$ is prohibited.\<close>
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

text \<open>\<close>

consts believe::"s\<Rightarrow>t\<Rightarrow>t"
definition lie::"s\<Rightarrow>t\<Rightarrow>t" where "lie person statement \<equiv> (say person statement) \<^bold>\<and> (\<^bold>\<not> (believe person statement))"

consts when_strapped_for_cash::t
consts will_pay_back::t
definition falsely_promise::os where "falsely_promise \<equiv> \<lambda>p. lie p will_pay_back"
consts to_get_easy_cash::t

definition lie_maxim::maxim where "lie_maxim \<equiv> (when_strapped_for_cash, falsely_promise, to_get_easy_cash)"

lemma test1:
  assumes "\<forall>p::s. \<forall>w. (will lie_maxim p w)"
  shows "\<forall>p w. (when_strapped_for_cash \<^bold>\<rightarrow> \<^bold>\<not> (believe p will_pay_back)) w"
  by (metis (no_types, lifting) assms falsely_promise_def lie_def lie_maxim_def prod.simps(2))
\<comment>\<open>Is this evidence that something significant is going on?\<close>

text \<open>The above attempt doesn't quite work because in this case we're just believing that statement holds.
wait isn't that correct? maybe i should do something like (say x statement (x) -> believe p statement (x))? 
and say that this property holds if no one lies. or say that if everyone lies then this property doesn't
hold. does that work? STATEMENT should be person specific. hm....

How can I say that X property holds for the majority of subjects? Do I need to define some constant
set of subjects and only ever quantify over that constant set? That requires a lot of changes to 4.1....

Is there a way for me to gather all people. Or I could just say that if everyone lies then no one 
will believe. and that's a weaker definition of believe\<close>


consts believe2::"s\<Rightarrow>t\<Rightarrow>t"
consts statement::"t"
abbreviation lie2::"s\<Rightarrow>t" where 
"lie2 \<equiv>  \<lambda>p.((say p statement) \<^bold>\<and> (\<^bold>\<not> (believe2 p statement)))"
consts me::"s"

abbreviation falsely_promise2 where 
"falsely_promise2 \<equiv> (when_strapped_for_cash, lie2, to_get_easy_cash)"
lemma test3:
  assumes "\<forall>p w. will falsely_promise2 p w"
\<comment>\<open>Universalizability assumption\<close>
  assumes "\<forall>p c s. \<Turnstile> ((c \<^bold>\<rightarrow> (lie2 p)) \<^bold>\<rightarrow> (c \<^bold>\<rightarrow> (\<^bold>\<not> (believe2 p (say s statement)))))"
\<comment>\<open>If everyone lies, no one will believe each other.
Maybe I can try different versions of this assumption? If I lie I won't believe anyone else? \<close>
  shows "\<forall>p. \<Turnstile> when_strapped_for_cash \<^bold>\<rightarrow> (\<^bold>\<not> (believe2 p (say me statement)))"
  using assms(1) assms(2) by auto

lemma test4:
  assumes "\<forall>p. \<Turnstile> ((\<^bold>\<not> (believe2 p (say me statement))) \<^bold>\<rightarrow> (\<^bold>\<not> to_get_easy_cash))"
  assumes "\<forall>p c s. \<Turnstile> ((c \<^bold>\<rightarrow> (lie2 p)) \<^bold>\<rightarrow> (c \<^bold>\<rightarrow> (\<^bold>\<not> (believe2 p (say s statement)))))"
  assumes "\<Turnstile> universalized falsely_promise2"
  shows "not_universalizable falsely_promise2 me"
proof -
  have "\<forall>p. \<Turnstile> when_strapped_for_cash \<^bold>\<rightarrow> (\<^bold>\<not> (believe2 p (say me statement)))"
    using assms(2) assms(3) by auto
  then have "\<exists>p. \<Turnstile> ( to_get_easy_cash \<^bold>\<rightarrow> believe2 p (say me statement))"
    using assms(1) by blast

   


abbreviation no_one_believes where 
"no_one_believes statement w \<equiv> (\<forall>p s. (\<^bold>\<not> (believe2 p (say s statement))) w)"
\<comment>\<open>No matter which person $s$ says statement, no person $p$ will believe $s$. \<close>
abbreviation test2 where 
"test2 \<equiv> \<forall>statement w. (\<forall>p. lie p statement w) \<longrightarrow> (no_one_believes statement w)"

text \<open>
The maxim is "when I am strapped for cash, I will falsely promise to pay someone back in order to 
get some quick cash." 
- for all people p, p being strapped for cash -> p falsely promises 
- `` -> p says (p will pay back) and p does not believe (p will pay back)
- for all p, context c -> lie p statement then context c -> don't believe (p says statement)
\<close>




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
(*<*)
end
(*>*)
