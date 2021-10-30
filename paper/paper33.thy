(*<*) theory paper33
  imports  paper22 paper224

begin(*>*)

subsection "Lessons Learned and Goals for Chapter 3"

text \<open>In this chapter, I tested two prior attempts to formalize the Formula of Universal Law and found 
that these attempts didn't faithfully interpret the FUL. Specifically, certain properties that 
we expect to hold of the FUL didn't hold in these implementations. In an attempt to remedy these 
shortcomings, in the next chapter, I present my own custom implementation of the FUL that satisfies these properties
and is thus more faithful to the literature. Before presenting my 
implementation, I define some goals for my custom formalization based on learnings from prior
attempts and from philosophical literature on the FUL.

The results presented below are summarized in Figure \ref{fig:goalstable}. For each goal, I indicate which 
interpretations successfully meet that goal. The fact that my custom formalization meets all the goals
indicates that it improves on prior formalization attempts. Below I will explain and justify
the goals. \<close>

text_raw \<open>
\begin{figure}
\centering
\includegraphics[scale=0.4]{goalstable.png}
\caption{Table indicating which goals are met by the naive formalization, Kroy's formalization, and 
the custom formalization respectively..} \label{fig:goalstable}
\end{figure}\<close>

subsubsection "Goals From Prior Attempts"

text \<open>\textbf{FUL Stronger than DDL} One simple objective that the naive formalization failed to meet is the fact that the FUL should
not hold in the base logic (DDL). Recall that the naive formalization of the FUL\footnote{
This formalization reads $\vDash ((\neg (\square P \{A\})) \longrightarrow O \{\neg A\})$.} held in the 
base logic, so adding it as an axiom didn't make the logic any stronger. This is troubling 
because the base logic does not come equipped with the categorical imperative built-in. It 
defines basic properties of obligation, such as ought implies can, but contains no axioms that represent
the formula of universal law. Therefore, if a formalization of the FUL holds in the 
base logic, then it is too weak to actually represent the FUL. The naive interpretation holds in DDL but Kroy's formalization
does not. Because the naive interpretation is no stronger than DDL, it is acts a control group equivalent
to DDL itself.

\medskip 

\textbf{Obligation Universalizes Across People} Another property of the Formula of Universal Law that any implementation should satisfy is that obligation
generalizes across people. In other words, if a maxim is obligated for one person, it is obligated
for all other people because maxims are not person-specific. Velleman argues that, because 
reason is accessible to everyone identically, obligations apply to all people equually \cite[25]{velleman}. 
When Kant describes the categorical imperative as the objective principle of the will, he is referring 
to the fact that, as opposed to a subjective principle, the categorical imperative applies to all 
rational agents equally $\cite[16]{groundwork}$. At its core, the FUL best handles, ``the temptation 
to make oneself an exception: selfishness, meanness, advantagetaking, and disregard for the rights 
of others" \cite[30]{KorsgaardFUL}. Kroy latches onto this property and makes it the content of his
formalization, which essentially says that if an act is permissible for someone, it is permissible for 
everyone.\footnote{Formally, $P\{A(s)\} \longrightarrow \forall p. P\{A(p)\}$} While Kroy's interpretation 
clearly satisfies this property, the naive interpretation does not.

\medskip

\textbf{Contradictory Obligations} Another problem with prior formalizations was that they didn't
prohibit contradictory obligations, partially because DDL itself allows contradictory obligations. 
Kant subscribes to the general, popular view that morality is supposed to guide action, so ought implies 
can.\footnote{Kohl points out that this principle is referred to as 
Kant's dictum or Kant's law in the literature \cite[footnote 1]{kohl}.} Kohl reconstructs his argument for the principle as 
follows: if the will cannot comply with the moral law, then the moral law has no prescriptive authority 
for the will \cite[703-4]{kohl}. This defeats the purpose of Kant's theory—to develop an unconditional, categorical imperative 
for rational agents. Ought implies can requires that obligations never contradict, because an agent 
can't perform contradictory actions. Therefore, any ethical theory that respects ought implies can, 
and Kantian ethics in particular, must not result in conflicting obligations. 
Kant only briefly discusses contradictory obligations in \emph{Metaphysics of Morals}, where he argues that 
conflicting moral obligations are impossible under his theory \cite[V224]{metaphysicsintro}. Particularly, the categorical imperative generates 
``strict negative laws of omission," which cannot conflict by definition \cite[45]{timmerman}. \footnote{The 
kinds of obligations generated by the FUL are called ``perfect duties" which arise from ``contradictions 
in conception," or maxims that we cannot even concieve of universalizing. These duties are always negative 
and thus never conflict. Kant also presents ``imperfect duties," generated from ``contradictions in will,"
or maxims that we can concieve of universalizing but would never want to. These duties tend to be broader, 
such as ``improve oneself" or "help others," and are secondary to perfect duties. My project only analyzes 
perfect duties, as these are always stronger than imperfect duties.}. Both the naive formalization and 
Kroy's formalization allow contradictory obligations. 

During testing, I also realized that contradictory obligations are closely related to two other properties
that also fail in both of these systems. First is the idea that obligation implies permissibility, or 
that obligation is a stronger property than permissibility. If there are no contradictory obligations, 
then this property holds because actions are either permissible or prohibited and obligation contradicts
prohibition. Moreover, in a system with contradictory obligations, this property fails because there is some
A that is obligated but also prohibited and therefore not permisible. Indeed, formalizing this property below shows 
that this follows from the definition of implication in propositional logic.

\medskip 

\<close>

lemma "\<Turnstile> ((O {A} \<^bold>\<and> O {\<^bold>\<not> A}) \<^bold>\<equiv> (\<^bold>\<not> (O {A} \<^bold>\<rightarrow> \<^bold>\<not> O {\<^bold>\<not>A})))"
  by simp

text \<open>\textbf{Distributive Property} Another property related to contradictory obligations is the distributive property for the obligation
operator.\footnote{Formally, $O\{A\} \wedge O\{B\} \longleftrightarrow O\{A \wedge B\}$.} This is 
another property that we expect to hold. The rough English translation of  $O \{ A \wedge B \} $ is ``you are obligated to 
do both A and B". The rough English translation of $O\{A\} \wedge O\{B\}$ is ``you are obligated to do A 
and you are obligated to do B." We think those English sentences mean the same thing, so they should mean 
the same thing in logic as well. Moreover, if that (rather intuitive) property holds, then contradictory
obligations are impossible, as shown in the below proof.\<close>

lemma distributive_implies_no_contradictions: 
  assumes "\<forall>A B. \<Turnstile> ((O {A} \<^bold>\<and> O {B}) \<^bold>\<equiv> O {A \<^bold>\<and> B})"
  shows "\<forall>A. \<Turnstile>( \<^bold>\<not>(O {A} \<^bold>\<and> O {\<^bold>\<not> A})) "
  using O_diamond assms by blast

text \<open>Thus, while testing contradictory obligations, I also test the distributive property for the 
obligation operator. Again, this property fails in the naive formalization and for Kroy's formalization.


\medskip 

\textbf{Un-universalizable Actions} This goal is inspired by a test performed for Kroy's formalization. Under 
a naive reading of the Formula of Universal Law, it prohibits lying because, in a world 
where everyone simultaneously lies, lying is impossible. In other words, not everyone can simultaneously
lie because the institution of lying and believing would break down. More precisely, the FUL should 
show that actions that cannot possibly be universalized are prohibited, because those acts cannot be willed in 
a world where they are universalized. This property fails to hold in both the naive formalization 
and Kroy's formalization and is a goal for my custom formalization.\<close>

subsubsection "Goals From Philosophical Literature"

text \<open>The goals above come from moral intuition, properties of Kantian ethics, and logical requirements. 
In order to stay faithful to centuries of philosophical debate about the meaning of the Formula of 
Universl Law, I also present some goals inpsired by this literature.

\textbf{Maxims} Kant does not evaluate the correctness of acts, but rather of maxims. Therefore, any 
faithful formalization of the categorical imperative must evaluate maxims, not acts. This requires 
representing a maxim and making it the input to the obligation operator, which neither of the prior attempts do.

\medskip

\<close>

text \<open>\textbf{Practical Contradiction Interpretation} Kantians debate the correct interpretation of the Formula of Universal Law because Kant appears to 
interpret the universalizability test in different ways. Korsgaard argues for the practical contradiction 
interpretation, broadly accepted as correct within the philosophical community $\cite[177]{ebelsduggan}$.
Because her argument is broadly accepted, I will make it a goal to represent the practical contradiction
interpretation of the FUL in my custom formalization. The naive formalization and Kroy's formalization
clearly do not meet this goal.

Below, I briefly reconstruct Korsgaard's argument for the practical contradiction interpretation. While 
she believes that the text partially supports this interpretation, her argument is philosophical and 
derives its strength from the plausibility of the practical contradiction interpretation.

Recall that the formula of universal law is “act only in accordance with that maxim through which you can at the 
same time will that it become a universal law” $\cite[4:421]{groundwork}$. To determine if a maxim can be willed as a 
universal law, one must use the “universalizability test,” which requires imagining a world in which 
everyone for all of time has willed the maxim. If willing the maxim in such a world generates a contradiction, 
then the action is prohibited. There are three interpretations of what sort of contradiction is necessary: 
(1) the teleological view, prohibiting actions that conflict with some assumed teleological end when 
universalized, (2) the logical contradiction view, prohibiting maxims that are logically impossible 
when universalized (such as the lying example discussed earlier), and (3) the practical contradiction view, prohibiting maxims that are self-defeating 
when universalized.

Under the logical contradiction interpretation, falsely promising to repay a loan to get some quick cash
fails the universalizability test because, in such a world, the practice of promising would die out so 
making a false promise would be impossible. Korsgaard appeals to Dietrichson @{cite dietrichson} to construct the example of 
a mother killing her children that tend to cry more than average so that she can get some 
sleep at night. Universalizing this maxim does not generate a logical contradiction, but it is clearly 
morally wrong. The problem here is that killing is a natural action, which Korsgaard distinguishes from 
a practice, like promising. Natural actions will never be logically impossible, so the logical contradiction 
view fails to prohibit them.

Under the teleological contradiction interpretation, a maxim is prohibited if it undercuts some natural 
or assigned purpose for some practice, act, or object. For example, the purpose of promising is to 
create a system of mutual trust and false promising undercuts this purpose and is thus prohibited. The problem 
with this view is that it assumes that the agent is committed, either because of their own goals or 
because of some property of a rational will, to some teleological system. Acton formulates Hegel's argument that @{cite acton},
an agent doesn't have to be committed to promising as a system of mutual trust. Korsgaard concludes that 
assigning teleological purposes to actions is difficult because ``such purposes may have
nothing to do with what the agent wants or ought rationally to want, or even with what
any human being wants." If the agent is not committed to the purpose, then will not see a contradiction 
in willing an act that violates this purpose.

This difficulty with the teleological contradiction interpretation drives Korsgaard to look for purposes
that an agent must necessarily be committed to, and she concludes that this must be the purpose of the 
maxim itself. By willing a maxim, an agent commits themselves to the goal of the maxim, and thus cannot 
rationally will a system in which this goal is undercut. This system satisfactorily handles natural actions
like those of the sleep-deprived mother: in willing the end of sleeping through the night, she is 
implicitly willing that she be alive in order to secure and enjoy her sleep. If any mother is allowed to kill
any loud child, then she cannot be secure in the possession of her life, because her own mother may have 
grown frustrated with her crying. Her willing this maxim thwarts the end that she sought to secure. 

The practical contradiction interpretation not only addresses the problems with the first two 
interpretations, it also offers a much more satisfying explanation of why certain maxims are immoral. 
The problem is not the existence of a contradiction itself, but instead the fact that these maxims 
involve parasitic behavior on social conditions that the agent seeks to benefit from. The false promiser 
simultaneously wants to abuse the system of promising and benefit from it, and is thus making an exception 
of themselves. It is this kind of free-riding that the universalizability test seeks to draw out. The test
raises the same kinds of objections that the question ``What if everyone did that?" seeks to draw out.

Note that the practical contradiction interpretation is strictly stronger than the logical contradiction
interpretation. Actions that are not universalizble, like lying, are also not effective means to any end
when universalized because they become impossible. Therefore, a formalization of the practical contradiction
interpretation must still obey the earlier goal that non-universalizable acts be prohibited.  \<close>

 
(*<*)
end
(*>*)
