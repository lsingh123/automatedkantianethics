(*<*) theory thesis_5_discussion
  imports Main

begin(*>*)

text\<open>
There is robust debate in the literature on what
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
can be overcome in relatively uncontroversial ways. They are also ripe areas for future work. \<close>
(*<*)
end
(*>*)
