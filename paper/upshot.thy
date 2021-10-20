(*<*) theory upshot
  imports paper41

begin(*>*)

section "Philosophical Contributions"

text \<open>I argue that computational ethics should be useful for and interesting to philosophers for two 
reasons. First, it serves as the basis for AI agents with the capacity for philosophically sophisticated 
ethical reasoning. For example, my project contributes an implementation of the Formula of Universal Law
that an AI agent could use to reason about the world using the categorical imperative. Second, computational 
ethics helps philosophers think about ethics in the same way that calculators or theorem provers help 
mathematicians think about math. I am not arguing that the computer can replace human reasoning or prove things
that humans theoretically couldn't do. Instead, I argue that the computer bolsters human reasoning, firstly by forcing precision due to 
the rigid syntax of a computer program and secondly by making formal proofs less tedious. Below, I explore 
these contributions in greater detail.\<close>

subsection "AI Agents"

text \<open>As artifical intelligence becomes more powerful, the need for ethical AI becomes more urgent.
 Ethically intelligent artificial agents will need to 
be able to reason about sophisticated ethical theories in order to navigate the world. My project could 
serve as one component of a complete ethical reasoner. Specifically, my project could be repurposed 
into a library that takes as input the logical representation of a maxim and determines if it is obligatory, prohibited, 
or permissible.

As it stands, my project can evaluate the moral status of maxims represented in my logic and potentially 
serves as one component of an ``ethics engine," that an AI agent could use to make ethical decisions.
For example, my system could be combined with an input parser to translate moral dilemmas as represented to the AI agent into maxims in my logic and an output 
parser to translate the output of my system into a prescription for the action the AI agent should take.
\ref{fig:AIengine} depicts the workflow of this example of an ethics engine.
\<close>

text_raw \<open>
\begin{figure}
\centering
\includegraphics[scale=0.4]{AI_engine.png}
\caption{An example of an ethics engine for an artificial agent} \label{fig:AIengine}
\end{figure}\<close>

text \<open>In this workflow, an AI agent is faced with a moral dilemma in some internal representation and 
passes this representation to an input parser, which converts it to the appropriate logical representation 
for my system to evaluate. For example, if an AI agent represents the moral dilemma in natural language, 
the parser would convert the natural language representation to a representation in my logic.

Once the
input is a sentence in my logic, my project can evaluate its moral status using my implementation of 
the FUL. Concretely, my project would return a value indicating if the maxim is obligatory, permissible, 
or prohibited. The maxim would be prohibited if it fails the universalizability test, permissible if it passes, and obligatory 
if its negation fails the universalizability test. All three of these properties amount to testing if a 
certain theorem holds or not in my logic, a calculation that I demonstrate in my tests. 

This output could then be converted into some actionable, useful response with another output parser, 
and then passed back to the AI agent. For example, if the AI agent is equipped to evaluate natural language prescriptions, the 
status of the maxim could be parsed into a natural language sentence. This output will be passed back 
to the AI agent, which will use it to make a decision. The input parser, categorical imperative library, 
and output parser together constitute an ``ethics engine" that AI agents could use as a black box 
implementation of an ethical theory. 

The ethics engine depicted above is a high-level example of one way to use my project to guide an artifical agent. The 
upshot is that an automated version of the categorical imperative could function as the ethical engine 
for an AI agent, with some work to parse the input and the output. Effectively, the kind 
of automated ethics I implement could be 
exposed as an ``ethics API" that AI developers could use to easily give AI agent the capacity for 
sophisticated ethical reasoning faithful to philosophical literature. This represents an improvement 
over existing ethics engines, which rarely attempt to capture the complexity 
of any ethical theory that philosophers plausibly defend. For more on how my project is situated 
among other work in automated ethics, see Section ?? \<close>

subsection "Computational Philosophy"

text \<open>Above I explain how my system offers a mechanism for humans to build ethical AI agents. I also 
argue that computational ethics is a mechanism for computers to help humans think differently about 
philosophy. Just as theorem provers make mathematics more efficient and push mathematicians to think 
precisely about the phenomena they are modelling, computational ethics can help philosophers think about 
philosophy. Below I share an example of the kind of philosophical insight that computational ethics 
can prompt and analyze the value that this tool offers to philosophers. \<close>

subsubsection "Example of a  Philosophical Insight"

text \<open>As I tested prior formalizations of the categorical imperative and created my own, the process 
of implementing and testing a formalization using an interactive theorem prover resulted in philosophical 
insights that were novel to me. I reached surprising logical results that provoked 
interesting philosophical conversations as I tried to understand their implications for the ethical 
theory I am formalizing. This serves as an example for how computational ethics can prompt philosophical 
insights. For example, as I was implementing my formalization of the FUL, I realized
that my formalization was inconsistent unless I specified that the FUL only held for ``well-formed maxims,"
such that neither the act nor goal were already achieved in the given circumstances. Below I document how 
I came to this conclusion. 

First, I used Sledgehammer to show that my formalization of the FUL\footnote{The full logical representation is @{abbrev FUL0}.}
resulted in a contradiction. Sledgehammer was able to tell me which axioms it used to complete 
this proof, showing me that my formalization contradicted the axiom O\_diamond, which states that an 
obligated term cannot contradict its context. I hypothesized that there was some tension between 
the antecedent of the FUL, which states that a maxim is acted on by all agents, and the consequent, 
which states that a maxim is prohibited. If the maxim has already been acted on, then not acting on it
becomes impossible so the prohibition is impossible to obey.

To solve this problem, I returned to Korsgaard's practical contradiction interpretation and focused 
on the imaginatory component of the FUL. Specifically, the universalizability test requires that we imagine 
a world where the maxim is universalized, not that the maxim is actually universalized at the actual world. 
I implemented another version of the FUL under which, if a maxim is universalized at any world and rendered
ineffective at that world, it is prohibited at the current world. I hypothesized that this would remove 
the contradiction found above. To test this new formalization, I used Nitpick, a model checker that 
quickly generates models that satisfy some axioms and theorems. Usually, Nitpick can find a satisfying 
model to show that a logic is consistent in a matter of seconds, but Nitpick consistently timed out 
when looking for a model of my modified FUL. 

Nitpick generates many models and checks if they satisfy the given maxims. I suspected that Nitpick 
could potentially be timing out due to checking large models that exhausted its 
time limit, especially due to the logical complexity of my theory. To avoid this, I decided to specify the exact number of maxims 
in the system by passing as an argument to Nitpick the cardinality of my desired model. This did not 
fix the problem. I next defined a particular (circumstance, act, goal) tuple as a constant and, instead of
stating that the FUL held for all maxims, I stated that the FUL held for the specific maxim formed by this tuple.
To my surprise, Nitpick was now able to show that the FUL was consistent.

This appeared counterintuitive—after all, what is the difference between a model of cardinality 
1 and a model with one constant object? Professor Amin pointed out that as constants, the circumstances, 
act, and goal for which the FUL held were all distinct, but could be the same when quantified over. One line 
of code later, I tested this hypothesis and found that requiring that the circumstances did 
not entail the act or goal fixed the inconsistency. This logical inconsistency showed me that the FUL 
could not hold for maxims in which the act or goal have already been achieved in the circumstances.

To understand the philosophical plausibility of this property, I returned to Korsgaard and O'Neill's 
interpretations of maxims as practical, action-guiding principles. A maxim in 
which the circumstances already entail the act or goal is vacuous and therefore not a useful practical principle 
to evaluate. For example, the maxim, ``When I am eating breakfast, eat breakfast in order to eat breakfast," 
is not necessarily prohibited, but it is the wrong kind of question to be asking. The Formula of Universal 
Law is supposed to guide practical reason, the force that we use to navigate the world and decide what 
to do. Poorly formed maxims are of no use to practical reason and are the wrong kind of input to pass
to the categorical imperative. This is a non-trivial philosophical insight that the computer helped me discover.\<close>

subsubsection \<open>Two Uses of Computational Ethics\<close>

text \<open>I do not argue that computational ethics, as it stands today, uncovers philosophical insights that humans have not reached 
or are incapable of reaching. After all, my understanding of a well-formed maxim could 
very well exist in the literature and certainly could be reached by a philosopher working without any 
computational tools. Instead, I argue that computational tools prompt philosophers to ask questions that 
lead to insights. The computer offers a different perspective by forcing philosophers to make their 
work precise and allowing them to quickly complete proofs that would otherwise be tedious. Computational 
ethics can serve as another tool in a philosopher's arsenal, like a thought experiment or counterexample.

The first contribution of computational ethics is precision.
Representing a philosophical idea in logic and implementing it in an interactive theorem prover requires 
making the idea precise to a degree that ordinary discussion does not require. The initial representation 
of an idea in a logic requires making its form precise. For example, 
as I formalized the notion of a maxim, I had to understand its components and define it as a 
circumstance, act, goal tuple. Moreover, Isabelle's strict typing system required that I define 
coherent, consistent types for each of these entities and for a maxim as a whole. This requires understanding 
what role each of these components play in the FUL and assigning them each a type. In my example, I 
concluded that circumstances and goals are terms, which can be true or false at a world, and acts are 
open sentences, which are true for a particular subject at a particular world. This precision is possible 
without computational tools, but computational ethics forces a level of precision that ordinary discussion 
does not demand. Type fuzziness and overloaded definitions are all too common in philosophical writing and 
discussion (would be cool to cite some famous debate revolving around this idea), but computers don't 
allow this kind of imprecision.

The second virtue of computational ethics is that it makes formal ethics far less tedious, and therefore 
within reach even for non-logicians. There is plenty of work attempting to develop logical representations 
of philosophical phenomena in order to make these phenomena precise and use the tools of logic to prove 
facts about them\footnote{Is there? Should cite stuff}. Much of this work, however, requires tedious pencil and paper proofs which may not 
always produce relevant philosophical insights. Interactive theorem provers make such proofs accessible 
even to philosophers who don't specialize in logic. Moreover, these proofs start from first principles 
without requiring that a human being write pages and pages of syllogism as in Principia Mathematica. 
Just as calculators make arithmetic fast and accessible to non-specialists, computational ethics does the same for 
formal philosophy.\<close>

subsubsection \<open>Looking Forward\<close>

text \<open>
Computational ethics is at its infancy. The use of theorem provers in mathematics is just now beginning 
to make headway @{cite buzzardvideo}, even though theorem provers were first invented in the 1960's @{cite historyofITP}. In contrast, the first attempts to use theorem 
provers for ethics occurred in the last decade. The fact that this nascent technology is already 
helping humans reach non-trivial philosophical conclusions is reason to, at the very least, entertain 
the possibility of a future where computational ethics becomes as normal as using a calculator for arithmetic.

To the skeptic, the ethical insights uncovered by the computer are not necessarily impressive 
philosophy. Indeed, the fact that a theorem prover requires specialized knowledge outside of the field 
of philosophy indicates that the technology is nowhere near ready for universal use in philosophy 
departments. However, history indicates that as computing power increases and computer scientists make 
progress, computational ethics will become more usable. Theorem provers in mathematics began as toys 
incapable of proving that the real number 2 is not equal to the real number 1, but Buzzard showed that 
moving from such a primitive system to a tool for Fields medal winning mathematics is possible in a 
matter of years @{cite buzzardvideo}. Countless examples from the history of computer science, from the Turing 
Test to AI game playing to protein folding, demonstrate that progress in computer science can make seemingly 
obscure computer programs useful and usable in ways that exceed our wildest imaginations. Indeed, 
programmable computers themselves initially began as unwieldy punch card readers, but their current ubiquity 
need not be stated. If computer scientists and philosophers invest in computational ethics, it can 
become as much a tool for philosophy as a calculator is for for arithmetic.\footnote{Is this too like, 
lalalala fantasy of computational philosophy? Would it be less so if I did more work explaining 
the history of theorem proving for math? Is this even that important for my project?}
\<close>


(*<*)
end
(*>*)
