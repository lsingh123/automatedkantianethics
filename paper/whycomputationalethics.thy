(*<*) theory whycomputationalethics
  imports Main

begin(*>*)

section \<open>Is Computational Ethics A Good Idea?\<close>

text \<open>Even if computational tools can help philosophers with ethical inquiry, some may worry that they
somehow cheapen philosophy. After all, there seems to be something valuable about the process of ethical
reasoning and computational ethics threatens to destroy this value. In this section, I argue that, 
regardless of where we locate the value of ethics, computational ethics can enhance this value. The
value of human ethical reasoning is a reason to avoid totally automating the study of ethics, but 
human-computer symbiotic ethics preserves this value. Human-computer symbiosis is a model of computation
in which humans ``set the goals, formulate the hypotheses, determine the criteria, and perform the evaluations,”
and computers perform ``routinizable work that must be done to prepare the way for insights and decisions” \citep{licklider}.
There are two different kinds of ethics that
could benefit from computational tools: the kind that ordinary people use to decide how to live their 
lives and the kind studied by professional philosophers. In the first subsection, I consider the role of ethics 
in an ordinary person’s life and in the second subsection, I analyze the value that ethical study offers to 
the professional philosopher. 

I will contrast human-symbiotic ethics with fully automated ethics, in which computers replace human
ethicists entirely and produce ethical theories and truths with no human input. This vision is far
from becoming a reality. Fully automated ethics may not even be possible, and I do not claim to implement 
anywhere near fully automated ethics in this project. I will use this as an extreme example to understand
the limitations of the arguments below. If a theory of the value of ethical study implies that 
fully automated ethics is good, then it will certainly imply that the kind of ethics I implement
in this project is good.
\<close>

subsection "Ethics for Ordinary People"

text \<open>Ethics has immediate bearing on everyone’s lives because it studies the unavoidable question: 
how should we live? If computers can make this study more efficient, then it seems that everyone should
engage in computational ethics. As Cornel West says, the ethical question is the only question that 
we answer merely by living. To turn away from ethics is to take a stance on the question of how to 
live (namely, to live unreflectively) and thus to engage in ethics. Ethical truths are valuable because 
they tell us how to live. Every rational being must decide how to navigate the world and ethical 
truths answer these questions. If the results of ethical study is practically valuable, then automated 
ethics is good because computational tools can help us locate ethical prescriptions and theories more efficiently. 
In the most extreme case, we can unthinkingly follow the commands of an ethical calculator that dictates 
how we should live. Computers can answer the unavoidable question for us.

Placing the value of ethics olely in its action-guiding potential fails to take into account the 
importance of practical reason, which, as I argued in Section Why Kant, is the source
of freedom itself. 
We are committed to ethical reflection because of the kind of beings that we are. Recall that Korsgaard 
argues that, as beings occupying minds with a reflective structure, when faced with a choice, “it is as if there 
were something over and above all of your desires, something that is you, and that chooses which desire 
to act on” (Sources 83). This choosing is the operation of practical reason, and this reflection
makes us free. We are free because we must choose which reasons to act on. Every decision that we 
make is an exercise of freedom. 

If reflecting makes us free, then unthinkingly obeying the computer sacrifices our autonomy. Consider 
the thought experiment of an Ethics Oracle that can unfailingly tell you the right thing to do in any 
situation.\footnote{This example is inspired by the Pocket Oracle presented in \citet{bok}.} Someone 
who surrenders themselves to this Oracle unthinkingly follows its prescriptions. 
There is some reflection involved in the decision to obey each of the Oracle’s prescriptions, but 
this is a thin kind of reflection \citep{bok}. This person is not reflecting on the real matters at hand and is 
not making decisions for themselves. They have surrendered their reflective capacity to the Oracle. 
They live a worse life than someone who reflects on their actions. They have less ownership over their 
actions than the reflective person. In a less extreme case, a person may retain control of many of 
their decisions but cede some important or tricky choices to the Ethics Oracle. Because every single 
exercise of practical reason is an exercise of autonomy, this person is still less autonomous than the 
purely reflective person. Even surrendering simple, inconsequential decisions such as which flavor of 
coffee to drink surrenders some piece of our autonomy. Perhaps in trivial cases we can accept that 
tiny sacrifice in autonomy, but giving over life-changing decisions to the machine sacrifices our 
core freedom. Unreflectively relying on computational ethics surrenders our autonomy to the machine. 

One objection to this emphasis on reflection is the impracticality of making ethical calculations from first principles 
every time we are faced with a decision. This is why we follow the advice of moral mentors, like our 
family or influential philosophers. These moral mentors differ from the Ethics Oracle because their advice 
comes with an argument justifying it; if human-computer symbiotic computational ethics also prompts 
reflection on the prescriptions given, it can also guide action without sacrificing autonomyy.
Most people do not reason about ethics during everyday decisions; they rely on some combination of 
prior knowledge and external testimony. For example, my mother taught me to respect myself, and I 
follow her advice. What is the difference between following the guidance of a moral educator and 
obeying the Ethics Oracle? The best kind of ethical advice prompts reflection, such as an argument 
made in a philosophy paper. Unthinkingly following someone’s advice results in the same loss of 
autonomy as unthinkingly obeying the Ethics Oracle; people who merely obey orders are less autonomous 
than those who think for themselves. This account of moral advice offers a model for human-computer 
symbiotic ethics. The computer should serve as a moral guide by providing arguments on what the right 
thing to do is, just as my mom explained why I should always respect myself. Human-computer symbiotic 
ethics nurtures autonomy when it not only offers prescriptions for action, but also explanations for 
these prescriptions. Because my theorem-prover-based computational ethical system is explainable, it can 
guide action without sacrificig autonomy because it can make an argument for some action, instead of 
only giving a verdict as many machine learning algorithms do. Isabelle can list the facts used to show
a partcular action prohibited, and a human being can reflect on whether or not these principles
indeed prohibit the action in question. The computer serves as a collaborator and a tool, but not as an authority, 
so the human being’s reflective capacity and freedom is preserved. 
\<close>

subsection \<open>Academic Ethics\<close>

text \<open>
Academic philosophers publish papers, mostly read by other professional philosophers or by philosophy students. 
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

If ethical truths also offer some value to society at-large, it seems ridiculous to sacrifice this 
value merely to preserve human philosophers’ fun. A more compelling argument against fully automated 
ethics is that the existence of human academic philosophers offers value even to non-philosophers. 
People derive joy and wonder from knowing that human beings produced great ethics. Plato’s Apology 
is not only a profound and insightful text, but it is also wonderous that a human being produced such 
a work. We derive joy from knowing that our fellow humans are capable of the kind of thought that 
great philosophers accomplished, just as an unimaginably beautiful work of art is more wonderous 
because a human being painted it. We watch the Olympics because we derive wonder and joy from human 
excellence. Even when admiring computational achievements, such as Google’s recent success in protein 
folding, we admire the human who programmed the machine, not the machine itself. We can relate to 
humans, so the mere knowledge that great people are doing great things enriches our lives. This 
knowledge is part of the attraction for the thousands of tourists who visit Harvard Yard every year; 
this is a place where of great human achievement\footnote{Is this too like, arrogant?}.

An even stronger argument for human-computer symbiotic ethics instead of fully automated ethics is 
that ethics is certainly an inherently human subject. We study ethics because, as argued above, we 
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

To present-day philosophers, computational ethics may sound outlandish. After all, no machine could 
or should replace humans studying the inherently human subject of ethics. Even though computational
tools may seem inaccessible to philosophers, they can make their work more efficient and interesting, 
just as online text-editors made philosophical communication clearer. The human-computer symbiotic model
understands computers as one tool in the philosopher's toolkit, like a thought experiment or counterargument.
Fully automated ethics certainly threatens something valuable about the field of philosophy, but
this model of computational ethics merely gives philosophers the ability to say, ``this argument was
verified by a computer." 
\<close>

(*<*)
end
(*>*)
