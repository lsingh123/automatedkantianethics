(*<*) theory paper (*>*)
(*<*) imports carmojones_DDL (*>*)

(*<*) begin (*>*)

section Introduction

text \<open>Leibniz dreamed of modelling all knowledge in the language of formal logic, so that all 
reasoning could be automated and all disputes could be solved with calculation. In the 21st 
century, both the logical and computational machinery exist to make Leibniz's dream a reality. A
key area of knowlege that can be automated is ethical reasoning. Computational 
ethics is a young but attractive field for two primary reasons. First, the proliferation of 
artifically autonomous agents is creating and will continue to create a demand for 
ethical autonomous agents. One answer to the call for ``ethical AI" is the creation 
of automated ethical reasoners. Second, just as automated mathematical reasoning gives mathematicians
new powers and proof-finding ability, automated ethical reasoning is a tool that philosophers can use 
when reasoning about ethics. Many contradictions or paradoxes with an ethical system may not be 
immediately obvious to the human eye, but can be easily tested using an automated theorem prover.

Modelling ethics without sacrificing the intracacies and complexities of an ethical theory is a 
challenging computational and philosophical problem. Much prior work encodes ethics as a constraint 
satisfaction problem, with ethical rules as the constraints. This approach to ethics does not capture 
all of the complexity of any plausible ethical system. Any faithful model of an ethical theory will 
require machinery more complex than a single constraint satisfaction problem.

In addition to computational machinery, computational ethics also requires a sophisticated 
ethical theory to model. Constraint satisfaction systems often default to some version of utiliarianism, 
the principle of doing the most good for the most people. Alternatively, they model basic moral 
principles such as ``do not kill," without modelling the theory that these principles originated from.
Modelling a more complex ethical theory will not only enable smarter philosophical machines, it will
also empower philosophers to study more complex ethical issues with the computer's help.

The ideal candidate ethical theory will be both philosophically interesting and easy to 
formalize. Kantian ethics, often described as ``formal," is such a candidate. The categorical imperative,
Kant's universal law of morality, is a moral rule that can be used to guide action in all spheres of life.
Kant's original presentation itself is methodical and formal, and the theory lends itself well to 
formalization.

This paper's objective is to automate reasoning about Kantian ethics. I present, implement, and test
three formalizations of Kant's categorical imperative in the Isabelle/HOL theorem prover. Each 
formalization is modelled as an extension of Carmo and Jones' Dyadic Deontic Logic (DDL). The corresponding 
DDL formalization is then embedded in higher-order logic (HOL) and implemented in Isabelle. Section 
3.1 implements and tests the naive formalization, a control group that is equivalent to DDL 
itself. Section 3.2 examines a more sophisticated formalization inspired by Moshe Kroy's partial 
formalization of thecategorical imperative. Section 3.3 explores ????

I contribute implementations of three different interpretations of the categorical imperative, 
examples of how each implementation can be used to model and solve ethical scenarios, and tests that
examine ethical and logical properties of the system, including logical consistency, consistency
of obligation, and possibility of permissibility. The implementations themselves are usable models 
of ethical principles and the tests represent the kind of philosophical work that formalized ethics 
can contribute.\<close>

section "System Overview"

text \<open>The goal of this project is to automate sophisticated ethical reasoning. This requires three
key components. First, the choice of an ethical theory that is both intuitively attractive and 
lends itself to formalization. Second, the choice of formal logic to model the theory in. Third, the 
choice of automation engine to implement the formal model in. Section 2.1 introduces Kantian
ethics, Section 2.2 exposits Carmo and Jones's Dyadic Deontic Logic @{cite CJDDL} as a 
base logic, and Section 3.3 presents the Isabelle/HOL theorem prover used to implement the 
formalization.\<close>

subsection "Kantian Ethics"

text \<open>Kantian ethics is an attractive choice of ethical theory to automate for two key reasons. The 
first is that Kant's writings have been a major inspiration for much of Western analytic philosophy. 
In addition to the rich neo-Kantian program, almost all major philosophical traditions after Kant have
engaged with his work, including the logicians of the 20th century. Much of Western libertarian
political thought is inspired by Kant's deontology, and his ethics have bled into household ethical 
conversations. Deontology is seen as one of the three major schools of traditional analytic philosophy.

Kantian ethics also lends itself to formalization because of its rule-based structure. Understanding 
the ethic's potential for formalization requires understanding some of Kant's system. Kant argues 
that if morality exists, it must take the form of an inviolable rule, which he calls the ``categorical
imperative." He presents three formulations of the categorical imperative, as well as a robust defense
of them in his seminal work on ethics. {@cite Groundwork} He argues that all three formulations are 
equivalent. 

The first formulation of the categorical imperative is often called the ``Formula of Universal Law."
The FUL states ``I ought never to act except in such a way that I could also will that my maxim should 
become a universal law."{@cite Groundwork} The FUL creates a thought experiment called the universalizability test: to 
decide if a maxim is permissible, imagine what would happen if everyone willed that maxim. If your 
imagined world yields a contradiction, the maxim is prohibited. The universalizability test makes the 
``formal" nature of Kant's ethics immediately clear. Formal logic has the tools to universalize a 
maxim (apply a universal quantifier) and to test for contradictions (test for inconsistency or 
validity). 

Kant also presents two additional formulations of the categorical imperative. The Formula of Humanity (FUH)
is to act in such a way "that you use humanity, whether in your own person or in the person
of any other, always at the same time as an end, never merely as a means." This formulation cements 
Kant's belief in human dignity. The third formulation of the categorical imperative, often called 
the Kingdom of Ends, is that "we should so act that we may think of ourselves as legislating universal 
laws through our maxims." {@cite Korsgaard} These formulations are not as obviously formal as the FUL, 
but they can still be modelled in logic. Because Kantian ethics presents a series of rules, a logical
system can encode the theory by modelling each rule as an axiom.

The formal nature of Kant's ethic is not accidental. Kant has been a major influence on the 
development of modern logic, and the starting point for his ethic is unequivocally reason. The ethic 
is often criticized for the stringency of its rules, but the unconditional and universal nature of 
the categorical imperative is precisely what makes it a good candidate for formalization. 

The above outline is a brief and incomplete picture of a rich philosophical tradition. Kantian scholars
debate the meaning of each formulation of the categorical imperative and develop views far more 
nuanced than those above. For the purposes of this paper, I will adopt Kant's three original 
formulations presented above. Note additionally that Kantian ethics is widely disputed. Like any 
ethical theory, Kant's ethic has vocal critics and has inspired philosophical schools in its 
opposition. I do not present a defense of Kant's ethic in this paper. My approach to formalizing 
ethics can be applied to other theories as well. I choose Kantian ethics as a case study due to its 
influence and formality.\<close>

subsection "Dyadic Deontic Logic"

subsection "Isabelle/HOL"

section "Details"

subsection "Naive Implementation/Control Group"

subsection "Kroy's Partial Formalization"

section "Related Work"

section "Conclusion"


(*<*) end (*>*)