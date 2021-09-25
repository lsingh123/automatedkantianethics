(*<*) theory paper41
  imports  paper22 paper224

begin

typedecl s \<comment>\<open>s is the type for a ``subject," i.e. the subject of a sentence\<close>

text \<open>Borrowing subjects from Ch. 2.\<close>

typedecl act \<comment>\<open>Type representing an act such as ``Running"\<close>
typedecl goal \<comment>\<open>Type representing a goal such as ``To visit my mother"\<close>

type_synonym logos = "(t * act * goal * s)" \<comment>\<open>A logos or principle according to Aristotle
 is a circumstance, act, goal, subject pair. Read logos (C, A, G, S)
as ``In circumstance C, S will do A in order to G." A circumstance is represented as a set of worlds 
$t$ where that circumstance holds.

Korsgaard interprets a maxim as being equivalent to a logos, and thus only being composed of the features
above. Kitcher argues for one additional component: the motivation. This additional component is read 
as ``In circumstance C, S will do A in order to G because of M." where M may be ``duty" or ``self-love."
This captures Kant's idea that moral actions are done for the sake of duty itself. Given that the categorical
imperative captures the idea of duty, Kitcher argues that the FUL would obligate maxims of the form 
``In circumstance C, S will do A in order to G because they would will that and that simultaneously everyone
will do A in order to G in circumstance C." In other words, the motivation becomes the affirmative result
of the FUL for moral action.

While this notion richly captures Kant's idea of acting for duty's own sake, I will not implement it 
because it is not essential to the FUL and because motivation is complex to capture computationally. 
Notice that in order to pass the maxim through the FUL, it suffices to know C, S, A and G. The FUL
derives the purpose that Kitcher bundles into the maxim, so automating the FUL does not require 
including some notion of a purpose. The ``input" to the FUL is the (C, S, A, G) pair. Second, doing
justice to the rich notion of motivation requires modelling the operation of practical reason itself, 
which it outside the scope of this project. My work focuses on the FUL test itself, but future work that 
models the process of practical reason may use my implementation of the FUL as a ``library." Combined 
with a logic of practical reason, an implementation of the FUL can move from evaluating a maxim to 
evaluating an agent's behavior, since that's where ``acting from duty" starts to matter.\<close>

type_synonym maxim = "logos \<Rightarrow> t" \<comment>\<open>I will define a maxim as a function that maps 
 a maxim to a term. To will a maxim is to assign it a truth value at a set of worlds, or, in this logic, 
to make it true at a set of worlds.\<close>

text \<open>\textbf{New Operators}

Because Isabelle is strongly typed, I need to define new operators to handle maxims. These operators 
are similar to DDL's original operators.  \<close>

abbreviation maxim_neg::"maxim \<Rightarrow> maxim" ("\<^emph>\<not>_")
  where "(\<^emph>\<not>A) \<equiv> \<lambda>x::logos. \<^bold>\<not>(A(x))"
abbreviation maxim_and::"maxim \<Rightarrow> maxim \<Rightarrow> maxim" ("_\<^emph>\<and>_")
  where "(A \<^emph>\<and> B) \<equiv> \<lambda>x::logos. ((A(x)) \<^bold>\<and> (B(x)))"
abbreviation maxim_or::"maxim \<Rightarrow> maxim \<Rightarrow> maxim" ("_\<^emph>\<or>_")
  where "(A \<^emph>\<or> B) \<equiv> \<lambda>x::logos. ((A(x)) \<^bold>\<or> (B(x)))"
abbreviation maxim_ob::"maxim \<Rightarrow> maxim" ("\<^emph>O{_}")
  where "\<^emph>O{A} \<equiv> \<lambda>(c, a, g, s). (O{ A(c, a, g, s) | c})"

text \<open>Once again, the notion of permissibility will be useful here.\<close>

abbreviation ddl_permissible::"t\<Rightarrow>t\<Rightarrow>t" ("P{_|_}")
  where "P{A|C} \<equiv> \<^bold>\<not> (O{\<^bold>\<not> A | C})"
abbreviation maxim_permissible::"maxim\<Rightarrow>maxim" ("\<^emph>P {_}")
  where "\<^emph>P{A} \<equiv> \<lambda>(c, a, g, s). P{ A(c, a, g, s) | c}"


(*<*)
end
(*>*)
