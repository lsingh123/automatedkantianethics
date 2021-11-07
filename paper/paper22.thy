(*<*) theory paper22 (*>*)
(*<*)  imports Main (*>*)

(*<*) begin (*>*) 

subsection \<open>Isabelle/HOL Implementation \label{sec:isabelle}\<close>

text \<open>The final component of my project is the automated theorem prover I use to automate my formalization.
Isabelle/HOL is an interactive proof assistant built on Haskell and Scala @{cite isabelle}. It 
allows the user to define types, functions, definitions, and axiom systems. It has built-in support for both
automatic and interactive/manual theorem proving. 

I started my project by reimplementing Benzmueller, Farjami, and Parent's implementation 
of DDL in Isabelle/HOL \cite{BFP, logikey}. This helped me learn how to use Isabelle/HOL, and the implementation showcased in the 
next few sections demonstrates the power of Isabelle.

Benzmueller, Farjami, and Parent use a shallow semantic embedding. This kind of embedding models the semantics of DDL as 
constants in HOL and axioms as constraints on DDL models. This document will contain a subset of my 
implementation that is particularly interesting and relevant to understanding the rest of the project. 
For the complete implementation, see the source code in @{file paper22.thy}.
\<close>

subsubsection "System Definition"

text \<open>The first step in embedding a logic in Isabelle is defining the relevant terms and types.\<close>

typedecl i \<comment> \<open> i is the type for a set of worlds.\<close>

type_synonym t = "(i \<Rightarrow> bool)" \<comment> \<open> t represents a set of DDL formulae. \<close>
\<comment> \<open>A set of formulae is defined by its truth value at a set of worlds. For example, the set \{True\}
would be true at any set of worlds.\<close>

(*<*)
\<comment> \<open> accessibility relations map a set of worlds to: \<close>
consts av::"i \<Rightarrow> t" \<comment> \<open>actual versions of that world set\<close>
  \<comment> \<open>these worlds represent what is "open to the agent"\<close>
  \<comment> \<open>for example, the agent eating pizza or pasta for dinner might constitute two different actual worlds\<close>

consts pv::"i \<Rightarrow> t" \<comment> \<open>possible versions of that world set\<close>
  \<comment> \<open>these worlds represent was was "potentially open to the agent"\<close>
 \<comment> \<open>for example, what someone across the world eats for dinner might constitute a possible world, 
 \<comment> \<open>since the agent has no control over this\<close>\<close>
(*>*)

text \<open>The main accessibility relation that I will use is the $ob$ relation:\<close>

consts ob::"t \<Rightarrow> (t \<Rightarrow> bool)"  \<comment> \<open>set of propositions obligatory in this context\<close>
 \<comment> \<open>ob(context)(term) is True if the term is obligatory in this context\<close>

(*<*)consts cw::i  \<comment> \<open>current world\<close>(*>*)

subsubsection Axiomatization 

text \<open>For a semantic embedding, axioms are modelled as restrictions on models of the system. In this case,
a model is specificied by the relevant accessibility relations, so it suffices to place conditions on 
the accessibility relations. These axioms can be quite unweildy, so luckily I was able to lift BFP's 
implementation of Carmo and Jones's original axioms directly \citep{BFP}. Here's an example of an axiom:\<close>

(*<*)
axiomatization where
ax_3a: "\<forall>w.\<exists>x. av(w)(x)" 
 \<comment> \<open>every world has some actual version\<close>

and ax_4a: "\<forall>w x. av(w)(x) \<longrightarrow> pv(w)(x)" 
\<comment> \<open>all actual versions of a world are also possible versions of it\<close>

and ax_4b: "\<forall>w. pv(w)(w)"
\<comment> \<open>every world is a possible version of itself\<close>

and ax_5a: "\<forall>X.\<not>ob(X)(\<lambda>w. False)" 
\<comment> \<open>in any arbitrary context X, something will be obligatory\<close>

and ax_5b: "\<forall>X Y Z. (\<forall>w. ((X(w) \<and> Y(w)) \<longleftrightarrow> (X(w) \<and> Z(w)))) \<longrightarrow> (ob(X)(Y) \<longleftrightarrow> ob(X)(Z))" \<comment> \<open>note that X(w) denotes w is a member of X\<close>
\<comment> \<open>X, Y, and Z are sets of formulas\<close>
\<comment> \<open>If X $\cap$ Y = X $\cap$ Z then the context X obliges Y iff it obliges Z\<close>

\<comment> \<open>ob(X)($\lambda$ w. Fw) can be read as F $\in$ ob(X)\<close>

and ax_5c2: "\<forall>X Y Z. (((\<exists>w. (X(w) \<and> Y(w) \<and> Z(w))) \<and> ob(X)(Y) \<and> ob(X)(Z))) \<longrightarrow> ob(X)(\<lambda>w. Y(w) \<and> Z(w))"
(*>*)

and ax_5d: "\<forall>X Y Z. ((\<forall>w. Y(w)\<longrightarrow>X(w)) \<and> ob(X)(Y) \<and> (\<forall>w. X(w)\<longrightarrow>Z(w))) 
  \<longrightarrow>ob(Z)(\<lambda>w.(Z(w) \<and> \<not>X(w)) \<or> Y(w))"
\<comment> \<open>If some subset Y of X is obligatory in the context X, then in a larger context Z,
 any obligatory proposition must either be in Y or in Z-X. Intuitively, expanding the context can't 
cause something unobligatory to become obligatory, so the obligation operator is monotonically increasing
 with respect to changing contexts.\<close>

(*<*)
and ax_5e: "\<forall>X Y Z. ((\<forall>w. Y(w)\<longrightarrow>X(w)) \<and> ob(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> ob(Y)(Z)"
\<comment> \<open>If Z is obligatory in context X, then Z is obligatory in a subset of X called Y, if Z shares some elements with Y\<close>
(*>*)

subsubsection Syntax

text \<open>The syntax that I will work with is defined as abbreviations. Each DDL operator is represented 
as a HOL formula. Isabelle automatically unfolds formulae defined with the @{verbatim abbreviation} command 
whenever they are applied. While the shallow embedding is performant (because it uses Isabelle's original 
syntax tree), abbreviations may hurt performance. In some complicated proofs, we want to control definition
unfolding. Benzmueller and Parent told me that the performance cost of abbreviations can 
be mitigated using a definition instead.\<close>

(*<*)
\<comment> \<open>propositional logic symbols\<close>
abbreviation ddlneg::"t\<Rightarrow>t" ("\<^bold>\<not>") 
  where "\<^bold>\<not>A \<equiv> \<lambda>w. \<not>A(w)" 
abbreviation ddlor::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<or>_") 
  where "A \<^bold>\<or> B \<equiv> \<lambda>w. (A(w) \<or> B(w))"
abbreviation ddland::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<and>_")
  where "A\<^bold>\<and> B \<equiv> \<lambda>w. (A(w) \<and> B(w))"
abbreviation ddlif::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<rightarrow>_")
  where "A\<^bold>\<rightarrow>B \<equiv> (\<lambda>w. A(w)\<longrightarrow>B(w))"
abbreviation ddlequiv::"t\<Rightarrow>t\<Rightarrow>t" ("_\<^bold>\<equiv>_")
  where "(A\<^bold>\<equiv>B) \<equiv> ((A\<^bold>\<rightarrow>B) \<^bold>\<and> ( B\<^bold>\<rightarrow>A))"
(*>*)

text \<open>Modal operators will be useful for my purposes, but the implementation is pretty standard.\<close>
abbreviation ddlbox::"t\<Rightarrow>t" ("\<box>") 
  where "\<box> A \<equiv> \<lambda>w.\<forall>y. A(y)" 
abbreviation ddldiamond::"t \<Rightarrow> t" ("\<diamond>")
  where "\<diamond>A \<equiv> \<^bold>\<not>(\<box>(\<^bold>\<not>A))"

text \<open>The most important operator for our purposes is the obligation operator.\<close>
abbreviation ddlob::"t\<Rightarrow>t\<Rightarrow>t" ("O{_|_}")
  where "O{B|A} \<equiv> \<lambda> w. ob(A)(B)"
\<comment> \<open>O$\{B \vert A\}$ can be read as ``B is obligatory in the context A"\<close>

(*<*)
\<comment> \<open>modal symbols over the actual and possible worlds relations\<close>
abbreviation ddlboxa::"t\<Rightarrow>t" ("\<box>\<^sub>a")
  where "\<box>\<^sub>aA \<equiv> \<lambda>x.\<forall>y. (\<not> av(x)(y) \<or> A(y))"
abbreviation ddldiamonda::"t\<Rightarrow>t" ("\<diamond>\<^sub>a")
  where "\<diamond>\<^sub>aA \<equiv> \<^bold>\<not>(\<box>\<^sub>a(\<^bold>\<not>A))"
abbreviation ddlboxp::"t\<Rightarrow>t" ("\<box>\<^sub>p")
  where "\<box>\<^sub>pA \<equiv> \<lambda>x.\<forall>y. (\<not> pv(x)(y) \<or> A(y))"
abbreviation ddldiamondp::"t\<Rightarrow>t" ("\<diamond>\<^sub>p")
  where "\<diamond>\<^sub>pA \<equiv> \<^bold>\<not>(\<box>\<^sub>a(\<^bold>\<not>A))"

\<comment> \<open>obligation symbols over the actual and possible worlds\<close>
abbreviation ddloba::"t\<Rightarrow>t" ("O\<^sub>a")
  where "O\<^sub>a A \<equiv> \<lambda>x. ob(av(x))(A) \<and> (\<exists>y.(av(x)(y) \<and> \<not>A(y)))"
abbreviation ddlobp::"t\<Rightarrow>t" ("O\<^sub>p")
  where "O\<^sub>p A \<equiv> \<lambda>x. ob(pv(x))(A) \<and> (\<exists>y.(pv(x)(y) \<and> \<not>A(y)))"
(*>*)

text \<open>While DDL is powerful because of its support for a dyadic obligation operator, in many cases 
we need a monadic obligation operator. Below is some syntactic sugar for a monadic obligation operator.\<close>
abbreviation ddltrue::"t" ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation ddlfalse::"t" ("\<^bold>\<bottom>")
  where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation ddlob_normal::"t\<Rightarrow>t" ("O {_}")
  where "(O {A}) \<equiv> (O{A|\<^bold>\<top>}) "
\<comment>\<open>Intuitively, the context \texttt{True} is the widest context possible because \texttt{True} holds at all worlds.\<close>

text \<open>Validity will be useful when discussing metalogical/ethical properties.\<close>
abbreviation ddlvalid::"t\<Rightarrow>bool" ("\<Turnstile>_")
  where "\<Turnstile>A \<equiv> \<forall>w. A w"

(*<*)
abbreviation ddlvalidcw::"t\<Rightarrow>bool" ("\<Turnstile>\<^sub>c_")
  where "\<Turnstile>\<^sub>cA \<equiv> A cw"
(*>*)



subsubsection "Syntactic Properties"

text \<open>One way to show that a semantic embedding is complete is to show that the syntactic specification
of the theory (axioms) are valid for this semantics - so to show that every axiom holds at every 
world. Benzmueller, Farjami, and Parent provide a complete treatment of the completeness of their embedding, but I 
will include selected axioms that are particularly interesting here. This section also demonstrates many
of the relevant features of Isabelle/HOL for my project.\<close>

text \<open>\textbf{Consistency}\<close>
lemma True nitpick [satisfy,user_axioms,format=2] by simp
\<comment> \<open>Isabelle has built-in support for Nitpick, a model checker. 
Nitpick successfully found a model satisfying these axioms so the system is consistent.\<close>
\<comment>\<open> \color{blue} Nitpick found a model for card i = 1:

  Empty assignment \color{black}\<close>

text \<open>Nitpick @{cite nitpick} can generate models or countermodels, so it's useful to falsify potential
theorems, as well as to show consistency. {\color{red} by simp} indicates the proof method. In this 
case, {\color{red} simp} indicates the Simplification proof method, which involves unfolding definitions
and applying theorems directly. HOL has $True$ as a theorem, which is why this theorem was so easy to prove.\<close>

(*<*)
end
(*>*)
