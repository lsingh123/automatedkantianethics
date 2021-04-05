theory carmojones_DDL
  imports 
    Main 

begin

text "Referencing Benzmueller, Farjami, and Parent's implementation @{cite BFP}"
text "This theory contains the axiomatization of the system and some useful abbreviations."


section "System Definition"

subsection Definitions 

text "This section contains definitions and constants necessary to construct a DDL model."

typedecl i \<comment> \<open> i is the type for a set of possible worlds." \<close>

type_synonym t = "(i \<Rightarrow> bool)" 
\<comment> \<open> t represents a set of DDL formulas.   \<close>
\<comment> \<open> this set is defined by its truth function, mapping the set of worlds to the formula set's truth value. \<close>

\<comment> \<open> accessibility relations map a set of worlds to: \<close>
consts av::"i \<Rightarrow> t" \<comment> \<open>actual versions of that world set\<close>
  \<comment> \<open>these worlds represent what is "open to the agent"\<close>
  \<comment> \<open>for example, the agent eating pizza or pasta for dinner might constitute two different actual worlds\<close>

consts pv::"i \<Rightarrow> t" \<comment> \<open>possible versions of that world set\<close>
  \<comment> \<open>these worlds represent was was "potentially open to the agent"\<close>
 \<comment> \<open>for example, what someone across the world eats for dinner might constitute a possible world, 
 \<comment> \<open>since the agent has no control over this\<close>\<close>

consts ob::"t \<Rightarrow> (t \<Rightarrow> bool)"  \<comment> \<open>set of propositions obligatory in this "context"\<close>
 \<comment> \<open>ob(context)(term) is True if t is obligatory in the context\<close>

consts cw::i  \<comment> \<open>current world\<close>

subsection Axiomatization 

text "This subsection contains axioms. Because the embedding is semantic, these are just constraints on models."
text "This axiomatization comes from @{cite CJDDL} p6 and the HOL embedding defined in Benzmuller and Parent"

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

and ax_5d: "\<forall>X Y Z. ((\<forall>w. Y(w)\<longrightarrow>X(w)) \<and> ob(X)(Y) \<and> (\<forall>w. X(w)\<longrightarrow>Z(w))) 
  \<longrightarrow>ob(Z)(\<lambda>w.(Z(w) \<and> \<not>X(w)) \<or> Y(w))"
\<comment> \<open>If some subset Y of X is in ob(X) then in a larger context Z, any obligatory proposition must either be in Y or in Z-X\<close>

and ax_5e: "\<forall>X Y Z. ((\<forall>w. Y(w)\<longrightarrow>X(w)) \<and> ob(X)(Z) \<and> (\<exists>w. Y(w) \<and> Z(w))) \<longrightarrow> ob(Y)(Z)"
\<comment> \<open>If Z is obligatory in context X, then Z is obligatory in a subset of X called Y, if Z shares some elements with Y\<close>

subsection Abbreviations

text "These abbreviations are defined in @cite{BenzmullerParent} p9"
text "These are all syntactic sugar for HOL expressions, so evaluating these symbols will be light-weight"

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

\<comment> \<open>modal operators\<close>
abbreviation ddlbox::"t\<Rightarrow>t" ("\<box>") 
  where "\<box> A \<equiv> \<lambda>w.\<forall>y. A(y)" 
abbreviation ddldiamond::"t \<Rightarrow> t" ("\<diamond>")
  where "\<diamond>A \<equiv> \<^bold>\<not>(\<box>(\<^bold>\<not>A))"

\<comment> \<open>O$\{B \vert A\}$ can be read as ``B is obligatory in the context A"\<close>
abbreviation ddlob::"t\<Rightarrow>t\<Rightarrow>t" ("O{_|_}")
  where "O{B|A} \<equiv> \<lambda> w. ob(A)(B)"

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

\<comment> \<open>syntactic sugar for a ``monadic" obligation operator\<close>
abbreviation ddltrue::"t" ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation ddlob_normal::"t\<Rightarrow>t" ("O {_}")
  where "(O {A}) \<equiv> (O{A|\<^bold>\<top>}) "

\<comment> \<open>validity\<close>
abbreviation ddlvalid::"t\<Rightarrow>bool" ("\<Turnstile>_")
  where "\<Turnstile>A \<equiv> \<forall>w. A w"
abbreviation ddlvalidcw::"t\<Rightarrow>bool" ("\<Turnstile>\<^sub>c_")
  where "\<Turnstile>\<^sub>cA \<equiv> A cw"

subsection Consistency

text "Consistency is so easy to show in Isabelle!"

lemma True nitpick [satisfy,user_axioms,show_all,format=2] oops 
\<comment> \<open>Nitpick successfully found a countermodel.\<close>
\<comment> \<open>It's not shown in the document printout, hence the oops.\<close>
\<comment> \<open>If you hover over "nitpick" in JEdit, the model will be printed to output.\<close>


end
