(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory base
imports HOL.Nitpick HOL.Sledgehammer "HOL-Eisbach.Eisbach"
begin

declare[[smt_timeout=60]]
(* declare[[show_types]] *)
declare[[syntax_ambiguity_warning=false]]
sledgehammer_params[isar_proof=false,abduce=0,falsify=false]
(*Nitpick settings*)
nitpick_params[assms=true,user_axioms=true,box=false,show_all,expect=genuine,max_potential=0,max_genuine=1,format=3]

(*************** Hide notation/symbols from the library  *****************)
hide_const(open) 
      Set.supset Set.subset Set.supset_eq Set.subset_eq Set.union Set.inter 
      Orderings.ord_class.less_eq Orderings.ord_class.greater_eq
      Orderings.top_class.top Orderings.bot_class.bot
      Power.power_class.power Power.power_class.power2 Relation.converse Fields.inverse_divide
      Groups.times_class.times Groups.plus_class.plus      
      Groups.one_class.one Groups.zero_class.zero 
      Groups.uminus_class.uminus Groups.minus_class.minus
      Fun.comp
no_notation 
  Set.supset  ("(_/ \<supset> _)" [51, 51] 50) and Set.subset  ("(_/ \<subset> _)" [51, 51] 50) and
  Set.subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) and Set.subset_eq ("'(\<subseteq>')") and
  Set.supset_eq  ("(_/ \<supseteq> _)" [51, 51] 50) and Set.supset_eq ("'(\<supseteq>')") and
  Set.union (infixl "\<union>" 65) and Set.inter (infixl "\<inter>" 70) and
  Power.power_class.power (infixr "^" 80) and Power.power_class.power2  ("(_\<^sup>2)" [1000] 999) and
  Relation.converse ("(_\<inverse>)" [1000] 999) and Fields.inverse_divide (infixl "'/" 70) and 
  Orderings.ord_class.less_eq ("'(\<le>')") and Orderings.ord_class.less_eq ("(_/ \<le> _)"  [51, 51] 50) and
  Orderings.ord_class.greater_eq (infix "\<ge>" 50) and 
  Orderings.top_class.top ("\<top>") and Orderings.bot_class.bot ("\<bottom>") and
  Groups.times_class.times (infixl "*" 70) and Groups.plus_class.plus (infixl "+" 65) and 
  Groups.one_class.one  ("1") and Groups.zero_class.zero  ("0") and
  Groups.uminus_class.uminus ("- _" [81] 80) and Groups.minus_class.minus  (infixl "-" 65) and
  Fun.comp (infixl "\<circ>" 55)



(**********************  Alternative notations ***************************)

(*Introduce alias for type bool*)
type_synonym o = bool ("o")

(*We introduce (pedagogically convenient) alternative notation for HOL logical constants*)
notation HOL.All ("\<forall>") 
notation HOL.Ex  ("\<exists>")

notation(input) HOL.Not ("'(\<not>')")

notation HOL.True  ("\<top>")
notation HOL.False ("\<bottom>")

notation HOL.implies (infixr "\<rightarrow>" 25)
notation HOL.iff (infixr "\<leftrightarrow>" 25)

(*Let us introduce some useful abbreviations*)
abbreviation(input) seilpmi  (infixl "\<leftarrow>" 25) (*reversed implication (for convenience)*)
  where "A \<leftarrow> B \<equiv> B \<rightarrow> A"
abbreviation(input) diff::"o \<Rightarrow> o \<Rightarrow> o" (infixr "\<leftharpoonup>" 51) 
  where "A \<leftharpoonup> B \<equiv> A \<and> \<not>B" (** difference*)
abbreviation ffid::"o \<Rightarrow> o \<Rightarrow> o" (infixr "\<rightharpoonup>" 51) (*reversed difference (for convenience)*)
  where "A \<rightharpoonup> B \<equiv> B \<leftharpoonup> A"
abbreviation(input) nand::"o \<Rightarrow> o \<Rightarrow> o" (infixr "\<up>" 54) (*cf. Sheffer's 'stroke'*)
  where "A \<up> B \<equiv> \<not>(A \<and> B)"
abbreviation(input) nor::"o \<Rightarrow> o \<Rightarrow> o" (infixr "\<down>" 53) (*cf. Quine's 'dagger'*)
  where "A \<down> B \<equiv> \<not>(A \<or> B)"

(*Add (binder) notation for definite descriptions (incl. binder notation)*)
notation(input) HOL.The ("\<iota>")
notation(input) HOL.The (binder "\<iota>" 10)

(*Add (binder) notation for indefinite descriptions aka. Hilbert's epsilon or choice operator*)
notation(input) Hilbert_Choice.Eps ("\<epsilon>")
notation(input) Hilbert_Choice.Eps (binder "\<epsilon>" 10)

(*Sanity check*)
lemma "(\<iota> x. A x) = (THE x. A x)" ..
lemma "(\<epsilon> x. A x) = (SOME x. A x)" ..


subsection \<open>A minimal theory of functions, sets and relations\<close>

type_synonym ('a)Set = "'a \<Rightarrow> o" ("Set(_)" [99])
type_synonym ('a,'b)Rel = "'a \<Rightarrow> 'b \<Rightarrow> o" ("Rel'(_,_')" [99])

(*By extension/enumeration:*)
abbreviation(input) oneElem::"'a \<Rightarrow> Set('a)" ("{_}")
  where \<open>{a} \<equiv> \<lambda>x. a = x\<close>  (* i.e. (=)a *)
abbreviation(input) twoElem::"'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("{_,_}")
  where \<open>{a,b} \<equiv> \<lambda>x. a = x \<or> b = x\<close>
abbreviation(input) threeElem::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("{_,_,_}")
  where \<open>{a,b,c} \<equiv> \<lambda>x. a = x \<or> b = x \<or> c = x\<close>

(*Two useful functions with boolean codomain: The "universal" and the "empty" set.*)
abbreviation(input) univ::"Set('a)" ("\<UU>")
  where "\<UU> \<equiv> \<lambda>x. \<top>"
abbreviation(input) empty::"Set('a)" ("\<emptyset>")
  where "\<emptyset> \<equiv> \<lambda>x. \<bottom>"

(*We can also define some binary operations on sets *)
abbreviation(input) inter::"Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)" (infixr "\<inter>" 54) 
  where "A \<inter> B \<equiv> \<lambda>x. A x \<and> B x"
abbreviation(input) union::"Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)" (infixr "\<union>" 53) 
  where "A \<union> B \<equiv> \<lambda>x. A x \<or> B x"

(*Union and intersection can be generalized to the 'infinitary' case (i.e. operating on arbitrary sets of sets)*)
abbreviation(input) biginter::"Set(Set('a)) \<Rightarrow> Set('a)" ("\<Inter>")
  where "\<Inter>S \<equiv> \<lambda>x. \<forall>A. S A \<rightarrow> A x"
abbreviation(input) bigunion::"Set(Set('a)) \<Rightarrow> Set('a)" ("\<Union>") 
  where "\<Union>S \<equiv> \<lambda>x. \<exists>A. S A  \<and>  A x"

(*The algebra of sets is ordered by the standard subset (endo)relation, as defined below.*)
abbreviation(input) subset::"Rel(Set('a),Set('a))" (infixr "\<subseteq>" 51) 
  where "A \<subseteq> B \<equiv> \<forall>x. A x \<rightarrow> B x"

(*Given a function f we can obtain its (functional) range as the set of those objects 'b' in the 
 codomain that are the image of some object 'a' (i.e. have a non-empty preimage) under the function f.*)
definition funRange::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
  where "funRange f \<equiv> \<lambda>b. \<exists>a. f a = b"

(*Function composition*)
abbreviation(input) fun_comp::"('b \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'a" (infixl "\<circ>" 55)
  where "f \<circ> g \<equiv> \<lambda>x. f (g x)"

(*Some relevant properties of (endo-)relations *)
abbreviation(input) "transitive R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
abbreviation(input) "reflexive R \<equiv> \<forall>x. R x x"
abbreviation(input) "antisymmetric R \<equiv> \<forall>x y. R x y \<and> R y x \<longrightarrow> x = y"

(*These operators generalize the notion of upper/lower bounds of a set (wrt. relation R).*)
definition upper::"Rel('a,'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("_\<Up>")
  where  "R\<Up>  \<equiv> \<lambda>A. \<lambda>b. \<forall>a. A a \<longrightarrow> R a b"
definition lower::"Rel('a,'b) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("_\<Down>")
  where  "R\<Down>  \<equiv> \<lambda>B. \<lambda>a. \<forall>b. B b \<longrightarrow> R a b"

(*The set of least (resp. greatest) elements of a set A wrt. a relation R*)
definition least::"Rel('a,'a) \<Rightarrow> (Set('a) \<Rightarrow> Set('a))" ("_-least")
  where \<open>R-least \<equiv> \<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R m x)\<close>
definition greatest::"Rel('a,'a) \<Rightarrow> (Set('a) \<Rightarrow> Set('a))" ("_-greatest")
  where \<open>R-greatest \<equiv> \<lambda>A. \<lambda>m. A m \<and> (\<forall>x. A x \<longrightarrow> R x m)\<close>

(*The (set of) least upper-bound(s) and greatest lower-bound(s) for a given set*)
abbreviation(input) lub::"Rel('a,'a) \<Rightarrow> (Set('a) \<Rightarrow> Set('a))" ("_-lub")
  where "R-lub \<equiv> \<lambda>A. R-least(R\<Up>A)"
abbreviation(input) glb::"Rel('a,'a) \<Rightarrow> (Set('a) \<Rightarrow> Set('a))" ("_-glb")
  where "R-glb \<equiv> \<lambda>A. R-greatest(R\<Down>A)"

(*Some convenient properties of set operations*)
abbreviation(input) "MONO \<phi> \<equiv> \<forall>x y. x \<subseteq> y \<longrightarrow> \<phi> x \<subseteq> \<phi> y" (*monotonicity*)
abbreviation(input) "EXP \<phi> \<equiv> \<forall>x. x \<subseteq> \<phi> x" (*expansiveness/extensiveness/increasingness*)
abbreviation(input) "IDEM \<phi> \<equiv> \<forall>x. \<phi>(\<phi> x) = \<phi> x" (*idempotency*)

definition "Closure \<phi> \<equiv> MONO \<phi> \<and> EXP \<phi> \<and> IDEM \<phi>"

end