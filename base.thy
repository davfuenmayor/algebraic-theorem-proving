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
      Set.supset Set.union Set.inter 
      Orderings.ord_class.less_eq Orderings.ord_class.greater_eq
      Orderings.top_class.top Orderings.bot_class.bot
      Power.power_class.power Power.power_class.power2 Relation.converse Fields.inverse_divide
      Groups.times_class.times Groups.plus_class.plus      
      Groups.one_class.one Groups.zero_class.zero 
      Groups.uminus_class.uminus Groups.minus_class.minus
      Fun.comp
no_notation 
  Set.supset  ("(_/ \<supset> _)" [51, 51] 50) and Set.union (infixl "\<union>" 65) and Set.inter (infixl "\<inter>" 70) and
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

(*Function composition*)
abbreviation(input) fun_comp::"('b \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'a" (infixl "\<circ>" 55)
  where "f \<circ> g \<equiv> \<lambda>x. f (g x)"

end