(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z3_operators
imports Z3_order102
begin


(*Two values are called 'contrary' when they 'meet' at the bottom *)
abbreviation(input) contrary (infixr "\<plusminus>" 52)
  where "A \<plusminus> B \<equiv> A \<^bold>\<and> B = \<^bold>\<bottom>"
(*Dually, we call two values 'subcontrary' when they 'join' at the top *)
abbreviation(input) subcontrary (infixr "\<minusplus>" 53)
  where "A \<minusplus> B \<equiv> A \<^bold>\<or> B = \<^bold>\<top>"

(*Two values are said to be coresiduated (aka. coadjoint) when: *)
abbreviation(input) "CORESID f g \<equiv> \<forall>x y. f x \<minusplus> y \<longleftrightarrow> x \<plusminus> g y"
abbreviation(input) "CORESID2 f g \<equiv> \<forall>z. CORESID (f z) (g z)"

lemma "RESID f g \<longleftrightarrow> CORESID f g" nitpick oops
lemma "RESID f g \<longleftrightarrow> CORESID g f" nitpick oops

(*Let us recall, for the binary case: *)
lemma   "RESID2 f g = (\<forall>x y z. (f z x \<le> y) \<longleftrightarrow> (x \<le> g z y))" by blast
lemma "CORESID2 f g = (\<forall>x y z. (f z x \<minusplus> y) \<longleftrightarrow> (x \<plusminus> g z y))" by blast

(*Two values can also be said to be (dual-)Galois-adjoint (aka form a (dual-)Galois connection)*)
abbreviation(input)  "GALOIS f g \<equiv> \<forall>x y. y \<le> f x \<longleftrightarrow> x \<le> g y"
abbreviation(input) "DGALOIS f g \<equiv> \<forall>x y. f x \<le> y \<longleftrightarrow> g y \<le> x"

(*The relation of being (dual-)Galois-adjoint is in fact symmetric.*)
lemma  "GALOIS f g \<longleftrightarrow>  GALOIS g f" by blast
lemma "DGALOIS f g \<longleftrightarrow> DGALOIS g f" by blast

abbreviation(input)  "GALOIS2 f g \<equiv> \<forall>z. GALOIS (f z) (g z)"
abbreviation(input) "DGALOIS2 f g \<equiv> \<forall>z. DGALOIS (f z) (g z)"

(*Two values can also be said to be (dual-)conjugated *)
abbreviation(input)  "CONJ f g \<equiv> \<forall>x y. f x \<plusminus> y \<longleftrightarrow> x \<plusminus> g y"
abbreviation(input) "DCONJ f g \<equiv> \<forall>x y. f x \<minusplus> y \<longleftrightarrow> x \<minusplus> g y"

(*The (dual-)conjugation relation is symmetric too.*)
lemma  "CONJ f g \<longleftrightarrow>  CONJ g f" sorry (*TODO: reconstruction takes too long*)
lemma "DCONJ f g \<longleftrightarrow> DCONJ g f" sorry (*TODO: reconstruction takes too long*)

abbreviation(input)  "CONJ2 f g \<equiv> \<forall>z.  CONJ (f z) (g z)"
abbreviation(input) "DCONJ2 f g \<equiv> \<forall>z. DCONJ (f z) (g z)" 


(*Verifies relationships between operations:*)

lemma "RESID (\<lambda>x. \<^bold>\<bottom>) (\<lambda>x. \<^bold>\<top>)" using leq.elims(3) by auto
lemma "RESID (\<lambda>x. x) (\<lambda>x. x)" by simp
lemma "RESID \<C>\<^sub>n \<I>\<^sub>n" sorry (*TODO: reconstruction takes too long*)
lemma "CORESID (\<lambda>x. \<^bold>\<top>) (\<lambda>x. \<^bold>\<bottom>)" by (metis Join_maxdef Meet_mindef Z\<^sub>3.simps(6) leq.elims(2))
lemma "CORESID (\<lambda>x. \<^bold>\<sim>x) (\<lambda>x. \<^bold>\<sim>x)" by (smt (verit, best) Join.simps(1) Join.simps(2) Join.simps(3) Join.simps(4) Join.simps(5) Join.simps(6) Join.simps(7) Join.simps(8) Join.simps(9) Meet.simps(1) Meet.simps(2) Meet.simps(3) Meet.simps(4) Meet.simps(5) Meet.simps(6) Meet.simps(7) Meet.simps(8) Meet.simps(9) Negation.elims Negation.simps(1) Negation.simps(3))
lemma "CORESID \<^bold>\<smile> \<^bold>\<frown>" by (smt (verit, del_insts) ClosureA.elims Join.simps(4) Join.simps(5) Join.simps(6) Join.simps(7) Join.simps(8) Join.simps(9) Meet.simps(2) Meet.simps(3) Meet.simps(5) Meet.simps(6) Meet.simps(8) Meet.simps(9) NegationC.simps(1) NegationC.simps(2) NegationC.simps(3) NegationI.simps(1) NegationI.simps(2) NegationI.simps(3))

lemma "GALOIS (\<lambda>x. \<^bold>\<top>) (\<lambda>x. \<^bold>\<top>)" using leq.elims(3) by blast
lemma "GALOIS (\<lambda>x. \<^bold>\<sim>x) (\<lambda>x. \<^bold>\<sim>x)" by (smt (verit, best) Negation.elims Negation.simps(3) Z3_order102.antisym Z3_order102.linear leq.simps(1) leq.simps(2))
lemma "GALOIS \<^bold>\<smile> \<^bold>\<smile>" by (metis NegationI.elims NegationI.simps(3) Z3_order102.antisym leq.simps(1) leq.simps(2) leq.simps(3))
lemma "DGALOIS (\<lambda>x. \<^bold>\<bottom>) (\<lambda>x. \<^bold>\<bottom>)" by simp
lemma "DGALOIS (\<lambda>x. \<^bold>\<sim>x) (\<lambda>x. \<^bold>\<sim>x)" by (metis (mono_tags, lifting) Negation.elims Z\<^sub>3.distinct(5) Z\<^sub>3.simps(2) Z\<^sub>3.simps(4) leq.elims(2) leq.elims(3))
lemma "DGALOIS \<^bold>\<frown> \<^bold>\<frown>" by (smt (verit, best) NegationC.elims NegationC.simps(1) Z3_order102.antisym Z3_order102.refl leq.elims(3) leq.simps(7))

lemma "CONJ (\<lambda>x. \<^bold>\<bottom>) (\<lambda>x. \<^bold>\<bottom>)" by (simp add: Meet_mindef Z3_order102.antisym)
lemma "CONJ (\<lambda>x. x) (\<lambda>x. x)" by simp
lemma "CONJ \<C>\<^sub>n \<C>\<^sub>n" by (smt (verit) ClosureN.simps(1) ClosureN.simps(2) ClosureN.simps(3) InteriorA.elims Meet.simps(2) Meet.simps(3) Meet.simps(4) Meet.simps(5) Meet.simps(6) Meet.simps(7) Meet.simps(8))
lemma "DCONJ (\<lambda>x. \<^bold>\<top>) (\<lambda>x. \<^bold>\<top>)" using Join.elims by blast
lemma "DCONJ (\<lambda>x. x) (\<lambda>x. x)" by simp
lemma "DCONJ \<I>\<^sub>n \<I>\<^sub>n" by (smt (verit, del_insts) InteriorN.elims Join.simps(2) Join.simps(3) Join.simps(4) Join.simps(6) Join.simps(7) Join.simps(8) Join.simps(9) Z\<^sub>3.distinct(1))

lemma "RESID2 (\<^bold>\<and>) (\<^bold>\<rightarrow>)" using resid_law1 by auto
lemma "RESID2 (\<^bold>\<rightharpoonup>) (\<^bold>\<or>)" using resid_law2 by blast

lemma "CORESID2 (\<lambda>x y. \<^bold>\<sim>(x \<^bold>\<and> y)) (\<lambda>x y. (x \<^bold>\<and> (\<^bold>\<sim>y)))" sorry (*TODO: reconstruction takes too long*)
lemma "CORESID2 (\<lambda>x y. (x \<^bold>\<or> (\<^bold>\<sim>y))) (\<lambda>x y. \<^bold>\<sim>(x \<^bold>\<or> y))" sorry (*TODO: reconstruction takes too long*)

end