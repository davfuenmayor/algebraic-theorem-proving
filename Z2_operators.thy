(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z2_operators
imports Z2_isoA
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
lemma  "CONJ f g \<longleftrightarrow>  CONJ g f" (*by (smt (verit) Meet.elims)*) sorry (*TODO: reconstruction takes too long*)
lemma "DCONJ f g \<longleftrightarrow> DCONJ g f" (*by (smt (verit) Join.elims)*) sorry (*TODO: reconstruction takes too long*)

abbreviation(input)  "CONJ2 f g \<equiv> \<forall>z.  CONJ (f z) (g z)"
abbreviation(input) "DCONJ2 f g \<equiv> \<forall>z. DCONJ (f z) (g z)"


(*Verifies relationships between operations:*)

lemma "RESID (\<lambda>x. \<^bold>\<bottom>) (\<lambda>x. \<^bold>\<top>)" using leq.elims(3) by blast
lemma "RESID (\<lambda>x. x) (\<lambda>x. x)" by simp
lemma "CORESID (\<lambda>x. \<^bold>\<top>) (\<lambda>x. \<^bold>\<bottom>)" by (metis Join.simps(3) Join.simps(4) Meet.simps(1) Meet.simps(3) Z\<^sub>2.exhaust)
lemma "CORESID (\<lambda>x. \<^bold>\<sim>x) (\<lambda>x. \<^bold>\<sim>x)" by (smt (verit, ccfv_SIG) Join.simps(2) Join_maxdef Meet.simps(3) Meet_mindef Negation.elims)

lemma "GALOIS (\<lambda>x. \<^bold>\<top>) (\<lambda>x. \<^bold>\<top>)" using leq.elims(3) by blast
lemma "GALOIS (\<lambda>x. \<^bold>\<sim>x) (\<lambda>x. \<^bold>\<sim>x)" by (metis (full_types, opaque_lifting) Negation.elims Z2_order.refl)
lemma "DGALOIS (\<lambda>x. \<^bold>\<bottom>) (\<lambda>x. \<^bold>\<bottom>)" by simp
lemma "DGALOIS (\<lambda>x. \<^bold>\<sim>x) (\<lambda>x. \<^bold>\<sim>x)" by (metis Negation.simps(1) leq.elims(2) leq.elims(3))

lemma "CONJ (\<lambda>x. \<^bold>\<bottom>) (\<lambda>x. \<^bold>\<bottom>)" using Meet.elims by blast
lemma "CONJ (\<lambda>x. x) (\<lambda>x. x)" by simp
lemma "DCONJ (\<lambda>x. \<^bold>\<top>) (\<lambda>x. \<^bold>\<top>)" using Join.elims by blast
lemma "DCONJ (\<lambda>x. x) (\<lambda>x. x)" by simp

lemma "RESID2 (\<^bold>\<and>) (\<^bold>\<rightarrow>)" by (simp add: resid_law1)
lemma "RESID2 (\<^bold>\<rightharpoonup>) (\<^bold>\<or>)" by (simp add: resid_law2)

lemma "CORESID2 (\<^bold>\<up>) (\<^bold>\<leftharpoonup>)" sorry (*TODO: reconstruction takes too long*)
lemma "CORESID2 (\<^bold>\<leftarrow>) (\<^bold>\<down>)" sorry (*TODO: reconstruction takes too long*)

end