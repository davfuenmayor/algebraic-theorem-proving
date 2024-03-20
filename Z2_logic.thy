(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z2_logic
imports Z2_order CAS_integration
begin

section \<open>Logical reasoning by polynomial manipulation in Z2\<close>


subsection \<open>Logical validity in algebraic terms\<close>

(*The notions of logical validity and invalidity are stated algebraically as follows: *)
abbreviation(input) Validity::"Z\<^sub>2 \<Rightarrow> o" ("\<turnstile> _" 49) 
  where "\<turnstile> C  \<equiv> C = \<^bold>\<top>"
abbreviation(input) Invalidity::"Z\<^sub>2 \<Rightarrow> o" ("\<turnstile>\<^sup>n _" 49) 
  where "\<turnstile>\<^sup>n C \<equiv> C = \<^bold>\<bottom>"


subsection \<open>Logical consequence in algebraic terms\<close>

(*The notion of logical consequence corresponds to what is known in the literature as 'local' 
  (aka. 'degree-preserving') consequence *)
definition ConsequenceLocal::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> o" (infixr "\<turnstile>" 10) 
  where "A \<turnstile> C \<equiv> A \<le> C"

(*The (dual-)deduction-metatheorem, (d)DMT, allows for switching between consequence and (in)validity*)
lemma DMT:  "(A \<turnstile> B) \<longleftrightarrow> \<turnstile>  A \<^bold>\<rightarrow> B" 
  unfolding ConsequenceLocal_def by (smt (verit) Implication.simps leq.elims Z\<^sub>2.distinct)
lemma dDMT: "(A \<turnstile> B) \<longleftrightarrow> \<turnstile>\<^sup>n A \<^bold>\<leftharpoonup> B" 
  unfolding ConsequenceLocal_def by (smt (verit) DualImplication.simps leq.elims Z\<^sub>2.distinct)

(*It is also possible to define what is known in the literature as 'global' (aka. 'truth-preserving')
 consequence, which ends up being equivalent (by bivalence) to the previous definition*)
definition ConsequenceGlobal::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> o" (infixr "\<turnstile>\<^sub>g" 10)
  where "A \<turnstile>\<^sub>g C \<equiv> \<turnstile> A \<longrightarrow> \<turnstile> C"

lemma ConsequenceGlobal_char: "(A \<turnstile>\<^sub>g C) = (A \<turnstile> C)"
  by (smt (verit) ConsequenceGlobal_def ConsequenceLocal_def Z\<^sub>2.simps leq.elims)

(*The definitions below draw from the fact (cite) that global consequence in m-valued logics, 
 for a prime-power m, can be stated in terms of ideal membership in GF(m), and viceversa.*)
definition idealMembership1::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> o" ("_ in <_>")
  where "P in <Q> \<equiv> Q + \<^bold>\<top> \<turnstile>\<^sub>g P + \<^bold>\<top>"
definition idealMembership2::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> o" ("_ in <_,_>")
  where "P in <Q\<^sub>1,Q\<^sub>2> \<equiv> (Q\<^sub>1 + \<^bold>\<top> \<^bold>\<and> Q\<^sub>2 + \<^bold>\<top>) \<turnstile>\<^sub>g P + \<^bold>\<top>"
definition idealMembership3::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> o" ("_ in <_,_,_>")
  where "P in <Q\<^sub>1,Q\<^sub>2,Q\<^sub>3> \<equiv> (Q\<^sub>1 + \<^bold>\<top> \<^bold>\<and> Q\<^sub>2 + \<^bold>\<top> \<^bold>\<and> Q\<^sub>3 + \<^bold>\<top>) \<turnstile>\<^sub>g P + \<^bold>\<top>"

(*The equalities below conveniently transform global-consequence to ideal-membership checking (IMC)*)
lemma ConsequenceGlobal_imc: "(A \<turnstile>\<^sub>g C) = (C - \<^bold>\<top> in < A - \<^bold>\<top> >)" 
  unfolding idealMembership1_def by (smt (z3) Addition.simps Z\<^sub>2.exhaust)
lemma ConsequenceGlobal_imc2: "(A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<turnstile>\<^sub>g C) = (C - \<^bold>\<top> in < A\<^sub>1 - \<^bold>\<top>, A\<^sub>2 - \<^bold>\<top> >)" 
  unfolding idealMembership2_def by (smt (z3) Addition.simps Z\<^sub>2.exhaust)
lemma ConsequenceGlobal_imc3: "(A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<and> A\<^sub>3 \<turnstile>\<^sub>g C) = (C - \<^bold>\<top> in < A\<^sub>1 - \<^bold>\<top>, A\<^sub>2 - \<^bold>\<top>, A\<^sub>3 - \<^bold>\<top> >)" 
  unfolding idealMembership3_def by (smt (z3) Addition.simps Z\<^sub>2.exhaust)


subsection \<open>Solving logic problems with Sage\<close>

(*Step-by-step: how to solve a local consequence problem algebraically (with Sage)*)
lemma "\<^bold>\<sim>(x \<^bold>\<and> y) \<turnstile> (\<^bold>\<sim>x \<^bold>\<or> \<^bold>\<sim>y)"
  unfolding DMT (*apply deduction metatheorem (optional)*)
  unfolding polydefs (*expand logical connectives as their polynomial representations*)
  apply(polysimp "''PolynomialRing(GF(2),{x,y})''") (*simplify given polynomial over the field Z\<^sub>2[x,y] *)
  sorry (*proven because the simplified expression trivially holds*) (*TODO: do this automatically via oracle*)

(*Step-by-step: how to solve a global consequence problem algebraically (with Sage)*)
lemma "\<^bold>\<sim>(x \<^bold>\<and> y) \<turnstile>\<^sub>g (\<^bold>\<sim>x \<^bold>\<or> \<^bold>\<sim>y)"
  unfolding ConsequenceGlobal_imc (*apply transformation to ideal-membership checking *)
  unfolding polydefs (*expand logical connectives as their polynomial representations*)
  apply(polyimc "''PolynomialRing(GF(2),{x,y})''") (*check ideal-membership over the field Z\<^sub>2[x,y] *)
  sorry (*proven because the simplified expression trivially holds*) (*TODO: do this automatically via oracle*)

(*Configuration string indicating that we work with polynomials over Z\<^sub>2 using variables among {x,y,z,w} *)
abbreviation(input) \<open>Z2config \<equiv> ''PolynomialRing(GF(2), {x,y,z,w})''\<close>
(*Furthermore, we can use Eisbach to introduce convenient proof methods*)
method psimp = unfold ConsequenceLocal_def polydefs; polysimp "Z2config"
method pfact = unfold ConsequenceLocal_def polydefs; polyfact "Z2config"
method pimc = (unfold ConsequenceGlobal_imc3 | unfold ConsequenceGlobal_imc2 | unfold ConsequenceGlobal_imc);
              unfold polydefs; polyimc "Z2config"


(*Proving theorems (double-checking with nitpick)*)

lemma "\<turnstile> x \<^bold>\<or> \<^bold>\<sim>x" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression*)

lemma "\<turnstile>\<^sup>n x \<^bold>\<and> \<^bold>\<sim>x" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression*)

lemma "x \<turnstile> \<^bold>\<sim>(\<^bold>\<sim>x)" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression (by reflexivity of  \<le>)*)

lemma "x \<turnstile>\<^sub>g \<^bold>\<sim>(\<^bold>\<sim>x)" nitpick[expect=none]
  apply pimc sorry (*pimc returns True*)

lemma "\<^bold>\<sim>(\<^bold>\<sim>x) \<turnstile> x" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*psimp returns a trivially true expression*)

lemma "\<^bold>\<sim>(\<^bold>\<sim>x) \<turnstile>\<^sub>g x" nitpick[expect=none]
  apply pimc sorry (*pimc returns True*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile> ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  apply psimp oops (*psimp returns a not-quite-trivially true expression (we should massage the formula a little...)*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile> ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*... using DMT, psimp now returns a trivially true expression*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile>\<^sub>g ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  apply pimc sorry (*pimc returns True*)


(*Refuting non-theorems (double-checking with nitpick)*)

lemma "x \<turnstile> \<^bold>\<sim>x" nitpick[expect=genuine]
  apply psimp oops (*psimp returns a not-quite-trivially false expression (x \<le> x + 1 does not generally hold in Z\<^sub>2)*)

lemma "x \<turnstile> \<^bold>\<sim>x" nitpick[expect=genuine]
  unfolding DMT apply psimp oops (*using DMT, psimp now returns a trivially false expression*)

lemma "x \<turnstile>\<^sub>g \<^bold>\<sim>x" nitpick[expect=genuine]
  apply pimc sorry (*pimc returns False*)

lemma "y \<^bold>\<rightarrow> \<^bold>\<sim>(x \<^bold>\<rightarrow> y \<^bold>\<and> (z \<^bold>\<or> (y \<^bold>\<rightarrow> x))) \<turnstile> z \<^bold>\<rightarrow> \<^bold>\<sim>(x \<^bold>\<or> y)" nitpick[expect=genuine]
  unfolding DMT apply psimp oops (*using DMT, psimp returns a trivially false expression*)

lemma "y \<^bold>\<rightarrow> \<^bold>\<sim>(x \<^bold>\<rightarrow> y \<^bold>\<and> (z \<^bold>\<or> (y \<^bold>\<rightarrow> x))) \<turnstile>\<^sub>g z \<^bold>\<rightarrow> \<^bold>\<sim>(x \<^bold>\<or> y)" nitpick[expect=genuine]
  apply pimc sorry (*pimc returns False*)

end