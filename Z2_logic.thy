(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z2_logic
imports Z2_order
begin

section \<open>Logics based on Z2\<close>

(*Solve interesting problems using CAS*)
ML_file\<open>SagePoly.ML\<close>

method_setup polysimp = 
\<open>Args.term >> (fn params => fn ctxt =>  SIMPLE_METHOD' (SUBGOAL (cmd_exec ctxt (simp_cmd (term2str ctxt params)))))\<close>
"Uses SageMath to simplify current goal by reducing the given polynomial to its unique normal form"

method_setup polyfact =
\<open>Args.term >> (fn params => fn ctxt =>  SIMPLE_METHOD' (SUBGOAL (cmd_exec ctxt (factor_cmd (term2str ctxt params)))))\<close>
"Uses SageMath to simplify current goal by factoring the given polynomial"

abbreviation(input) \<open>Z2 \<equiv> ''PolynomialRing(GF(2), {0})''\<close>

(*Let us introduce the following convenient proof methods (variables among 'x,y,z')*)
method pfact = unfold polydefs; polyfact "[Z2, ''|x,y,z|'']"
method psimp = unfold polydefs; polysimp "[Z2, ''|x,y,z|'']"


(*Test factorization and simplification of polynomials using Sage*)
lemma "x \<^bold>\<and> y = 0" apply pfact oops
lemma "x \<^bold>\<rightarrow> y = 0" apply pfact oops

lemma "x \<^bold>\<or> y = r" apply pfact oops
lemma "x \<^bold>\<rightharpoonup> y = r" apply psimp oops


(*Consequence and validity definitions *)
abbreviation(input) Validity::"Z\<^sub>2 \<Rightarrow> bool" ("\<turnstile> _" 49) 
  where "\<turnstile> a \<equiv> a = \<^bold>\<top>"
abbreviation(input) Consequence_local::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> bool" (infixr "\<turnstile>" 10) 
  where "a \<turnstile> b \<equiv> a \<le> b"
abbreviation(input) Consequence_global::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> bool" (infixr "\<turnstile>\<^sub>g" 10) 
  where "a \<turnstile>\<^sub>g b \<equiv> \<turnstile> a \<longrightarrow> \<turnstile> b"

(*Local and global consequence are the same (in the bivalued case)*)
lemma "(a \<turnstile>\<^sub>g b) = (a \<turnstile> b)" using leq.elims(1) by blast

(*The deduction metatheorem (DMT)*)
lemma DMT: "(a \<turnstile> b) \<longleftrightarrow> \<turnstile> (a \<^bold>\<rightarrow> b)"
  by (smt (z3) Implication.elims Z\<^sub>2.simps(2) leq.elims(3) leq.simps(3))


abbreviation(input) Invalidity::"Z\<^sub>2 \<Rightarrow> bool" ("\<turnstile>\<^sup>n _" 49) 
  where "\<turnstile>\<^sup>n a \<equiv> a = \<^bold>\<bottom>"

(*The (dual) deduction metatheorem (DMT)*)
lemma dDMT: "(a \<turnstile> b) \<longleftrightarrow> \<turnstile>\<^sup>n (a \<^bold>\<leftharpoonup> b)"
  by (metis DMT DualImplication.simps(1) DualImplication.simps(2) DualImplication.simps(3) DualImplication.simps(4) leq.elims(2) leq.elims(3))


(*How to use Sage to refute/verify logic conjectures*)
lemma "\<turnstile> x \<^bold>\<or> \<^bold>\<sim>x" apply psimp oops (*polysimp returns \<^bold>\<top>*)
lemma "\<turnstile>\<^sup>n x \<^bold>\<and> \<^bold>\<sim>x" apply psimp oops (*polysimp returns \<^bold>\<bottom>*)
lemma "x \<turnstile> \<^bold>\<sim>(\<^bold>\<sim>x)" unfolding DMT apply psimp oops (*polysimp returns \<^bold>\<top>*)
lemma "\<^bold>\<sim>(\<^bold>\<sim>x) \<turnstile> x" unfolding DMT apply psimp oops (*polysimp returns \<^bold>\<top>*)

(*Both below return the same polynomial (TODO: implement equality check in tactic)*)
lemma "\<^bold>\<sim>(x \<^bold>\<or> y) = (\<^bold>\<sim>x \<^bold>\<and> \<^bold>\<sim>y)" apply psimp oops
lemma "\<^bold>\<sim>(x \<^bold>\<or> y) = (\<^bold>\<sim>x \<^bold>\<and> \<^bold>\<sim>y)"  apply(rule sym) apply(psimp) oops

end