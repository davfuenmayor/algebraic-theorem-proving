(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z3_logic
imports Z3_order102
begin

section \<open>Logics based on Z3 (with the specified ordering)\<close>

(*Solve interesting problems using CAS*)
ML_file\<open>SagePoly.ML\<close>

method_setup polysimp = 
\<open>Args.term >> (fn params => fn ctxt =>  SIMPLE_METHOD' (SUBGOAL (cmd_exec ctxt (simp_cmd (term2str ctxt params)))))\<close>
"Uses SageMath to simplify current goal by reducing the given polynomial to its unique normal form"

method_setup polyfact =
\<open>Args.term >> (fn params => fn ctxt =>  SIMPLE_METHOD' (SUBGOAL (cmd_exec ctxt (factor_cmd (term2str ctxt params)))))\<close>
"Uses SageMath to simplify current goal by factoring the given polynomial"

abbreviation(input) \<open>Z3 \<equiv> ''PolynomialRing(GF(3), {0})''\<close>

(*Let us introduce the following convenient proof methods (variables among 'x,y,z')*)
method pfact = unfold polydefs; polyfact "[Z3, ''|x,y,z|'']"
method psimp = unfold polydefs; polysimp "[Z3, ''|x,y,z|'']"


(*Test factorization and simplification of polynomials using Sage*)
lemma "x \<^bold>\<and> y = 0" apply pfact oops
lemma "x \<^bold>\<rightarrow> y = 0" apply pfact oops

lemma "x \<^bold>\<or> y = r" apply pfact oops
lemma "x \<^bold>\<rightharpoonup> y = r" apply psimp oops


(*Consequence and validity definitions *)
abbreviation(input) Validity::"Z\<^sub>3 \<Rightarrow> bool" ("\<turnstile> _" 49) 
  where "\<turnstile> a \<equiv> a = \<^bold>\<top>"
abbreviation(input) Consequence_local::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> bool" (infixr "\<turnstile>" 10) 
  where "a \<turnstile> b \<equiv> a \<le> b"
abbreviation(input) Consequence_global::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> bool" (infixr "\<turnstile>\<^sub>g" 10) 
  where "a \<turnstile>\<^sub>g b \<equiv> \<turnstile> a \<longrightarrow> \<turnstile> b"

(*The deduction metatheorem (DMT)*)
lemma DMT: "(a \<turnstile> b) \<longleftrightarrow> \<turnstile> (a \<^bold>\<rightarrow> b)" (*holds for local consequence*)
  by (smt (verit, del_insts) Implication.simps(1) Implication.simps(2) Implication.simps(3) Implication.simps(4) Implication.simps(5) Implication.simps(6) Implication.simps(7) Implication.simps(8) Implication.simps(9) Z\<^sub>3.simps(2) leq.elims(1))
lemma "(a \<turnstile>\<^sub>g b) \<longleftrightarrow> \<turnstile> (a \<^bold>\<rightarrow> b)" nitpick oops (*counterexample for global consequence*)


abbreviation(input) Invalidity::"Z\<^sub>3 \<Rightarrow> bool" ("\<turnstile>\<^sup>n _" 49) 
  where "\<turnstile>\<^sup>n a \<equiv> a = \<^bold>\<bottom>"

(*The (dual) deduction metatheorem (DMT)*)
lemma dDMT: "(a \<turnstile> b) \<longleftrightarrow> \<turnstile>\<^sup>n (a \<^bold>\<leftharpoonup> b)" (*holds for local consequence*)
  by (metis Join_maxdef Z3_order102.antisym leq.simps(1) resid_law2)
lemma "(a \<turnstile>\<^sub>g b) \<longleftrightarrow> \<turnstile>\<^sup>n (a \<^bold>\<leftharpoonup> b)" nitpick oops (*counterexample for global consequence*)


(*How to use Nitpick and Sage to refute/verify logic conjectures*)
lemma "\<turnstile> x \<^bold>\<or> \<^bold>\<smile>x" nitpick oops (*countermodel*)
lemma "\<turnstile>\<^sup>n x \<^bold>\<and> \<^bold>\<smile>x" apply psimp oops (*polysimp returns \<^bold>\<bottom>*)
lemma "x \<turnstile> \<^bold>\<smile>(\<^bold>\<smile>x)" unfolding DMT apply psimp oops (*polysimp returns \<^bold>\<top>*)
lemma "\<^bold>\<smile>(\<^bold>\<smile>x) \<turnstile> x" nitpick oops (*countermodel*)

(*Both below return the same polynomial (TODO: implement equality check in tactic)*)
lemma "\<^bold>\<smile>(x \<^bold>\<or> y) = (\<^bold>\<smile>x \<^bold>\<and> \<^bold>\<smile>y)" apply psimp oops
lemma "\<^bold>\<smile>(x \<^bold>\<or> y) = (\<^bold>\<smile>x \<^bold>\<and> \<^bold>\<smile>y)"  apply(rule sym) apply(psimp) oops

end