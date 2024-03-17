(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z3_logic
imports Z3_order120
begin

section \<open>Logical reasoning by polynomial simplification in Z3 (wrt. given ordering)\<close>

subsection \<open>Logical notions in algebraic terms\<close>

(*The notions of logical validity and invalidity are stated algebraically as follows: *)
abbreviation(input) Validity::"Z\<^sub>3 \<Rightarrow> bool" ("\<turnstile> _" 49) 
  where "\<turnstile> C  \<equiv> C = \<^bold>\<top>"
abbreviation(input) Invalidity::"Z\<^sub>3 \<Rightarrow> bool" ("\<turnstile>\<^sup>n _" 49) 
  where "\<turnstile>\<^sup>n C \<equiv> C = \<^bold>\<bottom>"

(*For non-bivalent logics we shall introduce a convenient notion of generalized logical consequence 
 that takes into account two different kinds of assumptions: local and global *)
definition Consequence1::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> bool" ("[_|_\<turnstile>_]")         (*for one global premise*)
  where "[A\<^sub>g | A\<^sub>l \<turnstile> C]  \<equiv> \<turnstile> A\<^sub>g \<longrightarrow> A\<^sub>l \<le> C"
definition Consequence2::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> bool" ("[_,_|_\<turnstile>_]") (*for two global premises*)
  where "[A\<^sub>g\<^sub>1, A\<^sub>g\<^sub>2 | A\<^sub>l \<turnstile> C]  \<equiv> \<turnstile> A\<^sub>g\<^sub>1 \<and> \<turnstile> A\<^sub>g\<^sub>2 \<longrightarrow> A\<^sub>l \<le> C"
(* ... (extend for more global premises as the need arises)*)

(*In the absence of global assumptions, the notion of logical consequence corresponds to what is known
 in the literature as 'local' (aka. 'degree-preserving') consequence: *)
definition ConsequenceL::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> bool" (infixr "\<turnstile>" 10) 
  where "A \<turnstile> C \<equiv> A \<le> C"

lemma  "(A \<turnstile> C) = [\<^bold>\<top> | A \<turnstile> C]" by (simp add: Consequence1_def ConsequenceL_def)

(*In the absence of local assumptions, the notion of logical consequence corresponds to what is known
 in the literature as 'global' (aka. 'truth-preserving') consequence: *)
definition ConsequenceG1::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> bool" (infixr "\<turnstile>\<^sub>g" 10)     (*for one premise*)
  where "A \<turnstile>\<^sub>g C \<equiv> \<turnstile> A \<longrightarrow> \<turnstile> C"
definition ConsequenceG2::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> bool" ("[_,_\<turnstile>\<^sub>g_]") (*for two premises*) 
  where "[A\<^sub>1, A\<^sub>2 \<turnstile>\<^sub>g C] \<equiv> \<turnstile> A\<^sub>1 \<and> \<turnstile> A\<^sub>2 \<longrightarrow> \<turnstile> C"

lemma  "(A \<turnstile>\<^sub>g C) = [A | \<^bold>\<top> \<turnstile> C]" by (smt (verit) Consequence1_def ConsequenceG1_def Z\<^sub>3.distinct leq.elims)
lemma  "[A\<^sub>1, A\<^sub>2 \<turnstile>\<^sub>g C] = [A\<^sub>1, A\<^sub>2 | \<^bold>\<top> \<turnstile> C]"  by (smt (verit) Consequence2_def ConsequenceG2_def Z\<^sub>3.distinct leq.elims)

(*The (dual-)deduction-metatheorem, (d)DMT, allows for switching between local consequence and (in)validity*)
lemma DMT:  "(A \<turnstile> C) \<longleftrightarrow> \<turnstile>  A \<^bold>\<rightarrow> C" unfolding ConsequenceL_def by (smt (z3) Implication.elims leq.simps)
lemma dDMT: "(A \<turnstile> C) \<longleftrightarrow> \<turnstile>\<^sup>n A \<^bold>\<leftharpoonup> C" unfolding ConsequenceL_def by (smt (z3) DualImplication.elims leq.simps)


subsection \<open>Setting-up CAS Integration\<close>

(*Routines for integrating CAS (SageMath) for manipulating polynomials*)
ML_file\<open>SagePoly.ML\<close>

(*Declares two methods for polynomial rewriting using CAS: 
  - polysimp: polynomial simplification by rewriting in canonical form (ie. as sum of monomials)
  - polyfact: polysimp followed by factorization (when applicable) *)
method_setup polysimp = 
\<open>Args.term >> (fn params => fn ctxt =>  SIMPLE_METHOD' (SUBGOAL (cmd_exec ctxt (simp_cmd (term2str ctxt params)))))\<close>
method_setup polyfact =
\<open>Args.term >> (fn params => fn ctxt =>  SIMPLE_METHOD' (SUBGOAL (cmd_exec ctxt (factor_cmd (term2str ctxt params)))))\<close>

(*Step-by-step: how to solve a logic problem algebraically (with Sage)*)
lemma "\<^bold>\<sim>(x \<^bold>\<and> y) \<turnstile> (\<^bold>\<sim>x \<^bold>\<or> \<^bold>\<sim>y)"
  unfolding DMT (*apply deduction metatheorem (optional)*)
  unfolding polydefs (*expand logical connectives as their polynomial representations*)
  apply(polysimp "''PolynomialRing(GF(3),{x,y})''") (*simplify given polynomial over the field Z\<^sub>3[x,y] *)
  sorry (*proven because the simplified expression trivially holds*) (*TODO: do this automatically via oracle*)

(*Configuration string indicating that we work with polynomials over Z\<^sub>3 using variables in {x,y,z,w} *)
abbreviation(input) \<open>Z3config \<equiv> ''PolynomialRing(GF(3), {x,y,z,w})''\<close>

(*Furthermore, we can use Eisbach to introduce convenient proof methods*)
method psimp = unfold polydefs ConsequenceL_def; polysimp "Z3config"
method pfact = unfold polydefs ConsequenceL_def; polyfact "Z3config"


subsection \<open>Solving logic problems with Sage\<close>

(*Proving theorems (double-checking with nitpick)*)

lemma "\<turnstile> x \<^bold>\<or> \<^bold>\<frown>x" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression*)

lemma "\<turnstile>\<^sup>n x \<^bold>\<and> \<^bold>\<smile>x" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression*)

lemma "x \<turnstile> \<^bold>\<smile>(\<^bold>\<smile>x)" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*psimp returns a trivially true expression*)

lemma "\<^bold>\<frown>(\<^bold>\<frown>x) \<turnstile> x" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*psimp returns a trivially true expression*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile> ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  apply psimp oops (*psimp returns a not-quite-trivially true expression (we should massage the formula a little...)*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile> ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*... using DMT, psimp now returns a trivially true expression*)


(*Refuting non-theorems (double-checking with nitpick)*)

lemma "x \<turnstile> \<^bold>\<frown>x" nitpick[expect=genuine]
  apply psimp oops (*psimp returns a not-quite-trivially false expression (x \<le> x^2 + x + 1 does not generally hold in Z\<^sub>3)*)

lemma "x \<turnstile> \<^bold>\<frown>x" nitpick[expect=genuine]
  unfolding DMT apply psimp oops (*using DMT, psimp now returns a trivially false expression*)

lemma "y \<^bold>\<rightarrow> \<^bold>\<sim>(x \<^bold>\<rightarrow> y \<^bold>\<and> (z \<^bold>\<or> x)) \<turnstile> z \<^bold>\<rightarrow> \<^bold>\<sim>(x \<^bold>\<or> y)" nitpick[expect=genuine]
  unfolding DMT apply psimp oops (*using DMT, psimp returns a trivially false expression*)

end