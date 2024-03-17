(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z2_logic
imports Z2_order
begin

section \<open>Logical reasoning by polynomial simplification in Z2\<close>

subsection \<open>Logical notions in algebraic terms\<close>

(*The notions of logical validity and invalidity are stated algebraically as follows: *)
abbreviation(input) Validity::"Z\<^sub>2 \<Rightarrow> bool" ("\<turnstile> _" 49) 
  where "\<turnstile> C  \<equiv> C = \<^bold>\<top>"
abbreviation(input) Invalidity::"Z\<^sub>2 \<Rightarrow> bool" ("\<turnstile>\<^sup>n _" 49) 
  where "\<turnstile>\<^sup>n C \<equiv> C = \<^bold>\<bottom>"

(*The notion of logical consequence can be stated algebraically as the lattice-ordering: *)
definition Consequence::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> bool" (infixr "\<turnstile>" 10) 
  where "A \<turnstile> C  \<equiv> A \<le> C"

(*The above definition of consequence (aka. 'degree-preserving') is equivalent, by bivalence, to the
 traditional definitions from the literature (based on 'truth-preservation', 'incompatibility', etc.)*)
lemma Consequence_truthpres_def: "(A \<turnstile> C) = (\<turnstile> A \<longrightarrow> \<turnstile> C)" unfolding Consequence_def using leq.elims(1) by blast
lemma Consequence_incompat_def:  "(A \<turnstile> C) = (\<turnstile>\<^sup>n A \<^bold>\<and> \<^bold>\<sim>C)" unfolding Consequence_def by (smt (z3) Meet.elims Negation.simps Z\<^sub>2.distinct leq.elims)

(*The (dual-)deduction-metatheorem, (d)DMT, allows for switching between consequence and (in)validity*)
lemma DMT:  "(A \<turnstile> C) \<longleftrightarrow> \<turnstile>  A \<^bold>\<rightarrow> C" unfolding Consequence_def by (smt (z3) Implication.elims leq.simps)
lemma dDMT: "(A \<turnstile> C) \<longleftrightarrow> \<turnstile>\<^sup>n A \<^bold>\<leftharpoonup> C" unfolding Consequence_def by (smt (z3) DualImplication.elims leq.simps)


subsection \<open>Setting-up CAS Integration\<close>

(*Routines for integrating a CAS (Sage) for manipulating polynomials*)
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
  apply(polysimp "''PolynomialRing(GF(2),{x,y})''") (*simplify given polynomial over the field Z\<^sub>2[x,y] *)
  sorry (*proven because the simplified expression trivially holds*) (*TODO: do this automatically via oracle*)

(*Configuration string indicating that we work with polynomials over Z\<^sub>2 using variables in {x,y,z,w} *)
abbreviation(input) \<open>Z2config \<equiv> ''PolynomialRing(GF(2), {x,y,z,w})''\<close>

(*Furthermore, we can use Eisbach to introduce convenient proof methods*)
method psimp = unfold polydefs Consequence_def; polysimp "Z2config"
method pfact = unfold polydefs Consequence_def; polyfact "Z2config"


subsection \<open>Solving logic problems with Sage\<close>

(*Proving theorems (double-checking with nitpick)*)

lemma "\<turnstile> x \<^bold>\<or> \<^bold>\<sim>x" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression*)

lemma "\<turnstile>\<^sup>n x \<^bold>\<and> \<^bold>\<sim>x" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression*)

lemma "x \<turnstile> \<^bold>\<sim>(\<^bold>\<sim>x)" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression (by reflexivity of  \<le>)*)

lemma "\<^bold>\<sim>(\<^bold>\<sim>x) \<turnstile> x" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*psimp returns a trivially true expression*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile> ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  apply psimp oops (*psimp returns a not-quite-trivially true expression (we should massage the formula a little...)*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile> ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*... using DMT, psimp now returns a trivially true expression*)


(*Refuting non-theorems (double-checking with nitpick)*)

lemma "x \<turnstile> \<^bold>\<sim>x" nitpick[expect=genuine]
  apply psimp oops (*psimp returns a not-quite-trivially false expression (x \<le> x + 1 does not generally hold in Z\<^sub>2)*)

lemma "x \<turnstile> \<^bold>\<sim>x" nitpick[expect=genuine]
  unfolding DMT apply psimp oops (*using DMT, psimp now returns a trivially false expression*)

lemma "y \<^bold>\<rightarrow> \<^bold>\<sim>(x \<^bold>\<rightarrow> y \<^bold>\<and> (z \<^bold>\<or> (y \<^bold>\<rightarrow> x))) \<turnstile> z \<^bold>\<rightarrow> \<^bold>\<sim>(x \<^bold>\<or> y)" nitpick[expect=genuine]
  unfolding DMT apply psimp oops (*using DMT, psimp returns a trivially false expression*)

end