(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory F4_logic
imports F4_operators
begin

section \<open>Logical reasoning by polynomial simplification in F4\<close>

subsection \<open>Logical notions in algebraic terms\<close>

(*The notions of logical validity and invalidity are stated algebraically as follows: *)
abbreviation(input) Validity::"F\<^sub>4 \<Rightarrow> bool" ("\<turnstile> _" 49) 
  where "\<turnstile> C  \<equiv> C = \<^bold>\<top>\<^sup>L"
abbreviation(input) Invalidity::"F\<^sub>4 \<Rightarrow> bool" ("\<turnstile>\<^sup>n _" 49) 
  where "\<turnstile>\<^sup>n C \<equiv> C = \<^bold>\<bottom>\<^sup>L"

(*For non-bivalent logics we shall introduce a convenient notion of generalized logical consequence 
 that takes into account two different kinds of assumptions: local and global *)
definition Consequence1::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> bool" ("[_|_\<turnstile>_]")         (*for one global premise*)
  where "[A\<^sub>g | A\<^sub>l \<turnstile> C]  \<equiv> \<turnstile> A\<^sub>g \<longrightarrow> A\<^sub>l \<le> C"
definition Consequence2::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> bool" ("[_,_|_\<turnstile>_]") (*for two global premises*)
  where "[A\<^sub>g\<^sub>1, A\<^sub>g\<^sub>2 | A\<^sub>l \<turnstile> C]  \<equiv> \<turnstile> A\<^sub>g\<^sub>1 \<and> \<turnstile> A\<^sub>g\<^sub>2 \<longrightarrow> A\<^sub>l \<le> C"
(* ... (extend for more global premises as the need arises)*)

(*In the absence of global assumptions, the notion of logical consequence corresponds to what is known
 in the literature as 'local' (aka. 'degree-preserving') consequence: *)
definition ConsequenceL::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> bool" (infixr "\<turnstile>" 10) 
  where "A \<turnstile> C \<equiv> A \<le> C"

lemma  "(A \<turnstile> C) = [\<^bold>\<top>\<^sup>L | A \<turnstile> C]" by (simp add: Consequence1_def ConsequenceL_def)

(*In the absence of local assumptions, the notion of logical consequence corresponds to what is known
 in the literature as 'global' (aka. 'truth-preserving') consequence: *)
definition ConsequenceG1::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> bool" (infixr "\<turnstile>\<^sub>g" 10)     (*for one premise*)
  where "A \<turnstile>\<^sub>g C \<equiv> \<turnstile> A \<longrightarrow> \<turnstile> C"
definition ConsequenceG2::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> bool" ("[_,_\<turnstile>\<^sub>g_]") (*for two premises*) 
  where "[A\<^sub>1, A\<^sub>2 \<turnstile>\<^sub>g C] \<equiv> \<turnstile> A\<^sub>1 \<and> \<turnstile> A\<^sub>2 \<longrightarrow> \<turnstile> C"

lemma  "(A \<turnstile>\<^sub>g C) = [A | \<^bold>\<top>\<^sup>L \<turnstile> C]" by (smt (verit) Consequence1_def ConsequenceG1_def F\<^sub>4.distinct leqL.elims)
lemma  "[A\<^sub>1, A\<^sub>2 \<turnstile>\<^sub>g C] = [A\<^sub>1, A\<^sub>2 | \<^bold>\<top>\<^sup>L \<turnstile> C]"  by (smt (verit) Consequence2_def ConsequenceG2_def F\<^sub>4.distinct leqL.elims)

(*The (dual-)deduction-metatheorem, (d)DMT, allows for switching between local consequence and (in)validity*)
lemma DMT:  "(A \<turnstile> B) \<longleftrightarrow> \<turnstile>  A \<^bold>\<rightarrow> B" unfolding ConsequenceL_def by (smt (verit) ImplicationL.simps leqL.elims F\<^sub>4.distinct)
lemma dDMT: "(A \<turnstile> B) \<longleftrightarrow> \<turnstile>\<^sup>n A \<^bold>\<leftharpoonup> B" unfolding ConsequenceL_def by (smt (verit) DualImplicationL.simps leqL.elims F\<^sub>4.distinct)


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
lemma "\<^bold>\<midarrow>(x \<^bold>\<and> y) \<turnstile> (\<^bold>\<midarrow>x \<^bold>\<or> \<^bold>\<midarrow>y)"
  unfolding DMT (*apply deduction metatheorem (optional)*)
  unfolding polydefs (*expand logical connectives as their polynomial representations*)
  apply(polysimp "''PolynomialRing(GF(4),{x,y})''") (*simplify given polynomial over the field Z\<^sub>3[x,y] *)
  sorry (*proven because the simplified expression trivially holds*) (*TODO: do this automatically via oracle*)

(*Configuration string indicating that we work with polynomials over Z\<^sub>3 using variables in {x,y,z,w} *)
abbreviation(input) \<open>F4config \<equiv> ''PolynomialRing(GF(4), {x,y,z,w})''\<close>

(*Furthermore, we can use Eisbach to introduce convenient proof methods*)
method psimp = unfold polydefs ConsequenceL_def; polysimp "F4config"
method pfact = unfold polydefs ConsequenceL_def; polyfact "F4config"


subsection \<open>Solving logic problems with Sage\<close>

(*Proving theorems (double-checking with nitpick)*)

lemma "\<turnstile> x \<^bold>\<or> \<^bold>\<midarrow>x" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression*)

lemma "\<turnstile>\<^sup>n x \<^bold>\<and> \<^bold>\<midarrow>x" nitpick[expect=none]
  apply psimp sorry (*psimp returns a trivially true expression*)

lemma "x \<turnstile> \<^bold>\<not>(\<^bold>\<not>x)" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*psimp returns a trivially true expression*)

lemma "\<^bold>\<not>(\<^bold>\<not>x) \<turnstile> x" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*psimp returns a trivially true expression*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile> ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  apply psimp oops (*psimp returns a not-quite-trivially true expression (we should massage the formula a little...)*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile> ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  unfolding DMT apply psimp sorry (*... using DMT, psimp now returns a trivially true expression*)


(*Refuting non-theorems (double-checking with nitpick)*)
lemma "\<turnstile> x \<^bold>\<or> \<^bold>\<not>x" nitpick[expect=genuine]
  apply psimp sorry (*psimp returns a trivially false expression*)

lemma "\<turnstile>\<^sup>n x \<^bold>\<and> \<^bold>\<not>x" nitpick[expect=genuine]
  apply psimp sorry (*psimp returns a trivially false expression*)

lemma "x \<turnstile> \<^bold>\<not>x" nitpick[expect=genuine]
  apply psimp oops (*psimp returns a not-quite-trivially false expression (x \<le> x^2 + 1 does not generally hold in F\<^sub>4)*)

lemma "x \<turnstile> \<^bold>\<not>x" nitpick[expect=genuine]
  unfolding DMT apply psimp oops (*using DMT, psimp now returns a trivially false expression*)

lemma "y \<^bold>\<rightarrow> \<^bold>\<not>(x \<^bold>\<rightarrow> y \<^bold>\<and> (z \<^bold>\<or> x)) \<turnstile> z \<^bold>\<rightarrow> \<^bold>\<not>(x \<^bold>\<or> y)" nitpick[expect=genuine]
  unfolding DMT apply psimp oops (*using DMT, psimp returns a trivially false expression*)

end