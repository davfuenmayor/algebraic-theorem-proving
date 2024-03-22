(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory F4_logic
imports F4_operators CAS_integration
begin

section \<open>Logical reasoning by polynomial manipulation in F4\<close>


subsection \<open>Logical validity in algebraic terms\<close>

(*The notions of logical validity and invalidity are stated algebraically as follows: *)
abbreviation(input) Validity::"F\<^sub>4 \<Rightarrow> o" ("\<turnstile> _" 49) 
  where "\<turnstile> C  \<equiv> C = \<^bold>\<top>\<^sup>L"
abbreviation(input) Invalidity::"F\<^sub>4 \<Rightarrow> o" ("\<turnstile>\<^sup>n _" 49) 
  where "\<turnstile>\<^sup>n C \<equiv> C = \<^bold>\<bottom>\<^sup>L"


subsection \<open>Logical consequence in algebraic terms\<close>

subsubsection \<open>Generalized consequence\<close>

(*For non-bivalent logics we shall introduce a convenient notion of generalized logical consequence 
 that takes into account two different kinds of assumptions: local and global *)
definition Consequence::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> o" ("[_|_\<turnstile>_]")
  where "[A\<^sub>g | A\<^sub>l \<turnstile> C]  \<equiv> \<turnstile> A\<^sub>g \<longrightarrow> A\<^sub>l \<le> C"

(*Observe that both global and local assumptions can be aggregated using the (logical) meet operation*)
lemma "[A\<^sub>g\<^sub>1 \<^bold>\<and> A\<^sub>g\<^sub>2 | A\<^sub>l \<turnstile> C] = (\<turnstile> A\<^sub>g\<^sub>1 \<and> \<turnstile> A\<^sub>g\<^sub>2 \<longrightarrow> A\<^sub>l \<le> C)" 
  by (smt (z3) Consequence_def MeetL.simps F\<^sub>4.exhaust)

subsubsection \<open>Local consequence\<close>

(*In the absence of global assumptions, the notion of logical consequence corresponds to what is known
 in the literature as 'local' (aka. 'degree-preserving') consequence *)
definition ConsequenceLocal::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> o" (infixr "\<turnstile>\<^sub>l" 10) 
  where "A \<turnstile>\<^sub>l C \<equiv> A \<le> C"

lemma  "(A \<turnstile>\<^sub>l C) = [\<^bold>\<top>\<^sup>L | A \<turnstile> C]" 
  unfolding Consequence_def ConsequenceLocal_def by simp

(*The (dual-)deduction-metatheorem, (d)DMT, allows for switching between local consequence and (in)validity*)
lemma DMT:  "(A \<turnstile>\<^sub>l B) \<longleftrightarrow> \<turnstile>  A \<^bold>\<rightarrow> B" 
  unfolding ConsequenceLocal_def by (smt (verit) ImplicationL.simps leqL.elims F\<^sub>4.distinct)
lemma dDMT: "(A \<turnstile>\<^sub>l B) \<longleftrightarrow> \<turnstile>\<^sup>n A \<^bold>\<leftharpoonup> B" 
  unfolding ConsequenceLocal_def by (smt (verit) DualImplicationL.simps leqL.elims F\<^sub>4.distinct)

subsubsection \<open>Global consequence\<close>

(*In the absence of local assumptions, the notion of logical consequence corresponds to what is known
 in the literature as 'global' (aka. 'truth-preserving') consequence *)
definition ConsequenceGlobal::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> o" (infixr "\<turnstile>\<^sub>g" 10)
  where "A \<turnstile>\<^sub>g C \<equiv> \<turnstile> A \<longrightarrow> \<turnstile> C"

lemma  "(A \<turnstile>\<^sub>g C) = [A | \<^bold>\<top>\<^sup>L \<turnstile> C]" 
  by (smt (verit) Consequence_def ConsequenceGlobal_def F\<^sub>4.distinct leqL.elims)

(*Generalized consequence can thus be stated in terms of global consequence using DMT (wrt. \<^bold>\<rightarrow>) *)
lemma ConsequenceGlobal_simp: "[A\<^sub>g | A\<^sub>l \<turnstile> C] = (A\<^sub>g \<turnstile>\<^sub>g A\<^sub>l \<^bold>\<rightarrow> C)" 
  using Consequence_def ConsequenceGlobal_def ConsequenceLocal_def DMT by simp

(*Introduces custom notation for ideal-membership checking (for interfacing with CAS)*)
consts idealMembership1::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> o" ("_ in <_>")
consts idealMembership2::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> o" ("_ in <_,_>")
consts idealMembership3::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> o" ("_ in <_,_,_>")

(*The equalities below draw from the fact (TODO cite) that global consequence in m-valued logics, 
for a prime-power m, can be stated in terms of ideal membership (modulo splitting polynomials) in GF(m)*)
axiomatization where
ConsequenceGlobal_imc: "(A \<turnstile>\<^sub>g C) = (C - \<^bold>\<top>\<^sup>L in < A - \<^bold>\<top>\<^sup>L >)" and
ConsequenceGlobal_imc2: "(A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<turnstile>\<^sub>g C) = (C - \<^bold>\<top>\<^sup>L in < A\<^sub>1 - \<^bold>\<top>\<^sup>L, A\<^sub>2 - \<^bold>\<top>\<^sup>L >)" and
ConsequenceGlobal_imc3: "(A\<^sub>1 \<^bold>\<and> A\<^sub>2 \<^bold>\<and> A\<^sub>3 \<turnstile>\<^sub>g C) = (C - \<^bold>\<top>\<^sup>L in < A\<^sub>1 - \<^bold>\<top>\<^sup>L, A\<^sub>2 - \<^bold>\<top>\<^sup>L, A\<^sub>3 - \<^bold>\<top>\<^sup>L >)" 


subsection \<open>Solving logic problems with Sage\<close>

(*Step-by-step: how to solve a local consequence problem algebraically (with Sage)*)
lemma "\<^bold>\<midarrow>(x \<^bold>\<and> y) \<turnstile>\<^sub>l (\<^bold>\<midarrow>x \<^bold>\<or> \<^bold>\<midarrow>y)"
  unfolding DMT (*apply deduction metatheorem (optional)*)
  unfolding polydefs (*expand logical connectives as their polynomial representations*)
  apply(poly_reduce "''PolynomialRing(GF(4),{x,y})''") (*simplify given polynomial over the field F\<^sub>4[x,y] *)
  sorry (*proven because the simplified expression trivially holds*) (*TODO: do this automatically via oracle*)

(*Step-by-step: how to solve a global consequence problem algebraically (with Sage)*)
lemma "\<^bold>\<midarrow>(x \<^bold>\<and> y) \<turnstile>\<^sub>g (\<^bold>\<midarrow>x \<^bold>\<or> \<^bold>\<midarrow>y)"
  unfolding ConsequenceGlobal_imc (*apply transformation to ideal-membership checking *)
  unfolding polydefs (*expand logical connectives as their polynomial representations*)
  apply(poly_imc "''PolynomialRing(GF(4),{x,y,z})''") (*check ideal-membership over the field F\<^sub>4[x,y] *)
  sorry (*proven because the simplified expression trivially holds*) (*TODO: do this automatically via oracle*)

(*Configuration string indicating that we work with polynomials over F\<^sub>4 using variables among {x,y,z,w} *)
abbreviation(input) \<open>F4config \<equiv> ''PolynomialRing(GF(4), {x,y,z,w})''\<close>
(*Furthermore, we can use Eisbach to introduce convenient proof methods*)
method preduce = unfold ConsequenceLocal_def polydefs; poly_reduce "F4config"
method pfactor = unfold ConsequenceLocal_def polydefs; poly_factorize "F4config"
method pimc = (unfold ConsequenceGlobal_imc3 | unfold ConsequenceGlobal_imc2 | unfold ConsequenceGlobal_imc);
              unfold polydefs; poly_imc "F4config"


(*Proving theorems (double-checking with nitpick)*)

lemma "\<turnstile> x \<^bold>\<or> \<^bold>\<midarrow>x" nitpick[expect=none]
  apply preduce sorry (*preduce returns a trivially true expression*)

lemma "\<turnstile>\<^sup>n x \<^bold>\<and> \<^bold>\<midarrow>x" nitpick[expect=none]
  apply preduce sorry (*preduce returns a trivially true expression*)

lemma "x \<turnstile>\<^sub>l \<^bold>\<not>(\<^bold>\<not>x)" nitpick[expect=none]
  unfolding DMT apply preduce sorry (*preduce returns a trivially true expression*)

lemma "x \<turnstile>\<^sub>g \<^bold>\<not>(\<^bold>\<not>x)" nitpick[expect=none]
  apply pimc sorry (*pimc returns True*)

lemma "\<^bold>\<not>(\<^bold>\<not>x) \<turnstile>\<^sub>l x" nitpick[expect=none]
  unfolding DMT apply preduce sorry (*preduce returns a trivially true expression*)

lemma "\<^bold>\<not>(\<^bold>\<not>x) \<turnstile>\<^sub>g x" nitpick[expect=none]
  apply pimc sorry (*pimc returns True*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile>\<^sub>l ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  apply preduce oops (*preduce returns a not-quite-trivially true expression (we should massage the formula a little...)*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile>\<^sub>l ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  unfolding DMT apply preduce sorry (*... using DMT, preduce now returns a trivially true expression*)

lemma "((x \<^bold>\<rightarrow> y) \<^bold>\<and> (z \<^bold>\<rightarrow> w)) \<turnstile>\<^sub>g ((x \<^bold>\<or> z) \<^bold>\<rightarrow> (y \<^bold>\<or> w))" nitpick[expect=none]
  apply pimc sorry (*pimc returns True*)


(*Refuting non-theorems (double-checking with nitpick)*)

lemma "\<turnstile> x \<^bold>\<or> \<^bold>\<not>x" nitpick[expect=genuine]
  apply preduce sorry (*preduce returns a trivially false expression*)

lemma "\<turnstile>\<^sup>n x \<^bold>\<and> \<^bold>\<not>x" nitpick[expect=genuine]
  apply preduce sorry (*preduce returns a trivially false expression*)

lemma "x \<turnstile>\<^sub>l \<^bold>\<not>x" nitpick[expect=genuine]
  apply preduce oops (*preduce returns a not-quite-trivially false expression (x \<le> x^2 + 1 does not generally hold in F\<^sub>4)*)

lemma "x \<turnstile>\<^sub>l \<^bold>\<not>x" nitpick[expect=genuine]
  unfolding DMT apply preduce oops (*using DMT, preduce now returns a trivially false expression*)

lemma "x \<turnstile>\<^sub>g \<^bold>\<not>x" nitpick[expect=genuine]
  apply pimc sorry (*pimc returns False*)

lemma "y \<^bold>\<rightarrow> \<^bold>\<not>(x \<^bold>\<rightarrow> y \<^bold>\<and> (z \<^bold>\<or> x)) \<turnstile>\<^sub>l z \<^bold>\<rightarrow> \<^bold>\<not>(x \<^bold>\<or> y)" nitpick[expect=genuine]
  unfolding DMT apply preduce oops (*using DMT, preduce returns a trivially false expression*)

lemma "y \<^bold>\<rightarrow> \<^bold>\<not>(x \<^bold>\<rightarrow> y \<^bold>\<and> (z \<^bold>\<or> x)) \<turnstile>\<^sub>g z \<^bold>\<rightarrow> \<^bold>\<not>(x \<^bold>\<or> y)" nitpick[expect=genuine]
  apply pimc sorry (*pimc returns False*)

end