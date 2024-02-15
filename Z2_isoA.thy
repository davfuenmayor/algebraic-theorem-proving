(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z2_isoA
imports Z2_order
begin

(*Convenient definition*)
definition xor :: "o \<Rightarrow> o \<Rightarrow> o"  (infix "\<triangle>" 30)
  where "a \<triangle> b \<equiv> a \<noteq> b"


section \<open>Isomorphism between Z2 and Bool (side A - the 'traditional' one)\<close>

definition toBool::"Z\<^sub>2 \<Rightarrow> o" ("[_]\<^sub>o")
  where "[x]\<^sub>o \<equiv> x = 1"
definition toZ2::"o \<Rightarrow> Z\<^sub>2"  ("[_]\<^sub>2")
  where "[x]\<^sub>2 \<equiv> if x then 1 else 0"

named_theorems Z2Bool_iso (* simplifying equations for (isomorphic) round-trip translation*)
lemma iso1[Z2Bool_iso]: "[[x]\<^sub>o]\<^sub>2 = x" unfolding toZ2_def toBool_def using Z\<^sub>2.exhaust by auto
lemma iso2[Z2Bool_iso]: "[[x]\<^sub>2]\<^sub>o = x" unfolding toZ2_def toBool_def by simp

named_theorems Z2Bool_trans (* simplifying equations for term translation*)
lemma zero_trans[Z2Bool_trans]: "[0]\<^sub>o = \<bottom>" unfolding toBool_def by simp
lemma one_trans[Z2Bool_trans]:  "[1]\<^sub>o = \<top>" unfolding toBool_def by simp
lemma succ_trans[Z2Bool_trans]: "[x + 1]\<^sub>o = (\<not>[x]\<^sub>o)" by (metis Addition.simps(2) Addition.simps(4) Z\<^sub>2.exhaust one_trans zero_trans)
lemma add_trans[Z2Bool_trans]:  "[x + y]\<^sub>o = ([x]\<^sub>o \<triangle> [y]\<^sub>o)" using Addition.elims unfolding toBool_def xor_def by blast
lemma mult_trans[Z2Bool_trans]: "[x * y]\<^sub>o = ([x]\<^sub>o \<and> [y]\<^sub>o)" using Multiplication.elims unfolding toBool_def by blast
lemma bot_trans[Z2Bool_trans]: "[\<bottom>]\<^sub>2 = 0" unfolding toZ2_def by simp
lemma top_trans[Z2Bool_trans]: "[\<top>]\<^sub>2 = 1" unfolding toZ2_def by simp
lemma neg_trans[Z2Bool_trans]: "[\<not>x]\<^sub>2 = [x]\<^sub>2 + 1" unfolding toZ2_def by simp
lemma xor_trans[Z2Bool_trans]:   "[x \<triangle> y]\<^sub>2  = [x]\<^sub>2 + [y]\<^sub>2" unfolding toZ2_def xor_def by simp
lemma conj_trans[Z2Bool_trans]:  "[x \<and> y]\<^sub>2  = [x]\<^sub>2 * [y]\<^sub>2" unfolding toZ2_def by simp
lemma disj_trans[Z2Bool_trans]:  "[x \<or> y]\<^sub>2  = [x]\<^sub>2 * [y]\<^sub>2 + [x]\<^sub>2 + [y]\<^sub>2" unfolding toZ2_def by simp
lemma impl_trans[Z2Bool_trans]:  "[x \<rightarrow> y]\<^sub>2 = [x]\<^sub>2 * [y]\<^sub>2 + [x]\<^sub>2 +  1" unfolding toZ2_def by simp
lemma dimpl_trans[Z2Bool_trans]: "[x \<rightharpoonup> y]\<^sub>2 = [x]\<^sub>2 * [y]\<^sub>2 + [y]\<^sub>2" unfolding toZ2_def by simp

named_theorems Z2Bool_simps (* all simplifying equations*)
declare Z2Bool_trans[Z2Bool_simps] Z2Bool_iso[Z2Bool_simps]

named_theorems Z2Bool_eq (* rules (backwards application)*)
lemma Bool_eq[Z2Bool_eq]: "[x]\<^sub>o = [y]\<^sub>o \<Longrightarrow> x = y" unfolding toBool_def by (metis Z\<^sub>2.exhaust)
lemma Bool_eq0[Z2Bool_eq]: "\<not>[x]\<^sub>o \<Longrightarrow> x = 0" by (metis Z\<^sub>2.exhaust one_trans)
lemma Bool_eq1[Z2Bool_eq]:  "[x]\<^sub>o \<Longrightarrow> x = 1" by (simp add: toBool_def)
lemma Z2_eq[Z2Bool_eq]: "[x]\<^sub>2 = [y]\<^sub>2 \<Longrightarrow> x = y" unfolding toZ2_def using Z\<^sub>2.distinct(1) by presburger
lemma Z2_eq0[Z2Bool_eq]: "[x]\<^sub>2 = 0 \<Longrightarrow> \<not>x" using top_trans by auto
lemma Z2_eq1[Z2Bool_eq]: "[x]\<^sub>2 = 1 \<Longrightarrow> x" by (metis Z2_eq top_trans)


(*Examples*)

lemma "(x \<^bold>\<rightarrow> y) = ((x \<^bold>\<leftharpoonup> y) + 1)" 
  unfolding polydefs  
  apply (rule Z2Bool_eq, unfold Z2Bool_simps)
  apply (rule Z2Bool_eq, unfold Z2Bool_simps)
  apply (rule Z2Bool_eq, unfold Z2Bool_simps)
  unfolding xor_def by auto

(*Let us introduce the following convenient proof method*)
method bool_iso = rule Z2Bool_eq; unfold Z2Bool_simps

lemma "(x \<rightarrow> y) = (\<not>(x \<leftharpoonup> y))" 
  apply bool_iso
  apply bool_iso
  apply bool_iso
  apply bool_iso
  unfolding xor_def by auto

(*TODO: more examples*)


end