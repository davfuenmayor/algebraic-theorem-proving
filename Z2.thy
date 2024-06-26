(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z2
imports base
begin

section \<open>The Integers Modulo 2: Z2\<close>

subsection \<open>Definitions\<close>

datatype Z\<^sub>2 = Zero ("0") | One ("1")

fun Addition::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2" (infixl "+" 65) where
  "0 + 0 = 0" |
  "0 + 1 = 1" |
  "1 + 0 = 1" |
  "1 + 1 = 0"

fun Multiplication::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2" (infixl "*" 70) where
  "0 * 0 = 0" |
  "0 * 1 = 0" |
  "1 * 0 = 0" |
  "1 * 1 = 1"

abbreviation(input) AdditiveInverse::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2" ("-_" [81] 80)
  where "-x \<equiv> x"

abbreviation(input) MultiplicativeInverse::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2" ("(_\<inverse>)" [1000] 999) 
  where "x\<inverse> \<equiv> x" (* intended behaviour for x \<noteq> 0 *)

(*Convenient abbreviations*)
abbreviation Substraction::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2" (infixl "-" 65) (*adding the additive inverse*)
  where "x - y \<equiv> x + -y"
abbreviation Division::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2" (infixl "'/" 70) (*multiplying the multiplicative inverse*)
  where "x / y \<equiv> x * y\<inverse>"


subsection \<open>General Field Properties\<close>

lemma "x + 0 = x"  (* 0 is an additive unit*)
  by (smt (z3) Addition.simps Z\<^sub>2.exhaust)
lemma "x * 0 = 0"     (* 0 is a multiplicative absorber*)
  by (smt (z3) Multiplication.elims)
lemma "x * 1 = x"      (* 1 is a multiplicative unit*)
  by (smt (z3) Multiplication.simps Z\<^sub>2.exhaust)
lemma "x + -x = 0"   (*additive inverse law*)
  by (smt (z3) Addition.elims)
lemma "x \<noteq> 0 \<longrightarrow> x * x\<inverse> = 1"     (*multiplicative inverse law*)
  by (smt (z3) Multiplication.elims)
lemma "x * (y + z) = (x * y) + (x * z)" (*multiplication distributes over addition*)
  by (smt (z3) Addition.simps Multiplication.elims)
lemma "x + (y * z) = (x + y) * (x + z)" nitpick oops (*countermodel: addition does not distribute over multiplication*)

lemma "((x + y) = z) \<longleftrightarrow> (x = (z - y))" (*substraction law*)
  by (smt (z3) Addition.simps Z\<^sub>2.exhaust)
lemma "y \<noteq> 0 \<Longrightarrow> ((x * y) = z) \<longleftrightarrow> (x = (z / y))" (*division law*)
  by (smt (z3) Multiplication.simps Z\<^sub>2.exhaust)


subsection \<open>Particular Z2 Properties\<close>

lemma addition_cycle: "(x + x) = 0" (*addition cycle*)
  by (smt (z3) Addition.elims)
lemma multiplication_cycle: "(x * x) = x" (*multiplication cycle*)
  by (smt (z3) Multiplication.elims)


subsection \<open>Polynomials\<close>

(*for reading convenience*)
notation(input) Multiplication (infixl "\<cdot>" 70)

(*Constructs a polynomial in one variable. Takes two parameters as coeficients: c\<^sub>1 and c\<^sub>0*)
abbreviation(input) poly1::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> (Z\<^sub>2 \<Rightarrow> Z\<^sub>2)"
  where "poly1 c\<^sub>1 c\<^sub>0 \<equiv> \<lambda>x. c\<^sub>1\<cdot>x + c\<^sub>0"

(*Constructs a polynomial in two variables. Takes four parameters as coeficients: c\<^sub>0-c\<^sub>3*)
abbreviation(input) poly2::"Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> (Z\<^sub>2 \<Rightarrow> Z\<^sub>2 \<Rightarrow> Z\<^sub>2)"
  where "poly2 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv> \<lambda>x y. c\<^sub>3\<cdot>x\<cdot>y + c\<^sub>2\<cdot>x + c\<^sub>1\<cdot>y + c\<^sub>0"

end