(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z4
imports base
begin

section \<open>The Integers Modulo 4: Z4\<close>

subsection \<open>Definitions\<close>

datatype Z\<^sub>4 = Zero ("0") | One ("1") | Two ("2") | Three ("3")

fun Addition::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4" (infixl "+" 65) where
  "0 + 0 = 0" |
  "0 + 1 = 1" |
  "0 + 2 = 2" |
  "0 + 3 = 3" |
  "1 + 0 = 1" |
  "1 + 1 = 2" |
  "1 + 2 = 3" |
  "1 + 3 = 0" |
  "2 + 0 = 2" |
  "2 + 1 = 3" |
  "2 + 2 = 0" |
  "2 + 3 = 1" |
  "3 + 0 = 3" |
  "3 + 1 = 0" |
  "3 + 2 = 1" |
  "3 + 3 = 2" 

fun Multiplication::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4" (infixl "*" 70) where
  "0 * 0 = 0" |
  "0 * 1 = 0" |
  "0 * 2 = 0" |
  "0 * 3 = 0" |
  "1 * 0 = 0" |
  "1 * 1 = 1" |
  "1 * 2 = 2" |
  "1 * 3 = 3" |
  "2 * 0 = 0" |
  "2 * 1 = 2" |
  "2 * 2 = 0" |
  "2 * 3 = 2" |
  "3 * 0 = 0" |
  "3 * 1 = 3" |
  "3 * 2 = 2" |
  "3 * 3 = 1" 

fun AdditiveInverse::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4" ("-_" [81] 80) where
  "-0 = 0" |
  "-1 = 3" |
  "-2 = 2" |
  "-3 = 1"

abbreviation Substraction::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4" (infixl "-" 65) (*adding the additive inverse*)
  where "x - y \<equiv> x + -y"

(*
abbreviation(input) MultiplicativeInverse::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4" ("(_\<inverse>)" [1000] 999) 
  where "x\<inverse> \<equiv> x"
abbreviation Division::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4" (infixl "'/" 70) (*multiplying the multiplicative inverse*)
  where "x / y \<equiv> x * y\<inverse>"
*)

abbreviation Square::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4" ("(_)^2" [91]90)
  where "x^2 \<equiv> x*x"
abbreviation Cube::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4" ("(_)^3" [91]90)
  where "x^3 \<equiv> x*x*x"


subsection \<open>Properties\<close>

lemma "x + 0 = x"  (* 0 is an additive unit*)
  by (metis Addition.simps(1) Addition.simps(13) Addition.simps(5) Addition.simps(9) Z\<^sub>4.exhaust)
lemma "x * 0 = 0"     (* 0 is a multiplicative absorber*)
  using Multiplication.elims by blast
lemma "x * 1 = x"      (* 1 is a multiplicative unit*)
  by (smt (verit, best) AdditiveInverse.elims Multiplication.simps(10) Multiplication.simps(14) Multiplication.simps(2) Multiplication.simps(6))

lemma "x + -x = 0"   (*additive inverse law*)
  by (smt (verit, best) Addition.simps(1) Addition.simps(11) Addition.simps(14) Addition.simps(8) AdditiveInverse.elims)

(*lemma "x \<noteq> 0 \<longrightarrow> x * x\<inverse> = 1"     (*multiplicative inverse law*)
  using Multiplication.elims by blast*)

lemma "(x + x) = 2*x"  (* multiplication as iterated addition *)
  by (smt (verit, ccfv_threshold) Addition.simps(1) Addition.simps(11) Addition.simps(16) Addition.simps(6) AdditiveInverse.elims Multiplication.simps(10) Multiplication.simps(11) Multiplication.simps(12) Multiplication.simps(9))
lemma "(x + x + x) = 3*x"  (* multiplication as iterated addition *)
  by (smt (verit, best) Addition.simps(1) Addition.simps(10) Addition.simps(11) Addition.simps(12) Addition.simps(16) Addition.simps(3) Addition.simps(6) Multiplication.simps(13) Multiplication.simps(14) Multiplication.simps(15) Multiplication.simps(16) Z\<^sub>4.exhaust)
    
lemma "(x + x + x + x) = 0" (*addition cycle*)
  by (smt (verit, best) Addition.simps(1) Addition.simps(10) Addition.simps(11) Addition.simps(12) Addition.simps(14) Addition.simps(16) Addition.simps(3) Addition.simps(6) Addition.simps(8) AdditiveInverse.cases)
lemma "(x * x * x * x) = x" (*multiplication cycle*)
  nitpick oops (*counterexample: since Z\<^sub>4 is not a field*)

lemma "x * (y + z) = (x * y) + (x * z)" (*multiplication distributes over addition*)
  sorry (* by (smt (z3) Addition.simps(1) Addition.simps(10) Addition.simps(11) Addition.simps(12) Addition.simps(13) Addition.simps(14) Addition.simps(15) Addition.simps(16) Addition.simps(2) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) AdditiveInverse.cases Multiplication.simps(1) Multiplication.simps(10) Multiplication.simps(11) Multiplication.simps(12) Multiplication.simps(13) Multiplication.simps(14) Multiplication.simps(15) Multiplication.simps(16) Multiplication.simps(2) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(6) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9)) *)
lemma "x + (y * z) = (x + y) * (x + z)" nitpick oops (*countermodel: addition does not distribute over multiplication*)

lemma "((x + y) = z) \<longleftrightarrow> (x = (z - y))" (*substraction law (for equalities)*)
  sorry (* by (smt (verit, best) Addition.simps(1) Addition.simps(10) Addition.simps(11) Addition.simps(12) Addition.simps(13) Addition.simps(14) Addition.simps(15) Addition.simps(16) Addition.simps(2) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) AdditiveInverse.cases AdditiveInverse.simps(1) AdditiveInverse.simps(2) AdditiveInverse.simps(3) AdditiveInverse.simps(4)) *)

(*lemma "y \<noteq> 0 \<Longrightarrow> ((x * y) = z) \<longleftrightarrow> (x = (z / y))" (*division law (for equalities) *) *)


subsubsection \<open>Polynomials\<close>

(*for reading convenience*)
notation(input) Multiplication (infixl "\<cdot>" 70)
notation(input) Square ("(_)\<^sup>2" [91]90)
notation(input) Cube ("(_)\<^sup>3" [91]90)

(*Constructs a polynomial in one variable. Takes four parameters as coeficients: c\<^sub>0-c\<^sub>3*)
abbreviation(input) poly1::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> (Z\<^sub>4 \<Rightarrow> Z\<^sub>4)"
  where "poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv> \<lambda>x. c\<^sub>3\<cdot>x\<^sup>3 + c\<^sub>2\<cdot>x\<^sup>2 + c\<^sub>1\<cdot>x + c\<^sub>0"

(*Constructs a polynomial in two variables. Takes 16 parameters as coeficients: c\<^sub>0-c\<^sub>15*)
abbreviation(input) poly2::"Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> (Z\<^sub>4 \<Rightarrow> Z\<^sub>4 \<Rightarrow> Z\<^sub>4)"
  where "poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv>
      \<lambda>x y. c\<^sub>1\<^sub>5\<cdot>x\<^sup>3\<cdot>y\<^sup>3 + c\<^sub>1\<^sub>4\<cdot>x\<^sup>3\<cdot>y\<^sup>2 + c\<^sub>1\<^sub>3\<cdot>x\<^sup>3\<cdot>y + c\<^sub>1\<^sub>2\<cdot>x\<^sup>3 + c\<^sub>1\<^sub>1\<cdot>x\<^sup>2\<cdot>y\<^sup>3 + c\<^sub>1\<^sub>0\<cdot>x\<^sup>2\<cdot>y\<^sup>2 +
           c\<^sub>9\<cdot>x\<^sup>2\<cdot>y + c\<^sub>8\<cdot>x\<^sup>2 + c\<^sub>7\<cdot>x\<cdot>y\<^sup>3 + c\<^sub>6\<cdot>x\<cdot>y\<^sup>2 + c\<^sub>5\<cdot>x\<cdot>y + c\<^sub>4\<cdot>x + c\<^sub>3\<cdot>y\<^sup>3 + c\<^sub>2\<cdot>y\<^sup>2 + c\<^sub>1\<cdot>y + c\<^sub>0"

end