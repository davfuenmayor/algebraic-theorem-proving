(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z3
imports base
begin

section \<open>The Integers Modulo 3: Z3\<close>

subsection \<open>Definitions\<close>

datatype Z\<^sub>3 = Zero ("0") | One ("1") | Two ("2")

fun Addition::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3" (infixl "+" 65) where
  "0 + 0 = 0" |
  "0 + 1 = 1" |
  "0 + 2 = 2" |
  "1 + 0 = 1" |
  "1 + 1 = 2" |
  "1 + 2 = 0" |
  "2 + 0 = 2" |
  "2 + 1 = 0" |
  "2 + 2 = 1" 

fun Multiplication::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3" (infixl "*" 70) where
  "0 * 0 = 0" |
  "0 * 1 = 0" |
  "0 * 2 = 0" |
  "1 * 0 = 0" |
  "1 * 1 = 1" |
  "1 * 2 = 2" |
  "2 * 0 = 0" |
  "2 * 1 = 2" |
  "2 * 2 = 1" 

fun AdditiveInverse::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("-_" [81] 80) where
  "-0 = 0" |
  "-1 = 2" |
  "-2 = 1"

abbreviation(input) MultiplicativeInverse::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("(_\<inverse>)" [1000] 999) 
  where "x\<inverse> \<equiv> x" (* intended behaviour for x \<noteq> 0 *)

(*Convenient abbreviations*)
abbreviation Substraction::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3" (infixl "-" 65) (*adding the additive inverse*)
  where "x - y \<equiv> x + -y"
abbreviation Division::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3" (infixl "'/" 70) (*multiplying the multiplicative inverse*)
  where "x / y \<equiv> x * y\<inverse>"
abbreviation Square::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("(_)^2" [91]90) (*iterating multiplication twice*)
  where "x^2 \<equiv> x*x"


subsection \<open>General Field Properties\<close>

lemma "x + 0 = x"  (* 0 is an additive unit*)
  by (smt (z3) Addition.simps Z\<^sub>3.exhaust)
lemma "x * 0 = 0"     (* 0 is a multiplicative absorber*)
  by (smt (z3) Multiplication.simps Z\<^sub>3.exhaust)
lemma "x * 1 = x"      (* 1 is a multiplicative unit*)
  by (smt (z3) Multiplication.simps Z\<^sub>3.exhaust)
lemma "x + -x = 0"   (*additive inverse law*)
  by (smt (z3) Addition.simps AdditiveInverse.simps Z\<^sub>3.exhaust)
lemma "x \<noteq> 0 \<longrightarrow> x * x\<inverse> = 1"     (*multiplicative inverse law*)
  by (smt (z3) Multiplication.elims)
lemma "x * (y + z) = (x * y) + (x * z)" (*multiplication distributes over addition*)
  by (smt (z3) Addition.simps Multiplication.simps Z\<^sub>3.exhaust)
lemma "x + (y * z) = (x + y) * (x + z)" nitpick oops (*countermodel: addition does not distribute over multiplication*)

lemma "((x + y) = z) \<longleftrightarrow> (x = (z - y))" (*substraction law*)
  by (smt (z3) Addition.simps AdditiveInverse.cases AdditiveInverse.simps)
lemma "y \<noteq> 0 \<Longrightarrow> ((x * y) = z) \<longleftrightarrow> (x = (z / y))" (*division law*)
  by (smt (z3) Multiplication.simps Z\<^sub>3.exhaust)


subsection \<open>Particular Z3 Properties\<close>

lemma addition_cycle: "(x + x + x) = 0" (*addition cycle*)
  by (smt (z3) Addition.simps Z\<^sub>3.exhaust)
lemma multiplication_cycle: "(x * x * x) = x" (*multiplication cycle*)
  by (smt (z3) Multiplication.simps Z\<^sub>3.exhaust)

lemma "(x + x) = 2*x"  (* multiplication as iterated addition *)
  by (smt (z3) Addition.simps Multiplication.simps Z\<^sub>3.exhaust)


subsection \<open>Polynomials\<close>

(*for reading convenience*)
notation(input) Multiplication (infixl "\<cdot>" 70)
notation(input) Square ("(_)\<^sup>2" [91]90)

(*Constructs a polynomial in one variable. Takes three parameters as coeficients: c\<^sub>0, c\<^sub>1 and c\<^sub>2*)
abbreviation(input) poly1::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> (Z\<^sub>3 \<Rightarrow> Z\<^sub>3)"
  where "poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv> \<lambda>x. c\<^sub>2\<cdot>x\<^sup>2 + c\<^sub>1\<cdot>x + c\<^sub>0"

(*Constructs a polynomial in two variables. Takes nine parameters as coeficients: c\<^sub>0-c\<^sub>8*)
abbreviation(input) poly2::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> (Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3)"
  where "poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv>
                  \<lambda>x y. c\<^sub>8\<cdot>x\<^sup>2\<cdot>y\<^sup>2 + c\<^sub>7\<cdot>x\<^sup>2\<cdot>y + c\<^sub>6\<cdot>x\<^sup>2 + c\<^sub>5\<cdot>x\<cdot>y\<^sup>2 + c\<^sub>4\<cdot>x\<cdot>y + c\<^sub>3\<cdot>x + c\<^sub>2\<cdot>y\<^sup>2 + c\<^sub>1\<cdot>y + c\<^sub>0"

end