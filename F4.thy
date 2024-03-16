(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory F4
imports base
begin

section \<open>The Galois Field of size 4: F4\<close>

subsection \<open>Definitions\<close>

datatype F\<^sub>4 = Zero ("0") | One ("1") | JustA ("a") | SquaredA ("b")

fun Addition::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4" (infixl "+" 65) where
  "0 + 0 = 0" |
  "0 + 1 = 1" |
  "0 + a = a" |
  "0 + b = b" |
  "1 + 0 = 1" |
  "1 + 1 = 0" |
  "1 + a = b" |
  "1 + b = a" |
  "a + 0 = a" |
  "a + 1 = b" |
  "a + a = 0" |
  "a + b = 1" |
  "b + 0 = b" |
  "b + 1 = a" |
  "b + a = 1" |
  "b + b = 0" 

fun Multiplication::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4" (infixl "*" 70) where
  "0 * 0 = 0" |
  "0 * 1 = 0" |
  "0 * a = 0" |
  "0 * b = 0" |
  "1 * 0 = 0" |
  "1 * 1 = 1" |
  "1 * a = a" |
  "1 * b = b" |
  "a * 0 = 0" |
  "a * 1 = a" |
  "a * a = b" |
  "a * b = 1" |
  "b * 0 = 0" |
  "b * 1 = b" |
  "b * a = 1" |
  "b * b = a" 

abbreviation(input) AdditiveInverse::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("-_" [81] 80) 
  where "-x \<equiv> x"

abbreviation Substraction::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4" (infixl "-" 65) (*adding the additive inverse*)
  where "x - y \<equiv> x + -y"

fun MultiplicativeInverse::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("(_\<inverse>)" [1000] 999) where
  "0\<inverse> = 0" |  (* as a convention *)
  "1\<inverse> = 1" |
  "a\<inverse> = b" |
  "b\<inverse> = a"

abbreviation Division::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4" (infixl "'/" 70) (*multiplying the multiplicative inverse*)
  where "x / y \<equiv> x * y\<inverse>"

abbreviation Square::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("(_)^2" [91]90)
  where "x^2 \<equiv> x*x"
abbreviation Cube::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("(_)^3" [91]90)
  where "x^3 \<equiv> x*x*x"


subsection \<open>Properties\<close>

(* 'b' can be stated in terms of 'a' as: *)
lemma "b = a + 1" by simp
lemma "b = a^2" by simp

lemma "x + 0 = x"  (* 0 is an additive unit*)
  by (smt (z3) Addition.simps F\<^sub>4.exhaust)
lemma "x * 0 = 0"     (* 0 is a multiplicative absorber*)
  using Multiplication.elims by blast
lemma "x * 1 = x"      (* 1 is a multiplicative unit*)
  by (smt (z3) Multiplication.simps F\<^sub>4.exhaust)

lemma "x + -x = 0"   (*additive inverse law*)
  by (smt (z3) Addition.simps F\<^sub>4.exhaust)

lemma "x \<noteq> 0 \<longrightarrow> x * x\<inverse> = 1"     (*multiplicative inverse law*)
  by (smt (z3) Multiplication.simps MultiplicativeInverse.simps F\<^sub>4.exhaust)

(*Multiplication is NOT iterated addition *)
lemma "(x + x) = a*x" nitpick oops (*counterexample*)
lemma "(x + x) = b*x" nitpick oops (*counterexample*)
lemma "(x + x + x) = a*x" nitpick oops (*counterexample*)
lemma "(x + x + x) = b*x" nitpick oops (*counterexample*)
    
lemma "(x + x) = 0" (*addition cycle (has size 2)*)
  by (smt (z3) Addition.simps F\<^sub>4.exhaust)
lemma "(x * x * x * x) = x" (*multiplication cycle (has size 4)*)
  by (smt (z3) Multiplication.simps F\<^sub>4.exhaust)

lemma "x * (y + z) = (x * y) + (x * z)"  (*multiplication distributes over addition*)
  by (smt (z3) Addition.simps Multiplication.simps MultiplicativeInverse.cases)
lemma "x + (y * z) = (x + y) * (x + z)" nitpick oops (*countermodel: addition does not distribute over multiplication*)

lemma "((x + y) = z) \<longleftrightarrow> (x = (z - y))" (*substraction law (for equalities)*)
  by (smt (z3) Addition.simps F\<^sub>4.exhaust)

lemma "y \<noteq> 0 \<Longrightarrow> ((x * y) = z) \<longleftrightarrow> (x = (z / y))" (*division law (for equalities) *)
  by (smt (z3) Multiplication.simps MultiplicativeInverse.simps F\<^sub>4.exhaust)


subsubsection \<open>Polynomials\<close>

(*for reading convenience*)
notation(input) Multiplication (infixl "\<cdot>" 70)
notation(input) Square ("(_)\<^sup>2" [91]90)
notation(input) Cube ("(_)\<^sup>3" [91]90)

(*Constructs a polynomial in one variable. Takes four parameters as coeficients: c\<^sub>0-c\<^sub>3*)
abbreviation(input) poly1::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> (F\<^sub>4 \<Rightarrow> F\<^sub>4)"
  where "poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv> \<lambda>x. c\<^sub>3\<cdot>x\<^sup>3 + c\<^sub>2\<cdot>x\<^sup>2 + c\<^sub>1\<cdot>x + c\<^sub>0"

(*Constructs a polynomial in two variables. Takes 16 parameters as coeficients: c\<^sub>0-c\<^sub>1\<^sub>5*)
abbreviation(input) poly2::"F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> (F\<^sub>4 \<Rightarrow> F\<^sub>4 \<Rightarrow> F\<^sub>4)"
  where "poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv>
      \<lambda>x y. c\<^sub>1\<^sub>5\<cdot>x\<^sup>3\<cdot>y\<^sup>3 + c\<^sub>1\<^sub>4\<cdot>x\<^sup>3\<cdot>y\<^sup>2 + c\<^sub>1\<^sub>3\<cdot>x\<^sup>3\<cdot>y + c\<^sub>1\<^sub>2\<cdot>x\<^sup>3 + c\<^sub>1\<^sub>1\<cdot>x\<^sup>2\<cdot>y\<^sup>3 + c\<^sub>1\<^sub>0\<cdot>x\<^sup>2\<cdot>y\<^sup>2 +
           c\<^sub>9\<cdot>x\<^sup>2\<cdot>y + c\<^sub>8\<cdot>x\<^sup>2 + c\<^sub>7\<cdot>x\<cdot>y\<^sup>3 + c\<^sub>6\<cdot>x\<cdot>y\<^sup>2 + c\<^sub>5\<cdot>x\<cdot>y + c\<^sub>4\<cdot>x + c\<^sub>3\<cdot>y\<^sup>3 + c\<^sub>2\<cdot>y\<^sup>2 + c\<^sub>1\<cdot>y + c\<^sub>0"

end