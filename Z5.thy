(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z5
imports base
begin

section \<open>The Integers Modulo 5: Z5\<close>

subsection \<open>Definitions\<close>

datatype Z\<^sub>5 = Zero ("0") | One ("1") | Two ("2")  | Three ("3")  | Four ("4")

fun Addition::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5" (infixl "+" 65) where
  "0 + 0 = 0" |
  "0 + 1 = 1" |
  "0 + 2 = 2" |
  "0 + 3 = 3" |
  "0 + 4 = 4" |
  "1 + 0 = 1" |
  "1 + 1 = 2" |
  "1 + 2 = 3" |
  "1 + 3 = 4" |
  "1 + 4 = 0" |
  "2 + 0 = 2" |
  "2 + 1 = 3" |
  "2 + 2 = 4" |
  "2 + 3 = 0" |
  "2 + 4 = 1" |
  "3 + 0 = 3" |
  "3 + 1 = 4" |
  "3 + 2 = 0" |
  "3 + 3 = 1" |
  "3 + 4 = 2" |
  "4 + 0 = 4" |
  "4 + 1 = 0" |
  "4 + 2 = 1" |
  "4 + 3 = 2" |
  "4 + 4 = 3" 

fun Multiplication::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5" (infixl "*" 70) where
  "0 * 0 = 0" |
  "0 * 1 = 0" |
  "0 * 2 = 0" |
  "0 * 3 = 0" |
  "0 * 4 = 0" |
  "1 * 0 = 0" |
  "1 * 1 = 1" |
  "1 * 2 = 2" |
  "1 * 3 = 3" |
  "1 * 4 = 4" |
  "2 * 0 = 0" |
  "2 * 1 = 2" |
  "2 * 2 = 4" |
  "2 * 3 = 1" |
  "2 * 4 = 3" |
  "3 * 0 = 0" |
  "3 * 1 = 3" |
  "3 * 2 = 1" |
  "3 * 3 = 4" |
  "3 * 4 = 2" |
  "4 * 0 = 0" |
  "4 * 1 = 4" |
  "4 * 2 = 3" |
  "4 * 3 = 2" |
  "4 * 4 = 1" 

fun AdditiveInverse::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5" ("-_" [81] 80) where
  "-0 = 0" |
  "-1 = 4" |
  "-2 = 3" |
  "-3 = 2" |
  "-4 = 1"

fun MultiplicativeInverse::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5" ("(_\<inverse>)" [1000] 999) where 
  "0\<inverse> = 0" |  (* intended behaviour for x \<noteq> 0 (value for 0 chosen for convenience) *)
  "1\<inverse> = 1" |
  "2\<inverse> = 3" |
  "3\<inverse> = 2" |
  "4\<inverse> = 4" 

(*Convenient abbreviations*)
abbreviation Substraction::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5" (infixl "-" 65) (*adding the additive inverse*)
  where "x - y \<equiv> x + -y"
abbreviation Division::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5" (infixl "'/" 70) (*multiplying the multiplicative inverse*)
  where "x / y \<equiv> x * y\<inverse>"
abbreviation Square::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5" ("(_)^2" [91]90)
  where "x^2 \<equiv> x*x"
abbreviation Cube::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5" ("(_)^3" [91]90)
  where "x^3 \<equiv> x*x*x"
abbreviation Tesseract::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5" ("(_)^4" [91]90)
  where "x^4 \<equiv> x*x*x*x"


subsection \<open>General Field Properties\<close>

lemma "x + 0 = x"  (* 0 is an additive unit*)
  by (smt (z3) Addition.simps Z\<^sub>5.exhaust)
lemma "x * 0 = 0"     (* 0 is a multiplicative absorber*)
  by (smt (z3) Multiplication.simps Z\<^sub>5.exhaust)
lemma "x * 1 = x"      (* 1 is a multiplicative unit*)
  by (smt (z3) Multiplication.simps Z\<^sub>5.exhaust)
lemma "x + -x = 0"   (*additive inverse law*)
  by (smt (z3) Addition.simps AdditiveInverse.simps Z\<^sub>5.exhaust)
lemma "x \<noteq> 0 \<longrightarrow> x * x\<inverse> = 1"     (*multiplicative inverse law*)
  by (smt (z3) Multiplication.simps MultiplicativeInverse.elims)
lemma "x * (y + z) = (x * y) + (x * z)" (*multiplication distributes over addition*)
  by (smt (z3) Addition.simps Multiplication.simps Z\<^sub>5.exhaust)
lemma "x + (y * z) = (x + y) * (x + z)" nitpick oops (*countermodel: addition does not distribute over multiplication*)

lemma "((x + y) = z) \<longleftrightarrow> (x = (z - y))" (*substraction law*)
  by (smt (z3) Addition.simps AdditiveInverse.cases AdditiveInverse.simps)
lemma "y \<noteq> 0 \<Longrightarrow> ((x * y) = z) \<longleftrightarrow> (x = (z / y))" (*division law*)
  by (smt (z3) Multiplication.simps MultiplicativeInverse.simps Z\<^sub>5.exhaust)


subsection \<open>Particular Z5 Properties\<close>

lemma addition_cycle: "(x + x + x + x + x) = 0" (*addition cycle*)
  by (smt (z3) Addition.simps Z\<^sub>5.exhaust)
lemma multiplication_cycle: "(x * x * x * x * x) = x" (*multiplication cycle*)
  by (smt (z3) Multiplication.simps Z\<^sub>5.exhaust)

lemma "(x + x) = 2*x"  (* multiplication as iterated addition *)
  by (smt (z3) Addition.simps Multiplication.simps Z\<^sub>5.exhaust)
lemma "(x + x + x) = 3*x"  (* multiplication as iterated addition *)
  by (smt (z3) Addition.simps Multiplication.simps Z\<^sub>5.exhaust)
lemma "(x + x + x + x) = 4*x"  (* multiplication as iterated addition *)
  by (smt (z3) Addition.simps Multiplication.simps Z\<^sub>5.exhaust)
    

subsection \<open>Polynomials\<close>

(*for reading convenience*)
notation(input) Multiplication (infixl "\<cdot>" 70)
notation(input) Square ("(_)\<^sup>2" [91]90)
notation(input) Cube ("(_)\<^sup>3" [91]90)
notation(input) Tesseract ("(_)\<^sup>4" [91]90)

(*Constructs a polynomial in one variable. Takes 5 parameters as coeficients: c\<^sub>0-c\<^sub>4*)
abbreviation(input) poly1::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> (Z\<^sub>5 \<Rightarrow> Z\<^sub>5)"
  where "poly1 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv> \<lambda>x. c\<^sub>4\<cdot>x\<^sup>4 + c\<^sub>3\<cdot>x\<^sup>3 + c\<^sub>2\<cdot>x\<^sup>2 + c\<^sub>1\<cdot>x + c\<^sub>0"

(*Constructs a polynomial in two variables. Takes 25 parameters as coeficients: c\<^sub>0-c\<^sub>2\<^sub>4*)
abbreviation(input) poly2::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow>
                            Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow>
                            Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow>
                            Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow>
                            Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> (Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5)"
  where "poly2 c\<^sub>2\<^sub>4 c\<^sub>2\<^sub>3 c\<^sub>2\<^sub>2 c\<^sub>2\<^sub>1 c\<^sub>2\<^sub>0 c\<^sub>1\<^sub>9 c\<^sub>1\<^sub>8 c\<^sub>1\<^sub>7 c\<^sub>1\<^sub>6 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv>
           \<lambda>x y. c\<^sub>2\<^sub>4\<cdot>x\<^sup>4\<cdot>y\<^sup>4 + c\<^sub>2\<^sub>3\<cdot>x\<^sup>4\<cdot>y\<^sup>3 + c\<^sub>2\<^sub>2\<cdot>x\<^sup>4\<cdot>y\<^sup>2 + c\<^sub>2\<^sub>1\<cdot>x\<^sup>4\<cdot>y + c\<^sub>2\<^sub>0\<cdot>x\<^sup>4 + 
                 c\<^sub>1\<^sub>9\<cdot>x\<^sup>3\<cdot>y\<^sup>4 + c\<^sub>1\<^sub>8\<cdot>x\<^sup>3\<cdot>y\<^sup>3 + c\<^sub>1\<^sub>7\<cdot>x\<^sup>3\<cdot>y\<^sup>2 + c\<^sub>1\<^sub>6\<cdot>x\<^sup>3\<cdot>y + c\<^sub>1\<^sub>5\<cdot>x\<^sup>3 + 
                 c\<^sub>1\<^sub>4\<cdot>x\<^sup>2\<cdot>y\<^sup>4 + c\<^sub>1\<^sub>3\<cdot>x\<^sup>2\<cdot>y\<^sup>3 + c\<^sub>1\<^sub>2\<cdot>x\<^sup>2\<cdot>y\<^sup>2 + c\<^sub>1\<^sub>1\<cdot>x\<^sup>2\<cdot>y + c\<^sub>1\<^sub>0\<cdot>x\<^sup>2 +
                 c\<^sub>9\<cdot>x\<cdot>y\<^sup>4 + c\<^sub>8\<cdot>x\<cdot>y\<^sup>3 + c\<^sub>7\<cdot>x\<cdot>y\<^sup>2 + c\<^sub>6\<cdot>x\<cdot>y + c\<^sub>5\<cdot>x + 
                 c\<^sub>4\<cdot>y\<^sup>4 + c\<^sub>3\<cdot>y\<^sup>3 + c\<^sub>2\<cdot>y\<^sup>2 + c\<^sub>1\<cdot>y + c\<^sub>0"

end