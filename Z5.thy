(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z5
imports base
begin

section \<open>The Integers Modulo 5: Z5)\<close>

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

abbreviation Substraction::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5" (infixl "-" 65) (*adding the additive inverse*)
  where "a - b \<equiv> a + -b"

fun MultiplicativeInverse::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5" ("(_\<inverse>)" [1000] 999) where 
  "0\<inverse> = 0" |  (* as a convention *)
  "1\<inverse> = 1" |
  "2\<inverse> = 3" |
  "3\<inverse> = 2" |
  "4\<inverse> = 4" 

abbreviation Division::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5 \<Rightarrow> Z\<^sub>5" (infixl "'/" 70) (*multiplying the multiplicative inverse*)
  where "a / b \<equiv> a * b\<inverse>"

abbreviation Square::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5" ("(_)^2" [91]90)
  where "x^2 \<equiv> x*x"
abbreviation Cube::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5" ("(_)^3" [91]90)
  where "x^3 \<equiv> x*x*x"
abbreviation Tesseract::"Z\<^sub>5 \<Rightarrow> Z\<^sub>5" ("(_)^4" [91]90)
  where "x^4 \<equiv> x*x*x*x"

subsection \<open>Properties\<close>

lemma "a + 0 = a"  (* 0 is an additive unit*)
  by (smt (verit, del_insts) Addition.simps(1) Addition.simps(11) Addition.simps(16) Addition.simps(21) Addition.simps(6) Z\<^sub>5.exhaust)
lemma "a * 0 = 0"     (* 0 is a multiplicative absorber*)
  using Multiplication.elims by blast
lemma "a * 1 = a"      (* 1 is a multiplicative unit*)
  by (smt (verit) Multiplication.simps(12) Multiplication.simps(17) Multiplication.simps(2) Multiplication.simps(22) Multiplication.simps(7) MultiplicativeInverse.cases)
(* lemma "a + 1 = (\<not>a)"  (* 1 is an additive negator*) *)

lemma "a + -a = 0"   (*additive inverse law*)
  by (metis Addition.simps(1) Addition.simps(10) Addition.simps(14) Addition.simps(18) Addition.simps(22) AdditiveInverse.simps(1) AdditiveInverse.simps(2) AdditiveInverse.simps(3) AdditiveInverse.simps(4) AdditiveInverse.simps(5) MultiplicativeInverse.cases)
lemma "a \<noteq> 0 \<longrightarrow> a * a\<inverse> = 1"     (*multiplicative inverse law*)
  by (metis Multiplication.simps(14) Multiplication.simps(18) Multiplication.simps(25) Multiplication.simps(7) MultiplicativeInverse.cases MultiplicativeInverse.simps(2) MultiplicativeInverse.simps(3) MultiplicativeInverse.simps(4) MultiplicativeInverse.simps(5))

lemma "(a + a) = 2*a"  (* multiplication as iterated addition *)
  by (smt (verit, best) Addition.simps(1) Addition.simps(13) Addition.simps(19) Addition.simps(25) Addition.simps(7) Multiplication.simps(11) Multiplication.simps(12) Multiplication.simps(13) Multiplication.simps(14) Multiplication.simps(15) Z\<^sub>5.exhaust)
lemma "(a + a + a) = 3*a"  (* multiplication as iterated addition *)
  by (smt (verit, del_insts) Addition.simps(1) Addition.simps(12) Addition.simps(13) Addition.simps(19) Addition.simps(20) Addition.simps(23) Addition.simps(25) Addition.simps(7) Addition.simps(9) Multiplication.simps(16) Multiplication.simps(17) Multiplication.simps(18) Multiplication.simps(19) Multiplication.simps(20) Z\<^sub>5.exhaust)
lemma "(a + a + a + a) = 4*a"  (* multiplication as iterated addition *)
  by (smt (verit, best) Addition.simps(1) Addition.simps(12) Addition.simps(13) Addition.simps(15) Addition.simps(17) Addition.simps(19) Addition.simps(20) Addition.simps(23) Addition.simps(24) Addition.simps(25) Addition.simps(7) Addition.simps(8) Addition.simps(9) Multiplication.simps(21) Multiplication.simps(22) Multiplication.simps(23) Multiplication.simps(24) Multiplication.simps(25) MultiplicativeInverse.cases)
    
lemma "(4*a + a) = 0" (*addition cycle*)
  by (smt (verit) Addition.simps(1) Addition.simps(10) Addition.simps(14) Addition.simps(18) Addition.simps(22) Multiplication.simps(21) Multiplication.simps(22) Multiplication.simps(23) Multiplication.simps(24) Multiplication.simps(25) MultiplicativeInverse.elims)
lemma "(a^4 * a) = a" (*multiplication cycle*)
  by (smt (verit, best) Multiplication.simps(1) Multiplication.simps(10) Multiplication.simps(13) Multiplication.simps(14) Multiplication.simps(18) Multiplication.simps(19) Multiplication.simps(23) Multiplication.simps(24) Multiplication.simps(25) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9) MultiplicativeInverse.cases)

lemma "a * (b + c) = (a * b) + (a * c)" (*multiplication distributes over addition*)
  sorry (* by (smt (verit) Addition.simps(1) Addition.simps(10) Addition.simps(11) Addition.simps(12) Addition.simps(13) Addition.simps(14) Addition.simps(15) Addition.simps(16) Addition.simps(17) Addition.simps(18) Addition.simps(19) Addition.simps(2) Addition.simps(20) Addition.simps(21) Addition.simps(22) Addition.simps(23) Addition.simps(24) Addition.simps(25) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) AdditiveInverse.elims Multiplication.simps(1) Multiplication.simps(10) Multiplication.simps(11) Multiplication.simps(12) Multiplication.simps(13) Multiplication.simps(14) Multiplication.simps(15) Multiplication.simps(16) Multiplication.simps(17) Multiplication.simps(18) Multiplication.simps(19) Multiplication.simps(2) Multiplication.simps(20) Multiplication.simps(21) Multiplication.simps(22) Multiplication.simps(23) Multiplication.simps(24) Multiplication.simps(25) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(6) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9)) *)
lemma "a + (b * c) = (a + b) * (a + c)" nitpick oops (*countermodel: addition does not distribute over multiplication*)

lemma "((a + b) = c) \<longleftrightarrow> (a = (c - b))" (*substraction law (for equalities)*)
  sorry (* by (smt (z3) Addition.simps(1) Addition.simps(10) Addition.simps(11) Addition.simps(12) Addition.simps(13) Addition.simps(14) Addition.simps(15) Addition.simps(16) Addition.simps(17) Addition.simps(18) Addition.simps(19) Addition.simps(2) Addition.simps(20) Addition.simps(21) Addition.simps(22) Addition.simps(23) Addition.simps(24) Addition.simps(25) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) AdditiveInverse.simps(1) AdditiveInverse.simps(2) AdditiveInverse.simps(3) AdditiveInverse.simps(4) AdditiveInverse.simps(5) MultiplicativeInverse.cases) *)
lemma "b \<noteq> 0 \<Longrightarrow> ((a * b) = c) \<longleftrightarrow> (a = (c / b))" (*division law (for equalities) *)
  sorry (* by (smt (z3) Multiplication.simps(10) Multiplication.simps(12) Multiplication.simps(13) Multiplication.simps(14) Multiplication.simps(15) Multiplication.simps(17) Multiplication.simps(18) Multiplication.simps(19) Multiplication.simps(2) Multiplication.simps(20) Multiplication.simps(22) Multiplication.simps(23) Multiplication.simps(24) Multiplication.simps(25) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9) MultiplicativeInverse.cases MultiplicativeInverse.simps(2) MultiplicativeInverse.simps(3) MultiplicativeInverse.simps(4) MultiplicativeInverse.simps(5)) *)


subsubsection \<open>Polynomials\<close>

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
where 
"poly2 c\<^sub>2\<^sub>4 c\<^sub>2\<^sub>3 c\<^sub>2\<^sub>2 c\<^sub>2\<^sub>1 c\<^sub>2\<^sub>0 c\<^sub>1\<^sub>9 c\<^sub>1\<^sub>8 c\<^sub>1\<^sub>7 c\<^sub>1\<^sub>6 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0 \<equiv>
 \<lambda>x y. c\<^sub>2\<^sub>4\<cdot>x\<^sup>4\<cdot>y\<^sup>4 + c\<^sub>2\<^sub>3\<cdot>x\<^sup>4\<cdot>y\<^sup>3 + c\<^sub>2\<^sub>2\<cdot>x\<^sup>4\<cdot>y\<^sup>2 + c\<^sub>2\<^sub>1\<cdot>x\<^sup>4\<cdot>y + c\<^sub>2\<^sub>0\<cdot>x\<^sup>4 + 
       c\<^sub>1\<^sub>9\<cdot>x\<^sup>3\<cdot>y\<^sup>4 + c\<^sub>1\<^sub>8\<cdot>x\<^sup>3\<cdot>y\<^sup>3 + c\<^sub>1\<^sub>7\<cdot>x\<^sup>3\<cdot>y\<^sup>2 + c\<^sub>1\<^sub>6\<cdot>x\<^sup>3\<cdot>y + c\<^sub>1\<^sub>5\<cdot>x\<^sup>3 + 
       c\<^sub>1\<^sub>4\<cdot>x\<^sup>2\<cdot>y\<^sup>4 + c\<^sub>1\<^sub>3\<cdot>x\<^sup>2\<cdot>y\<^sup>3 + c\<^sub>1\<^sub>2\<cdot>x\<^sup>2\<cdot>y\<^sup>2 + c\<^sub>1\<^sub>1\<cdot>x\<^sup>2\<cdot>y + c\<^sub>1\<^sub>0\<cdot>x\<^sup>2 +
       c\<^sub>9\<cdot>x\<cdot>y\<^sup>4 + c\<^sub>8\<cdot>x\<cdot>y\<^sup>3 + c\<^sub>7\<cdot>x\<cdot>y\<^sup>2 + c\<^sub>6\<cdot>x\<cdot>y + c\<^sub>5\<cdot>x + 
       c\<^sub>4\<cdot>y\<^sup>4 + c\<^sub>3\<cdot>y\<^sup>3 + c\<^sub>2\<cdot>y\<^sup>2 + c\<^sub>1\<cdot>y + c\<^sub>0"

end