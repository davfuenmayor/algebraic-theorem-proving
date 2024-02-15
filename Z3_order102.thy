(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Z3_order102
imports Z3
begin

section \<open>Ordering Z3\<close>

subsection \<open>Order Structure\<close>

fun leq::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> bool"  (infix "\<le>" 51) where
  "2 \<le> _ = \<top>" |
  "_ \<le> 1 = \<top>" |
  "0 \<le> 0 = \<top>" |
  "_ \<le> _ = \<bottom>"

abbreviation(input) geq::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> bool" (infix "\<ge>" 51)
  where "x \<ge> y \<equiv> y \<le> x"

lemma "2 \<le> 0 \<and> 0 \<le> 1" by simp

lemma refl: "x \<le> x" using leq.elims(3) by blast
lemma trans: "x \<le> y \<and> y \<le> z \<longrightarrow> x \<le> z" by (metis Z\<^sub>3.simps(6) leq.elims(2) leq.elims(3))
lemma antisym: "x \<le> y \<and> y \<le> x \<longrightarrow> x = y" by (metis Z\<^sub>3.distinct(5) leq.elims(2))
lemma linear: "x \<le> y \<or> y \<le> x" by (metis leq.elims(3) leq.simps(1) leq.simps(3))

(*Let's introduce the lattice operations: meet/min and join/max*)
fun Meet::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3" (infixl "\<^bold>\<and>" 56) where (*minimal (meet) of two values*)
  "0 \<^bold>\<and> 0 = 0" |
  "0 \<^bold>\<and> 1 = 0" |
  "0 \<^bold>\<and> 2 = 2" |
  "1 \<^bold>\<and> 0 = 0" |
  "1 \<^bold>\<and> 1 = 1" |
  "1 \<^bold>\<and> 2 = 2" |
  "2 \<^bold>\<and> 0 = 2" |
  "2 \<^bold>\<and> 1 = 2" |
  "2 \<^bold>\<and> 2 = 2"

lemma Meet_mindef: "Meet x y = (if x \<le> y then x else y)"  (*double check*)
  by (smt (verit, del_insts) Meet.simps(1) Meet.simps(2) Meet.simps(3) Meet.simps(4) Meet.simps(5) Meet.simps(6) Meet.simps(7) Meet.simps(8) Meet.simps(9) antisym leq.elims(3))

fun Join::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3" (infixl "\<^bold>\<or>" 55) where (*maximal (join) of two values*)
  "0 \<^bold>\<or> 0 = 0" |
  "0 \<^bold>\<or> 1 = 1" |
  "0 \<^bold>\<or> 2 = 0" |
  "1 \<^bold>\<or> 0 = 1" |
  "1 \<^bold>\<or> 1 = 1" |
  "1 \<^bold>\<or> 2 = 1" |
  "2 \<^bold>\<or> 0 = 0" |
  "2 \<^bold>\<or> 1 = 1" |
  "2 \<^bold>\<or> 2 = 2" 

lemma Join_maxdef: "Join x y = (if x \<le> y then y else x)" (*double check*)
  by (smt (verit, del_insts) AdditiveInverse.cases Join.simps(1) Join.simps(2) Join.simps(3) Join.simps(4) Join.simps(5) Join.simps(6) Join.simps(7) Join.simps(8) Join.simps(9) antisym leq.simps(1) leq.simps(2))

lemma lattice_distr1: "(x \<^bold>\<and> (y \<^bold>\<or> z)) = ((x \<^bold>\<and> y) \<^bold>\<or> (x \<^bold>\<and> z))"
  by (smt (verit, del_insts) AdditiveInverse.elims Join.simps(1) Join.simps(2) Join.simps(3) Join.simps(4) Join.simps(5) Join.simps(6) Join.simps(7) Join.simps(8) Join.simps(9) Meet.simps(1) Meet.simps(2) Meet.simps(3) Meet.simps(5) Meet.simps(6) Meet.simps(7) Meet.simps(9))
lemma lattice_distr2: "(x \<^bold>\<or> (y \<^bold>\<and> z)) = ((x \<^bold>\<or> y) \<^bold>\<and> (x \<^bold>\<or> z))" 
  by (smt (verit, ccfv_threshold) Join.simps(1) Join.simps(2) Join.simps(3) Join.simps(4) Join.simps(5) Join.simps(8) Join.simps(9) Meet.simps(1) Meet.simps(2) Meet.simps(3) Meet.simps(4) Meet.simps(5) Meet.simps(6) Meet.simps(7) Meet.simps(8) Meet.simps(9) Z\<^sub>3.exhaust)

(*We can recover multiplication using meet, join and additive inverse*)
lemma Multiplication_char: "(a * b) = (a \<^bold>\<and> b) \<^bold>\<or> (-a \<^bold>\<and> -b)" 
  by (smt (verit, best) AdditiveInverse.elims AdditiveInverse.simps(2) AdditiveInverse.simps(3) Join.simps(1) Join.simps(3) Join.simps(6) Join.simps(7) Join.simps(8) Join.simps(9) Meet.simps(1) Meet.simps(2) Meet.simps(3) Meet.simps(4) Meet.simps(5) Meet.simps(6) Meet.simps(7) Meet.simps(8) Meet.simps(9) Multiplication.simps(1) Multiplication.simps(2) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(6) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9))


subsection \<open>Residuation\<close>

(*First, observe that the following don't hold for inequalities: *)
lemma "((x + y) \<le> z) \<longleftrightarrow> (x \<le> (z - y))" nitpick oops (*countermodel: addition can 'overflow' (ring is finite)*)
lemma "y \<noteq> 0 \<Longrightarrow> ((x * y) \<le> z) \<longleftrightarrow> (x \<le> (z / y))" nitpick oops (*countermodel*)

abbreviation "RESID f g \<equiv> \<forall>x y. (f x \<le> y) \<longleftrightarrow> (x \<le> g y)"
abbreviation "RESID2 f g \<equiv> \<forall>z. RESID (f z) (g z)"

lemma "RESID2 f g = (\<forall>x y z. (f z x \<le> y) \<longleftrightarrow> (x \<le> g z y))" by blast

(*In fact, left/right residuals, when they exist, are unique*)
lemma "RESID2 f g\<^sub>1 \<and> RESID2 f g\<^sub>2 \<longrightarrow> g\<^sub>1 = g\<^sub>2" 
  using antisym refl (*by metis*) sorry (*TODO: reconstruction takes too long*)
lemma "RESID2 f\<^sub>1 g \<and> RESID2 f\<^sub>2 g \<longrightarrow> f\<^sub>1 = f\<^sub>2" 
  using antisym refl (*by metis*) sorry (*TODO: reconstruction takes too long*)

(*As it happens, there is no right residual to '*' and no left residual to '+' either: *)
lemma "RESID2 (*) g" nitpick[satisfy, expect=none] oops
lemma "RESID2 f (+)" nitpick[satisfy, expect=none] oops

(*But there is (at least) a residuated pair \<langle>f,g\<rangle> to be found... *)
lemma "RESID2 f g" nitpick[satisfy] oops

(*In fact, meet resp. join have right resp left residuals, and we can use nitpick to find them: *)
lemma "RESID2 (\<^bold>\<and>) g" nitpick[satisfy] oops
lemma "RESID2 f (\<^bold>\<or>)" nitpick[satisfy] oops

(*We call meet's right residual: 'implication'. Based upon the truth table generated by nitpick we define:*)
fun Implication::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3" (infixr "\<^bold>\<rightarrow>" 54) where
  "0 \<^bold>\<rightarrow> 0 = 1" |
  "0 \<^bold>\<rightarrow> 1 = 1" |
  "0 \<^bold>\<rightarrow> 2 = 2" |
  "1 \<^bold>\<rightarrow> 0 = 0" |
  "1 \<^bold>\<rightarrow> 1 = 1" |
  "1 \<^bold>\<rightarrow> 2 = 2" |
  "2 \<^bold>\<rightarrow> 0 = 1" |
  "2 \<^bold>\<rightarrow> 1 = 1" |
  "2 \<^bold>\<rightarrow> 2 = 1"

(*We call joins's left residual: 'dual-implication'. Based upon the truth table generated by nitpick we define:*)
fun DualImplication::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3 \<Rightarrow> Z\<^sub>3" (infixl "\<^bold>\<rightharpoonup>" 54) where
  "0 \<^bold>\<rightharpoonup> 0 = 2" |
  "0 \<^bold>\<rightharpoonup> 1 = 1" |
  "0 \<^bold>\<rightharpoonup> 2 = 2" |
  "1 \<^bold>\<rightharpoonup> 0 = 2" |
  "1 \<^bold>\<rightharpoonup> 1 = 2" |
  "1 \<^bold>\<rightharpoonup> 2 = 2" |
  "2 \<^bold>\<rightharpoonup> 0 = 0" |
  "2 \<^bold>\<rightharpoonup> 1 = 1" |
  "2 \<^bold>\<rightharpoonup> 2 = 2"

lemma resid_law1: "RESID2 (\<^bold>\<and>) (\<^bold>\<rightarrow>)" 
  by (smt (verit) AdditiveInverse.elims Implication.simps(1) Implication.simps(2) Implication.simps(3) Implication.simps(4) Implication.simps(5) Implication.simps(6) Implication.simps(7) Implication.simps(8) Implication.simps(9) Meet.simps(1) Meet.simps(2) Meet.simps(3) Meet.simps(4) Meet.simps(5) Meet.simps(6) Meet.simps(7) Meet.simps(8) Meet.simps(9) leq.elims(3) leq.simps(2) leq.simps(5) leq.simps(7))
lemma resid_law2: "RESID2 (\<^bold>\<rightharpoonup>) (\<^bold>\<or>)" 
  by (smt (verit, del_insts) DualImplication.simps(1) DualImplication.simps(2) DualImplication.simps(3) DualImplication.simps(4) DualImplication.simps(5) DualImplication.simps(6) DualImplication.simps(7) DualImplication.simps(8) DualImplication.simps(9) Join.simps(1) Join.simps(2) Join.simps(3) Join.simps(4) Join.simps(5) Join.simps(6) Join.simps(7) Join.simps(8) Join.simps(9) Z\<^sub>3.distinct(3) leq.elims(2) leq.elims(3))

(*More explicitly, we have: *)
lemma "(z \<^bold>\<and>  x \<le> y) \<longleftrightarrow> (x \<le> z \<^bold>\<rightarrow> y)" by (simp add: resid_law1)
lemma "(z \<^bold>\<rightharpoonup> x \<le> y) \<longleftrightarrow> (x \<le> z \<^bold>\<or> y)" by (simp add: resid_law2)

(*However, an analog result for equalities does not hold:*)
lemma "(z \<^bold>\<and> x = y) \<longleftrightarrow> (x = z \<^bold>\<rightarrow> y)" nitpick oops (*countermodel*)
lemma "(z \<^bold>\<rightharpoonup> x = y) \<longleftrightarrow> (x = z \<^bold>\<or> y)" nitpick oops (*countermodel*)

(*Let's add for writing convenience: *)
abbreviation(input) DualImplication_rev (infixr "\<^bold>\<leftharpoonup>" 54) 
  where "x \<^bold>\<leftharpoonup> y \<equiv> y \<^bold>\<rightharpoonup> x" 
abbreviation(input) Implication_rev (infixl "\<^bold>\<leftarrow>" 54) 
  where "x \<^bold>\<leftarrow> y \<equiv> y \<^bold>\<rightarrow> x"

(*In fact the following holds: *)
lemma "(x \<^bold>\<rightarrow> y = 1) \<longleftrightarrow> (x \<le> y)"
  by (smt (verit, ccfv_threshold) AdditiveInverse.elims Implication.simps(1) Implication.simps(2) Implication.simps(3) Implication.simps(4) Implication.simps(5) Implication.simps(6) Implication.simps(7) Implication.simps(8) Implication.simps(9) Z\<^sub>3.distinct(1) leq.elims(3) leq.simps(5) leq.simps(6) leq.simps(7))
lemma "(x \<^bold>\<leftharpoonup> y = 2) \<longleftrightarrow> (x \<le> y)"
  by (smt (verit, best) DualImplication.simps(1) DualImplication.simps(2) DualImplication.simps(3) DualImplication.simps(4) DualImplication.simps(5) DualImplication.simps(6) DualImplication.simps(7) DualImplication.simps(8) DualImplication.simps(9) Z\<^sub>3.simps(4) leq.elims(1))

(*While the following does not hold: *)
lemma "(x \<^bold>\<rightarrow> y \<ge> 0) \<longleftrightarrow> (x \<le> y)" nitpick oops (*counterexample*)
lemma "(x \<^bold>\<leftharpoonup> y \<le> 0) \<longleftrightarrow> (x \<le> y)" nitpick oops (*counterexample*)

(*The previous results justify introducing the following convenient definitions: *)
abbreviation(input) Top ("\<^bold>\<top>")    where "\<^bold>\<top> \<equiv> 1"
abbreviation(input) Bottom ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> 2"

(*Finally, let's find the polynomial representations for the operations discussed above: *)

(*Uses Nitpick to find polynomial coeficients and to compute the table*)
lemma "(\<^bold>\<and>) = poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "(\<^bold>\<or>) = poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "(\<^bold>\<rightarrow>) = poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "(\<^bold>\<rightharpoonup>) = poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops

(*Verifies polynomial representation*)
lemma Meet_polydef:            "(x \<^bold>\<and> y) =  (2\<cdot>x\<^sup>2\<cdot>y\<^sup>2        + x\<^sup>2 + 2\<cdot>x\<cdot>y + 2\<cdot>x + y\<^sup>2  + 2\<cdot>y)" by (smt (verit, best) Addition.simps(1) Addition.simps(2) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) AdditiveInverse.cases Meet.simps(1) Meet.simps(2) Meet.simps(3) Meet.simps(4) Meet.simps(5) Meet.simps(6) Meet.simps(7) Meet.simps(8) Meet.simps(9) Multiplication.simps(1) Multiplication.simps(2) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(6) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9))
lemma Join_polydef:            "(x \<^bold>\<or> y) =   (x\<^sup>2\<cdot>y\<^sup>2       + 2\<cdot>x\<^sup>2 +  x\<cdot>y + 2\<cdot>x + 2\<cdot>y\<^sup>2 + 2\<cdot>y)" by (smt (verit, del_insts) Addition.simps(1) Addition.simps(2) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) AdditiveInverse.elims Join.simps(1) Join.simps(2) Join.simps(3) Join.simps(4) Join.simps(5) Join.simps(6) Join.simps(7) Join.simps(8) Join.simps(9) Multiplication.simps(1) Multiplication.simps(2) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(6) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9))
lemma Implication_polydef:    "(x \<^bold>\<rightarrow> y) =   (x\<^sup>2\<cdot>y\<^sup>2  + x\<^sup>2\<cdot>y + x\<^sup>2 + 2\<cdot>x\<cdot>y  + x + 2\<cdot>y\<^sup>2  + y + 1)" by (smt (verit, ccfv_SIG) Addition.simps(1) Addition.simps(2) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) Implication.simps(1) Implication.simps(2) Implication.simps(3) Implication.simps(4) Implication.simps(5) Implication.simps(6) Implication.simps(7) Implication.simps(8) Implication.simps(9) Multiplication.simps(1) Multiplication.simps(2) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(6) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9) Z\<^sub>3.exhaust)
lemma DualImplication_polydef: "(x \<^bold>\<rightharpoonup> y) = (2\<cdot>x\<^sup>2\<cdot>y\<^sup>2 + x\<^sup>2\<cdot>y + 2\<cdot>x\<^sup>2 + x\<cdot>y  + x  + y\<^sup>2   + y + 2)" by (smt (verit, best) Addition.simps(1) Addition.simps(2) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) AdditiveInverse.cases DualImplication.simps(1) DualImplication.simps(2) DualImplication.simps(3) DualImplication.simps(4) DualImplication.simps(5) DualImplication.simps(6) DualImplication.simps(7) DualImplication.simps(8) DualImplication.simps(9) Multiplication.simps(1) Multiplication.simps(2) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(6) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9))


subsection \<open>Operators\<close>

(*Among all the (3^3 = 27) possible unary operations, we shall first consider those which are both
 order-preserving (aka. monotonic) and either order-increasing or order-decreasing. We shall refer 
 to them as '(positive) operators'.*)

abbreviation(input) "MONO \<phi> \<equiv> \<forall>x y. x \<le> y \<longrightarrow> \<phi> x \<le> \<phi> y"

(*Note that, in the present case, monotonicity ends up being equivalent to distributivity over meets/joins*)
lemma "MONO \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<and> y) = (\<phi> x) \<^bold>\<and> (\<phi> y))" sorry (*TODO: reconstruction takes too long*)
  (* by (smt (z3) Meet_mindef linear leq.elims(1)) *)
lemma "MONO \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<or> y) = (\<phi> x) \<^bold>\<or> (\<phi> y))" sorry (*TODO: reconstruction takes too long*)
  (* unfolding Join_maxdef by (smt (verit, best) linear leq.elims(2)) *)

(*Order increasing/decreasing-ness*)
abbreviation(input) "INCR \<phi> \<equiv> \<forall>x. x \<le> \<phi> x"
abbreviation(input) "DECR \<phi> \<equiv> \<forall>x. \<phi> x \<le> x"

(*There are 6 increasing (resp. decreasing) unary operations in total. Of them, one is not monotonic,
 and two others are trivial (identity or constant). So we have 3 increasing (resp. decreasing) operators
 to consider. We refer to increasing operators as 'closures' (\<C>) and decreasing ones as 'interiors' (\<I>).*)

fun ClosureA::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("\<C>\<^sub>a") where (* a for... nothing in particular *)
  "\<C>\<^sub>a 1 = 1" | 
  "\<C>\<^sub>a 0 = 1" |
  "\<C>\<^sub>a 2 = 0"  

fun ClosureI::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("\<C>\<^sub>i") where (* i for (just) idempotent*) 
  "\<C>\<^sub>i 1 = 1" | 
  "\<C>\<^sub>i 0 = 0" |
  "\<C>\<^sub>i 2 = 0"  

fun ClosureN::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("\<C>\<^sub>n") where (* n for normal (and thus idempotent)*)
  "\<C>\<^sub>n 1 = 1" | 
  "\<C>\<^sub>n 0 = 1" |
  "\<C>\<^sub>n 2 = 2"  

(*Closures are all monotonic and increasing*)
lemma "MONO \<C>\<^sub>a \<and> INCR \<C>\<^sub>a" by (metis ClosureA.elims Z\<^sub>3.distinct(5) Z\<^sub>3.simps(2) Z\<^sub>3.simps(4) leq.elims(2) leq.elims(3))
lemma "MONO \<C>\<^sub>i \<and> INCR \<C>\<^sub>i" by (metis ClosureI.elims Z\<^sub>3.simps(2) Z\<^sub>3.simps(4) Z\<^sub>3.simps(6) leq.elims(2) leq.elims(3))
lemma "MONO \<C>\<^sub>n \<and> INCR \<C>\<^sub>n" by (metis (full_types) ClosureN.elims ClosureN.simps(2) antisym leq.simps(1) leq.simps(2) leq.simps(3))

fun InteriorA::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("\<I>\<^sub>a") where 
  "\<I>\<^sub>a 1 = 0" | 
  "\<I>\<^sub>a 0 = 2" |
  "\<I>\<^sub>a 2 = 2"  

fun InteriorI::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("\<I>\<^sub>i") where  (* i for (just) idempotent*) 
  "\<I>\<^sub>i 1 = 0" | 
  "\<I>\<^sub>i 0 = 0" |
  "\<I>\<^sub>i 2 = 2"  

fun InteriorN::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("\<I>\<^sub>n") where (* n for normal (and thus idempotent)*)
  "\<I>\<^sub>n 1 = 1" | 
  "\<I>\<^sub>n 0 = 2" |
  "\<I>\<^sub>n 2 = 2" 

(*Interiors are all monotonic and decreasing*)
lemma "MONO \<I>\<^sub>a \<and> DECR \<I>\<^sub>a" by (metis InteriorA.elims Z\<^sub>3.distinct(5) Z\<^sub>3.simps(2) Z\<^sub>3.simps(4) leq.elims(2) leq.elims(3))
lemma "MONO \<I>\<^sub>i \<and> DECR \<I>\<^sub>i" by (metis InteriorI.elims antisym Z\<^sub>3.simps(6) leq.elims(3) leq.simps(4))
lemma "MONO \<I>\<^sub>n \<and> DECR \<I>\<^sub>n" by (metis InteriorN.elims refl leq.simps(1) leq.simps(6)) 

(*Now consider the following two properties, dubbed 'normality' and 'idempotence'*)
abbreviation(input) "NORM \<phi> \<equiv> (\<phi> \<^bold>\<top>) = \<^bold>\<top> \<and> (\<phi> \<^bold>\<bottom>) = \<^bold>\<bottom>" (*preserves the top and bottom elements*)
abbreviation(input) "IDEM \<phi> \<equiv> \<forall>x. \<phi>(\<phi> x) = \<phi> x"

(*Note that, in the present case, normality implies idempotency (but not the other way round)*)
lemma "NORM \<phi> \<longrightarrow> IDEM \<phi>" by (metis AdditiveInverse.cases)
lemma "IDEM \<phi> \<longrightarrow> NORM \<phi>" nitpick oops (*countermodel*)

(*We shall now check the properties above for closures and interiors:*)
lemma "IDEM \<C>\<^sub>a" nitpick oops (*counterexample*)
lemma "IDEM \<C>\<^sub>i" by (metis ClosureI.elims)
lemma "NORM \<C>\<^sub>n" by simp
lemma "IDEM \<I>\<^sub>a" nitpick oops (*counterexample*)
lemma "IDEM \<I>\<^sub>i" by (metis InteriorI.elims)
lemma "NORM \<I>\<^sub>n" by simp


subsection \<open>Negations\<close>

(*One of the main characteristics of negations is that of being order-reversing, aka. anti(mono)tonic.*)
abbreviation(input) "ANTI \<phi> \<equiv> \<forall>x y. x \<le> y \<longrightarrow> \<phi> y \<le> \<phi> x"

(*Note that, in the present case, anti(mono)tonicity is equivalent to antidistributivity over 
   meets/joins (which is just algebraic jargon for saying that the De Morgan laws hold). *)
lemma "ANTI \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<and> y) = (\<phi> x) \<^bold>\<or> (\<phi> y))" unfolding Join_maxdef Meet_mindef by (metis (full_types) antisym linear)
lemma "ANTI \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<or> y) = (\<phi> x) \<^bold>\<and> (\<phi> y))" unfolding Join_maxdef Meet_mindef by (metis (full_types) antisym linear)

(*We start by considering the (unique) involutive negation '\<^bold>\<sim>', which, with the given ordering, 
  ends up corresponding to the additive inverse '-' *)
abbreviation(input) "INVOL \<phi> \<equiv> \<forall>x. \<phi>(\<phi> x) = x"

fun Negation::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("\<^bold>\<sim>") where
  "\<^bold>\<sim>1 = 2" |
  "\<^bold>\<sim>0 = 0" |
  "\<^bold>\<sim>2 = 1"

lemma Negation_char: "\<^bold>\<sim>x = -x" by (metis AdditiveInverse.elims AdditiveInverse.simps(1) Negation.elims Negation.simps(2))

lemma "ANTI \<^bold>\<sim>" by (metis Negation.simps(1) Negation.simps(3) Z\<^sub>3.distinct(1) Z\<^sub>3.distinct(5) Z\<^sub>3.simps(4) leq.elims(2) leq.elims(3))
lemma "INVOL \<^bold>\<sim>" by (metis (full_types) Negation.cases Negation.simps(1) Negation.simps(2) Negation.simps(3))

(*The involutive negation is special, among others, because it gives some dualities:*)
lemma "\<C>\<^sub>a \<circ> \<^bold>\<sim> = \<^bold>\<sim> \<circ> \<I>\<^sub>a" by (metis (full_types) ClosureA.simps(1) ClosureA.simps(2) ClosureA.simps(3) InteriorA.elims Negation.simps(1) Negation.simps(2) Negation.simps(3))
lemma "\<C>\<^sub>i \<circ> \<^bold>\<sim> = \<^bold>\<sim> \<circ> \<I>\<^sub>i" by (metis ClosureI.simps(1) ClosureI.simps(2) ClosureI.simps(3) InteriorI.elims InteriorI.simps(3) Negation.elims Negation.simps(2) Z\<^sub>3.distinct(1))
lemma "\<C>\<^sub>n \<circ> \<^bold>\<sim> = \<^bold>\<sim> \<circ> \<I>\<^sub>n" by (metis ClosureN.simps(1) ClosureN.simps(2) ClosureN.simps(3) InteriorN.simps(1) InteriorN.simps(2) InteriorN.simps(3) Negation.cases Negation.simps(1) Negation.simps(2) Negation.simps(3))

(*In fact, composing the involutive negation with any (monotonic) operator gives an (antitonic) negation*)
lemma "MONO \<phi> \<longleftrightarrow> ANTI (\<^bold>\<sim> \<circ> \<phi>)" by (smt (verit, best) Negation.simps(1) Negation.simps(2) Negation.simps(3) Z\<^sub>3.simps(6) leq.elims(1)) 
lemma "MONO \<phi> \<longleftrightarrow> ANTI (\<phi> \<circ> \<^bold>\<sim>)" by (smt (verit, del_insts) Negation.elims Negation.simps(2) Negation.simps(3) antisym refl leq.simps(1) leq.simps(2) leq.simps(6)) 
(*And viceversa*)
lemma "ANTI \<phi> \<longleftrightarrow> MONO (\<^bold>\<sim> \<circ> \<phi>)" by (smt (verit, ccfv_SIG) Negation.elims Z\<^sub>3.simps(2) Z\<^sub>3.simps(4) leq.elims(3) leq.simps(5) leq.simps(6))
lemma "ANTI \<phi> \<longleftrightarrow> MONO (\<phi> \<circ> \<^bold>\<sim>)" by (smt (verit, best) Negation.simps(1) Negation.simps(2) Negation.simps(3) linear leq.elims(2) leq.simps(7))

(*Let's now consider the following convenient two negation(-like) operations: *)
fun NegationC::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("\<^bold>\<frown>") where
  "\<^bold>\<frown>1 = 2" |
  "\<^bold>\<frown>0 = 1" | 
  "\<^bold>\<frown>2 = 1" 
fun NegationI::"Z\<^sub>3 \<Rightarrow> Z\<^sub>3" ("\<^bold>\<smile>") where
  "\<^bold>\<smile>1 = 2" |
  "\<^bold>\<smile>0 = 2" |
  "\<^bold>\<smile>2 = 1"

(*As said before, they are obtained by composing the involutive negation with a (monotonic) operator.*)
lemma NegationC_char: "\<^bold>\<frown> = \<C>\<^sub>n \<circ> \<^bold>\<sim>" by (metis ClosureN.simps(1) ClosureN.simps(2) ClosureN.simps(3) NegationC.elims Negation.simps(1) Negation.simps(2) Negation.simps(3)) 
lemma NegationI_char: "\<^bold>\<smile> = \<I>\<^sub>n \<circ> \<^bold>\<sim>" by (metis InteriorN.simps(1) InteriorN.simps(2) InteriorN.simps(3) NegationI.elims Negation.simps(1) Negation.simps(2) Negation.simps(3))

(*They satisfy several useful properties*)
lemma "ANTI \<^bold>\<frown>" by (metis NegationC.elims leq.elims(2) leq.simps(1) leq.simps(3))
lemma "ANTI \<^bold>\<smile>" by (metis NegationI.elims refl leq.elims(2) leq.simps(1))

(*Both negations, though not involutive, still satisfy double negation elimination/introduction*)
lemma "INVOL \<^bold>\<frown>" nitpick oops (*counterexample*)
lemma "INVOL \<^bold>\<smile>" nitpick oops (*counterexample*)
lemma "\<^bold>\<frown>(\<^bold>\<frown>x) \<le> x" by (metis NegationC.simps(1) NegationC.simps(2) NegationC.simps(3) Z\<^sub>3.distinct(3) Z\<^sub>3.simps(6) leq.elims(3))
lemma "x \<le> \<^bold>\<smile>(\<^bold>\<smile>x)" using leq.elims(3) by fastforce

(*As well as the following properties (algebraic counterparts of 'excluded middle' and 'ex-contradictio' *)
lemma "\<^bold>\<frown>x \<^bold>\<or> x = \<^bold>\<top>" by (metis Join.simps(4) Join.simps(6) Join.simps(8) NegationC.elims)
lemma "\<^bold>\<smile>x \<^bold>\<and> x = \<^bold>\<bottom>" by (metis Meet.simps(6) Meet.simps(7) Meet.simps(8) NegationI.elims)

(*We fact in fact the following alternative definitions: *)
lemma NegationC_char2: "\<^bold>\<frown>x = (\<^bold>\<top> \<^bold>\<leftharpoonup> x)" by (metis DualImplication.simps(2) DualImplication.simps(5) DualImplication.simps(8) NegationC.simps(1) NegationC.simps(2) NegationC.simps(3) Z\<^sub>3.exhaust)
lemma NegationI_char2: "\<^bold>\<smile>x = (x \<^bold>\<rightarrow> \<^bold>\<bottom>)" by (metis Implication.simps(3) Implication.simps(6) Implication.simps(9) NegationI.elims)

(*Let us introduce the following convenient binary operations based upon negation:*)
abbreviation(input) Nmeet (infixl "\<^bold>\<up>" 56) (*aka. Sheffer stroke*)
  where "x \<^bold>\<up> y \<equiv> \<^bold>\<sim>(x \<^bold>\<and> y)"
abbreviation(input) Njoin (infixl "\<^bold>\<down>" 55) (*aka. Peirce arrow or Quine dagger*)
  where "x \<^bold>\<down> y \<equiv> \<^bold>\<sim>(x \<^bold>\<or> y)"

(*Finally, let us obtain convenient polynomial representations of the operators discussed above: *)
lemma "\<C>\<^sub>n = poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "\<I>\<^sub>n = poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "\<^bold>\<sim> = poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "\<^bold>\<frown> = poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "\<^bold>\<smile> = poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "(\<^bold>\<up>) = poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "(\<^bold>\<down>) = poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly2 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops

lemma ClosureN_polydef:  "\<C>\<^sub>n x = 2\<cdot>x\<^sup>2 + x + 1" by (smt (verit, best) Addition.simps(1) Addition.simps(2) Addition.simps(5) Addition.simps(8) Addition.simps(9) ClosureN.elims Multiplication.simps(1) Multiplication.simps(5) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9))
lemma InteriorN_polydef: "\<I>\<^sub>n x = x\<^sup>2 + x + 2" by (smt (verit, best) Addition.simps(1) Addition.simps(3) Addition.simps(5) Addition.simps(6) Addition.simps(9) InteriorN.elims Multiplication.simps(1) Multiplication.simps(5) Multiplication.simps(9))
lemma Negation_polydef:   "\<^bold>\<sim>x = 2\<cdot>x" by (metis (full_types) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9) Negation.elims)
lemma NegationC_polydef: "\<^bold>\<frown>x = 2\<cdot>x\<^sup>2 + 2\<cdot>x + 1" by (smt (verit, best) Addition.simps(1) Addition.simps(2) Addition.simps(5) Addition.simps(8) Addition.simps(9) Multiplication.simps(1) Multiplication.simps(5) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9) NegationC.elims)
lemma NegationI_polydef: "\<^bold>\<smile>x = x\<^sup>2 + 2\<cdot>x + 2" by (smt (verit, ccfv_threshold) Addition.simps(1) Addition.simps(3) Addition.simps(5) Addition.simps(6) Addition.simps(9) Multiplication.simps(1) Multiplication.simps(5) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9) NegationI.elims)
lemma Nmeet_polydef: "x \<^bold>\<up> y = x\<^sup>2\<cdot>y\<^sup>2 + 2\<cdot>x\<^sup>2 + x\<cdot>y + x + 2\<cdot>y\<^sup>2 + y" sorry (*TODO: reconstruction takes too long*)
  (* by (smt (z3) Addition.simps(1) Addition.simps(2) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) Meet.elims Multiplication.simps(1) Multiplication.simps(2) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(6) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9) Negation.simps(1) Negation.simps(2) Negation.simps(3))  *)
lemma Njoin_polydef: "x \<^bold>\<down> y = 2\<cdot>x\<^sup>2\<cdot>y\<^sup>2 + x\<^sup>2 + 2\<cdot>x\<cdot>y + x + y\<^sup>2 + y" sorry (*TODO: reconstruction takes too long*)
  (* by (smt (z3) Addition.simps(1) Addition.simps(2) Addition.simps(3) Addition.simps(4) Addition.simps(5) Addition.simps(6) Addition.simps(7) Addition.simps(8) Addition.simps(9) ClosureI.elims Join.simps(1) Join.simps(2) Join.simps(3) Join.simps(4) Join.simps(5) Join.simps(6) Join.simps(7) Join.simps(8) Join.simps(9) Multiplication.simps(1) Multiplication.simps(2) Multiplication.simps(3) Multiplication.simps(4) Multiplication.simps(5) Multiplication.simps(6) Multiplication.simps(7) Multiplication.simps(8) Multiplication.simps(9) Negation.simps(1) Negation.simps(2) Negation.simps(3)) *)


named_theorems polydefs
declare Meet_polydef[polydefs] Join_polydef[polydefs] 
        Implication_polydef[polydefs] DualImplication_polydef[polydefs]
        ClosureN_polydef[polydefs] InteriorN_polydef[polydefs]
        NegationI_polydef[polydefs] NegationC_polydef[polydefs] Negation_polydef[polydefs]
        Nmeet_polydef[polydefs] Njoin_polydef[polydefs]
end