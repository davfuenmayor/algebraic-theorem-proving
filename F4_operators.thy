(**************************************************************)
(*           Copyright (c) 2024 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory F4_operators
imports F4_orderA F4_orderL
begin

subsection \<open>Operators\<close>

(*Among all the (4^4 = 256) possible unary operations, we shall consider only a couple of examples that
 are both order-preserving (aka. monotonic) and either order-increasing or order-decreasing (wrt. either
 the A- or the L-ordering). We shall refer to them as '(positive) operators'.*)

abbreviation(input) monotonic_A ("MONO\<^sup>A")
  where "MONO\<^sup>A \<phi> \<equiv> \<forall>x y. x \<sqsubseteq> y \<longrightarrow> \<phi> x \<sqsubseteq> \<phi> y"
abbreviation(input) monotonic_L ("MONO\<^sup>L")
  where "MONO\<^sup>L \<phi> \<equiv> \<forall>x y. x \<le> y \<longrightarrow> \<phi> x \<le> \<phi> y"

(*Note that, monotonicity is equivalent to upwards (downwards) distributivity over meets (joins)*)
lemma "MONO\<^sup>A \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<sqinter> y) \<sqsubseteq> (\<phi> x) \<^bold>\<sqinter> (\<phi> y))" by (smt (z3) MeetA.simps leqA.simps F\<^sub>4.exhaust)
lemma "MONO\<^sup>A \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<squnion> y) \<sqsupseteq> (\<phi> x) \<^bold>\<squnion> (\<phi> y))" by (smt (z3) JoinA.simps leqA.simps F\<^sub>4.exhaust)

lemma "MONO\<^sup>L \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<and> y) \<le> (\<phi> x) \<^bold>\<and> (\<phi> y))" by (smt (z3) MeetL.simps leqL.simps F\<^sub>4.exhaust)
lemma "MONO\<^sup>L \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<or> y) \<ge> (\<phi> x) \<^bold>\<or> (\<phi> y))" by (smt (z3) JoinL.simps leqL.simps F\<^sub>4.exhaust)

(*Order increasing/decreasing-ness*)
abbreviation(input) increasing_A ("INCR\<^sup>A")
  where "INCR\<^sup>A \<phi> \<equiv> \<forall>x. x \<sqsubseteq> \<phi> x"
abbreviation(input) decreasing_A ("DECR\<^sup>A")
  where "DECR\<^sup>A \<phi> \<equiv> \<forall>x. \<phi> x \<sqsubseteq> x"

abbreviation(input) increasing_L ("INCR\<^sup>L")
  where "INCR\<^sup>L \<phi> \<equiv> \<forall>x. x \<le> \<phi> x"
abbreviation(input) decreasing_L ("DECR\<^sup>L")
  where "DECR\<^sup>L \<phi> \<equiv> \<forall>x. \<phi> x \<le> x"

(* We refer to increasing operators as 'closures' (\<C>) and decreasing ones as 'interiors' (\<I>).*)
fun Closure_A::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("\<C>\<^sup>A") where
  "\<C>\<^sup>A b = b" | 
  "\<C>\<^sup>A 1 = b" |
  "\<C>\<^sup>A 0 = b" |
  "\<C>\<^sup>A a = a"
fun Interior_A::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("\<I>\<^sup>A") where
  "\<I>\<^sup>A b = b" | 
  "\<I>\<^sup>A 1 = a" |
  "\<I>\<^sup>A 0 = a" |
  "\<I>\<^sup>A a = a"
fun Closure_L::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("\<C>\<^sup>L") where
  "\<C>\<^sup>L 1 = 1" | 
  "\<C>\<^sup>L b = 1" |
  "\<C>\<^sup>L a = 1" |
  "\<C>\<^sup>L 0 = 0"
fun Interior_L::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("\<I>\<^sup>L") where
  "\<I>\<^sup>L 1 = 1" | 
  "\<I>\<^sup>L b = 0" |
  "\<I>\<^sup>L a = 0" |
  "\<I>\<^sup>L 0 = 0"

(*Closures are monotonic and increasing*)
lemma "MONO\<^sup>A \<C>\<^sup>A \<and> INCR\<^sup>A \<C>\<^sup>A" by (smt (verit) Closure_A.simps leqA.simps leqA.elims)
lemma "MONO\<^sup>L \<C>\<^sup>L \<and> INCR\<^sup>L \<C>\<^sup>L" by (smt (verit) Closure_L.simps leqL.simps leqL.elims)
(*Interiors are monotonic and decreasing*)
lemma "MONO\<^sup>A \<I>\<^sup>A \<and> DECR\<^sup>A \<I>\<^sup>A" by (smt (verit) Interior_A.simps leqA.simps leqA.elims)  
lemma "MONO\<^sup>L \<I>\<^sup>L \<and> DECR\<^sup>L \<I>\<^sup>L" by (smt (verit) Interior_L.simps leqL.simps leqL.elims) 

(*The following property, dubbed 'normality', corresponds to preservation of top and bottom*)
abbreviation(input) normal_A ("NORM\<^sup>A") 
  where "NORM\<^sup>A \<phi> \<equiv> (\<phi> \<^bold>\<top>\<^sup>A) = \<^bold>\<top>\<^sup>A \<and> (\<phi> \<^bold>\<bottom>\<^sup>A) = \<^bold>\<bottom>\<^sup>A" 
abbreviation(input) normal_L ("NORM\<^sup>L") 
  where "NORM\<^sup>L \<phi> \<equiv> (\<phi> \<^bold>\<top>\<^sup>L) = \<^bold>\<top>\<^sup>L \<and> (\<phi> \<^bold>\<bottom>\<^sup>L) = \<^bold>\<bottom>\<^sup>L" 

(*Finally, let's consider 'idempotence'*)
abbreviation(input) "IDEM \<phi> \<equiv> \<forall>x. \<phi>(\<phi> x) = \<phi> x"

(*We shall now check the properties above for closures and interiors:*)
lemma "NORM\<^sup>A \<C>\<^sup>A" by simp
lemma "NORM\<^sup>L \<C>\<^sup>L" by simp
lemma "IDEM \<C>\<^sup>A" by (smt (z3) Closure_A.elims)
lemma "IDEM \<C>\<^sup>L" by (smt (z3) Closure_L.elims)  
lemma "NORM\<^sup>A \<I>\<^sup>A" by simp
lemma "NORM\<^sup>L \<I>\<^sup>L" by simp
lemma "IDEM \<I>\<^sup>A" by (smt (z3) Interior_A.elims)
lemma "IDEM \<I>\<^sup>L" by (smt (z3) Interior_L.elims)


subsection \<open>Negations\<close>

(*One of the main characteristics of negations is that of being order-reversing, aka. anti(mono)tonic.*)
abbreviation(input) antitonic_A ("ANTI\<^sup>A")
  where "ANTI\<^sup>A \<phi> \<equiv> \<forall>x y. x \<sqsubseteq> y \<longrightarrow> \<phi> y  \<sqsubseteq> \<phi> x"
abbreviation(input) antitonic_L ("ANTI\<^sup>L")
  where "ANTI\<^sup>L \<phi> \<equiv> \<forall>x y. x \<le> y \<longrightarrow> \<phi> y  \<le> \<phi> x"

(*Note that anti(mono)tonicity is equivalent to downwards (upwards) antidistributivity over meets (joins).*)
lemma "ANTI\<^sup>A \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<sqinter> y) \<sqsupseteq> (\<phi> x) \<^bold>\<squnion> (\<phi> y))" by (smt (z3) MeetA.simps JoinA.simps leqA.simps F\<^sub>4.exhaust)
lemma "ANTI\<^sup>A \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<squnion> y) \<sqsubseteq> (\<phi> x) \<^bold>\<sqinter> (\<phi> y))" by (smt (z3) MeetA.simps JoinA.simps leqA.simps F\<^sub>4.exhaust) 
lemma "ANTI\<^sup>L \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<and> y) \<ge> (\<phi> x) \<^bold>\<or> (\<phi> y))" by (smt (z3) MeetL.simps JoinL.simps leqL.simps F\<^sub>4.exhaust) 
lemma "ANTI\<^sup>L \<phi> \<longleftrightarrow> (\<forall>x y. \<phi>(x \<^bold>\<or> y) \<le> (\<phi> x) \<^bold>\<and> (\<phi> y))" by (smt (verit) MeetL.simps JoinL.simps leqL.simps F\<^sub>4.exhaust)

(*Another important (though arguably not essential) property of negations is involutivity*)
abbreviation(input) "INVOL \<phi> \<equiv> \<forall>x. \<phi>(\<phi> x) = x"

(*We start by considering the following operation (\<^bold>\<midarrow>) which we shall call 'classical negation' *)
fun NegationClass::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("\<^bold>\<midarrow>") where
  "\<^bold>\<midarrow>b = a" |
  "\<^bold>\<midarrow>0 = 1" |
  "\<^bold>\<midarrow>1 = 0" |
  "\<^bold>\<midarrow>a = b" 

lemma "ANTI\<^sup>A \<^bold>\<midarrow>" by (smt (verit) NegationClass.simps leqA.elims leqA.simps)
lemma "ANTI\<^sup>L \<^bold>\<midarrow>" by (smt (verit) NegationClass.simps leqL.elims leqL.simps)
lemma "INVOL \<^bold>\<midarrow>" by (smt (verit) NegationClass.simps F\<^sub>4.exhaust)

(*'Excluded middle' (tertium non datur, TND) and 'explosion' (ex contradictione quodlibet, ECQ) hold*)
lemma TND_A: "\<^bold>\<midarrow>x \<^bold>\<squnion> x = \<^bold>\<top>\<^sup>A" by (smt (z3) JoinA.simps NegationClass.elims)
lemma ECQ_A: "\<^bold>\<midarrow>x \<^bold>\<sqinter> x = \<^bold>\<bottom>\<^sup>A" by (smt (z3) MeetA.simps NegationClass.elims)
lemma TND_L: "\<^bold>\<midarrow>x \<^bold>\<or> x = \<^bold>\<top>\<^sup>L" by (smt (z3) JoinL.simps NegationClass.elims)
lemma ECQ_L: "\<^bold>\<midarrow>x \<^bold>\<and> x = \<^bold>\<bottom>\<^sup>L" by (smt (z3) MeetL.simps NegationClass.elims)

(*De Morgan laws hold in all cases*)
lemma "\<^bold>\<midarrow>(x \<^bold>\<squnion> y) = (\<^bold>\<midarrow>x) \<^bold>\<sqinter> (\<^bold>\<midarrow>y)" by (smt (z3) MeetA.simps JoinA.simps NegationClass.elims)
lemma "\<^bold>\<midarrow>(x \<^bold>\<sqinter> y) = (\<^bold>\<midarrow>x) \<^bold>\<squnion> (\<^bold>\<midarrow>y)" by (smt (z3) MeetA.simps JoinA.simps NegationClass.elims)
lemma "\<^bold>\<midarrow>(x \<^bold>\<or> y) = (\<^bold>\<midarrow>x) \<^bold>\<and> (\<^bold>\<midarrow>y)" by (smt (z3) MeetL.simps JoinL.simps NegationClass.elims)
lemma "\<^bold>\<midarrow>(x \<^bold>\<and> y) = (\<^bold>\<midarrow>x) \<^bold>\<or> (\<^bold>\<midarrow>y)" by (smt (z3) MeetL.simps JoinL.simps NegationClass.elims)

(*Closures and interiors are dual wrt. classical negation *)
lemma "\<C>\<^sup>A \<circ> \<^bold>\<midarrow> = \<^bold>\<midarrow> \<circ> \<I>\<^sup>A" by (metis Closure_A.simps Interior_A.simps MultiplicativeInverse.cases NegationClass.simps) 
lemma "\<C>\<^sup>L \<circ> \<^bold>\<midarrow> = \<^bold>\<midarrow> \<circ> \<I>\<^sup>L" by (metis Closure_L.simps Interior_L.simps MultiplicativeInverse.cases NegationClass.simps)

(*We have in fact the following alternative definitions for the classical negation: *)
lemma "\<^bold>\<midarrow>x = (\<^bold>\<top>\<^sup>A \<^bold>\<hookleftarrow> x)" by (smt (z3) DualImplicationA.simps NegationClass.simps F\<^sub>4.exhaust)
lemma "\<^bold>\<midarrow>x = (\<^bold>\<top>\<^sup>L \<^bold>\<leftharpoonup> x)" by (smt (z3) DualImplicationL.simps NegationClass.simps F\<^sub>4.exhaust)
lemma "\<^bold>\<midarrow>x = (x \<^bold>\<Rightarrow> \<^bold>\<bottom>\<^sup>A)" by (smt (z3) ImplicationA.simps NegationClass.simps F\<^sub>4.exhaust)
lemma "\<^bold>\<midarrow>x = (x \<^bold>\<rightarrow> \<^bold>\<bottom>\<^sup>L)" by (smt (z3) ImplicationL.simps NegationClass.simps F\<^sub>4.exhaust)


(*We shall now consider the following involutive operations that behave as negation-like operators.*)

(*Let us start with the multiplicative inverse (\<inverse>)*)
notation(input) MultiplicativeInverse ("'(\<inverse>')") (*convenient notation for reference*)

lemma "ANTI\<^sup>A (\<inverse>)" by (smt (z3) MultiplicativeInverse.elims leqA.simps)
lemma "ANTI\<^sup>L (\<inverse>)" nitpick oops (*countermodel*)
lemma "INVOL (\<inverse>)" by (smt (z3) MultiplicativeInverse.simps F\<^sub>4.exhaust)

(*Let us now introduce the following operation (\<^bold>\<not>), called 'de Morgan negation'*)
fun NegationDM::"F\<^sub>4 \<Rightarrow> F\<^sub>4" ("\<^bold>\<not>") where
  "\<^bold>\<not>b = b" |
  "\<^bold>\<not>0 = 1" |
  "\<^bold>\<not>1 = 0" |
  "\<^bold>\<not>a = a"

lemma "ANTI\<^sup>A \<^bold>\<not>" nitpick oops (*countermodel*)
lemma "ANTI\<^sup>L \<^bold>\<not>" by (smt (verit) NegationDM.simps leqL.elims leqL.simps)
lemma "INVOL \<^bold>\<not>" by (smt (verit) NegationDM.simps F\<^sub>4.exhaust)

lemma "(\<^bold>\<not>) = \<^bold>\<midarrow> \<circ> (\<inverse>)" by (metis MultiplicativeInverse.simps NegationClass.simps NegationDM.simps F\<^sub>4.exhaust)
lemma "\<^bold>\<midarrow> = (\<^bold>\<not>) \<circ> (\<inverse>)" by (metis MultiplicativeInverse.simps NegationClass.simps NegationDM.simps F\<^sub>4.exhaust)

(*'Excluded middle' (tertium non datur, TND) and 'explosion' (ex contradictione quodlibet, ECQ) don't hold*)
lemma "\<^bold>\<not>x \<^bold>\<squnion> x = \<^bold>\<top>\<^sup>A" nitpick oops (*countermodel*)
lemma "\<^bold>\<not>x \<^bold>\<sqinter> x = \<^bold>\<bottom>\<^sup>A" nitpick oops (*countermodel*)
lemma "\<^bold>\<not>x \<^bold>\<or> x = \<^bold>\<top>\<^sup>L" nitpick oops (*countermodel*)
lemma "\<^bold>\<not>x \<^bold>\<and> x = \<^bold>\<bottom>\<^sup>L" nitpick oops (*countermodel*)

lemma "x\<inverse> \<^bold>\<squnion> x = \<^bold>\<top>\<^sup>A" nitpick oops (*countermodel*)
lemma "x\<inverse> \<^bold>\<sqinter> x = \<^bold>\<bottom>\<^sup>A" nitpick oops (*countermodel*)
lemma "x\<inverse> \<^bold>\<or> x = \<^bold>\<top>\<^sup>L" nitpick oops (*countermodel*)
lemma "x\<inverse> \<^bold>\<and> x = \<^bold>\<bottom>\<^sup>L" nitpick oops (*countermodel*)

(*De Morgan laws hold in some cases: *)
lemma "\<^bold>\<not>(x \<^bold>\<squnion> y) = (\<^bold>\<not>x) \<^bold>\<sqinter> (\<^bold>\<not>y)" nitpick oops (*countermodel*)
lemma "\<^bold>\<not>(x \<^bold>\<sqinter> y) = (\<^bold>\<not>x) \<^bold>\<squnion> (\<^bold>\<not>y)" nitpick oops (*countermodel*)
lemma "\<^bold>\<not>(x \<^bold>\<or> y) = (\<^bold>\<not>x) \<^bold>\<and> (\<^bold>\<not>y)" by (smt (z3) JoinL.simps MeetL.simps NegationDM.simps F\<^sub>4.exhaust)
lemma "\<^bold>\<not>(x \<^bold>\<and> y) = (\<^bold>\<not>x) \<^bold>\<or> (\<^bold>\<not>y)" by (smt (z3) JoinL.simps MeetL.simps NegationDM.simps F\<^sub>4.exhaust)

lemma "(x \<^bold>\<or> y)\<inverse> = x\<inverse> \<^bold>\<and> y\<inverse>" nitpick oops (*countermodel*)
lemma "(x \<^bold>\<and> y)\<inverse> = x\<inverse> \<^bold>\<or> y\<inverse>" nitpick oops (*countermodel*)
lemma "(x \<^bold>\<squnion> y)\<inverse> = x\<inverse> \<^bold>\<sqinter> y\<inverse>" by (smt (z3) JoinA.simps MeetA.simps MultiplicativeInverse.simps F\<^sub>4.exhaust)
lemma "(x \<^bold>\<sqinter> y)\<inverse> = x\<inverse> \<^bold>\<squnion> y\<inverse>" by (smt (z3) JoinA.simps MeetA.simps MultiplicativeInverse.simps F\<^sub>4.exhaust)


(*Finally, let us introduce the following convenient binary operations based upon negation:*)
abbreviation(input) NmeetA (infixl "\<^bold>\<Up>" 56) (*aka. Sheffer stroke*)
  where "x \<^bold>\<Up> y \<equiv> \<^bold>\<midarrow>(x \<^bold>\<sqinter> y)"
abbreviation(input) NjoinA (infixl "\<^bold>\<Down>" 55) (*aka. Peirce arrow or Quine dagger*)
  where "x \<^bold>\<Down> y \<equiv> \<^bold>\<midarrow>(x \<^bold>\<squnion> y)"
abbreviation(input) NmeetL (infixl "\<^bold>\<up>" 56) (*aka. Sheffer stroke*)
  where "x \<^bold>\<up> y \<equiv> \<^bold>\<midarrow>(x \<^bold>\<and> y)"
abbreviation(input) NjoinL (infixl "\<^bold>\<down>" 55) (*aka. Peirce arrow or Quine dagger*)
  where "x \<^bold>\<down> y \<equiv> \<^bold>\<midarrow>(x \<^bold>\<or> y)"

(*We obtain convenient polynomial representations of the operators discussed above: *)
lemma "\<C>\<^sup>A = poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "\<I>\<^sup>A = poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "\<C>\<^sup>L = poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "\<I>\<^sup>L = poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "(\<^bold>\<midarrow>) = poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "(\<inverse>) = poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "(\<^bold>\<not>) = poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" nitpick[satisfy, eval="poly1 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] oops
lemma "(\<^bold>\<Up>) = poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" 
  (* nitpick[satisfy, eval="poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] *) oops
lemma "(\<^bold>\<Down>) = poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" 
  (* nitpick[satisfy, eval="poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] *) oops
lemma "(\<^bold>\<up>) = poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" 
  (* nitpick[satisfy, eval="poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] *) oops
lemma "(\<^bold>\<down>) = poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0" 
  (* nitpick[satisfy, eval="poly2 c\<^sub>1\<^sub>5 c\<^sub>1\<^sub>4 c\<^sub>1\<^sub>3 c\<^sub>1\<^sub>2 c\<^sub>1\<^sub>1 c\<^sub>1\<^sub>0 c\<^sub>9 c\<^sub>8 c\<^sub>7 c\<^sub>6 c\<^sub>5 c\<^sub>4 c\<^sub>3 c\<^sub>2 c\<^sub>1 c\<^sub>0"] *)  oops

lemma ClosureA_polydef:  "\<C>\<^sup>A x = x\<^sup>3 + a\<cdot>x\<^sup>2 + b\<cdot>x + b" by (smt (z3) Addition.simps Multiplication.simps Closure_A.simps F\<^sub>4.exhaust)
lemma InteriorA_polydef: "\<I>\<^sup>A x = x\<^sup>3 + b\<cdot>x\<^sup>2 + a\<cdot>x + a" by (smt (z3) Addition.simps Multiplication.simps Interior_A.simps F\<^sub>4.exhaust)
lemma ClosureL_polydef:  "\<C>\<^sup>L x = x\<^sup>3" by (smt (z3) Addition.simps Multiplication.simps Closure_L.simps F\<^sub>4.exhaust)
lemma InteriorL_polydef: "\<I>\<^sup>L x = x\<^sup>3 + x\<^sup>2 + x"  by (smt (z3) Addition.simps Multiplication.simps Interior_L.simps F\<^sub>4.exhaust)
lemma NegationClass_polydef:         "\<^bold>\<midarrow>x = x + 1" by (smt (z3) Addition.simps NegationClass.elims)
lemma MultiplicativeInverse_polydef: "x\<inverse> = x\<^sup>2" by (smt (z3) Multiplication.simps MultiplicativeInverse.elims)
lemma NegationDM_polydef:            "\<^bold>\<not>x = x\<^sup>2 + 1" by (smt (z3) Addition.simps Multiplication.simps NegationDM.elims)
lemma NmeetA_polydef: "x \<^bold>\<Up> y = x\<^sup>2\<cdot>y\<^sup>2 + x\<^sup>2\<cdot>y + x\<^sup>2 + x\<cdot>y\<^sup>2 + b\<cdot>x + y\<^sup>2 + b\<cdot>y + 1" by (simp add: MeetA_polydef NegationClass_polydef)
lemma NjoinA_polydef: "x \<^bold>\<Down> y = x\<^sup>2\<cdot>y\<^sup>2 + x\<^sup>2\<cdot>y + x\<^sup>2 + x\<cdot>y\<^sup>2 + a\<cdot>x + y\<^sup>2 + a\<cdot>y + 1" by (simp add: JoinA_polydef NegationClass_polydef)
lemma NmeetL_polydef: "x \<^bold>\<up> y = x\<^sup>2\<cdot>y\<^sup>2 + x\<^sup>2\<cdot>y + x\<cdot>y\<^sup>2 + 1" by (simp add: MeetL_polydef NegationClass_polydef)
lemma NjoinL_polydef: "x \<^bold>\<down> y = x\<^sup>2\<cdot>y\<^sup>2 + x\<^sup>2\<cdot>y + x\<cdot>y\<^sup>2 + x + y + 1" by (simp add: JoinL_polydef NegationClass_polydef)

declare ClosureA_polydef[polydefs] InteriorA_polydef[polydefs] ClosureL_polydef[polydefs] InteriorL_polydef[polydefs]
        NegationClass_polydef[polydefs] MultiplicativeInverse_polydef[polydefs] NegationDM_polydef[polydefs]

end