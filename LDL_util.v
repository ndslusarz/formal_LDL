Require Import Coq.Program.Equality.

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.

(******************************************************************************)
(*                               Utilities                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Local Open Scope ring_scope.

Section hyperbolic_function.
Variable R : realType.

Definition sinh (x : R) := (expR x - expR (- x)) / 2.
Definition cosh (x : R) := (expR x + expR (- x)) / 2.
Definition tanh (x : R) := sinh x / cosh x.

End hyperbolic_function.

Notation "'nondecreasing_fun' f" := ({homo f : n m / (n <= m)%O >-> (n <= m)%O})
  (at level 10).
Notation "'nonincreasing_fun' f" := ({homo f : n m / (n <= m)%O >-> (n >= m)%O})
  (at level 10).
Notation "'increasing_fun' f" := ({mono f : n m / (n <= m)%O >-> (n <= m)%O})
  (at level 10).
Notation "'decreasing_fun' f" := ({mono f : n m / (n <= m)%O >-> (n >= m)%O})
  (at level 10).

Section nameme.
Context {R : numDomainType}.

Definition sumR (Es : seq R) : R := \sum_(i <- Es) i.
Definition prodR (Es : seq R) : R := \prod_(i <- Es) i.
Definition product_dl_prod : R -> R -> R := (fun a1 a2 => a1 + a2 - a1 * a2).
Definition product_dl_prodR (Es : seq R) : R := \big[product_dl_prod/0]_(i <- Es) i.
Definition minR (Es : seq R) : R := \big[minr/1]_(i <- Es) i.
Definition maxR (Es : seq R) : R := \big[maxr/0]_(i <- Es) i.

Definition sumE (Es : seq \bar R) : \bar R := \sum_(i <- Es) i.
Definition minE (Es : seq \bar R) : \bar R := \big[mine/+oo%E]_(i <- Es) i.

End nameme.

Lemma sum_01{R : numDomainType} (I : eqType) (s : seq I) (f : I -> R) :
  (forall i, i \in s -> f i <= 1) -> \sum_(i <- s) f i <= (size s)%:R.
Proof.
move=> s01; rewrite -sum1_size natr_sum big_seq [leRHS]big_seq.
by rewrite ler_sum// => r /s01 /andP[].
Qed.

Lemma In_in (I : eqType) (s : seq I) e : e \in s <-> List.In e s.
Proof.
elim: s => //= h t ih; split=> [|[<-|/ih] ].
- by rewrite inE => /predU1P[->|/ih]; [left|right].
- by rewrite mem_head.
- by rewrite inE => ->; rewrite orbT.
Qed.

Lemma maxr01 {R : realType} (x : R) : (maxr x 0 == 1) = (x == 1).
Proof. rewrite/maxr; case: ifP=>//; lra. Qed.

Lemma minr10 {R : realType} (x : R) : (minr x 1 == 0) = (x == 0).
Proof. rewrite /minr; case: ifP=>//; lra. Qed.

Lemma prod1 {R : realFieldType} (e1 e2 : R) :
  0 <= e1 <= 1 -> 0 <= e2 <= 1 -> (e1 * e2 == 1) = ((e1 == 1) && (e2 == 1)).
Proof.
nra.
Qed.

Lemma prod01 {R : realFieldType} [s : seq R] :
  (forall e, e \in s -> 0 <= e <= 1) -> (0 <= \prod_(j <- s) j <= 1).
Proof.
elim: s => [_|e0].
- by rewrite big_nil ler01 lexx.
- move=> s IH es01.
  rewrite big_cons.
  have h0 : (0 <= \prod_(j <- s) j <= 1)%R.
    by apply: IH => e es; apply: es01; rewrite in_cons es orbT.
  have : (0 <= e0 <= 1)%R.
    by apply: es01; rewrite in_cons eq_refl.
  nra.
Qed.

Lemma psumr_eqsize {R : realType} :
  forall (I : eqType) (r : seq I) [F : I -> R],
  (forall i : I, F i <= 1)%R ->
  (\sum_(i <- r) F i = (size r)%:R) <-> forall i, i \in r -> (F i = 1).
Proof.
move => I r F h1.
elim: r.
- by rewrite big_nil.
- move => a s IH.
  split.
  + have : (\sum_(i <- s) F i <= (size s)%:R)%R.
      by apply: sum_01 => i _.
    rewrite /= le_eqVlt big_cons => /orP[/eqP h|h].
      rewrite -natr1 addrC h.
      move/addrI => h' i.
      rewrite in_cons => /orP[/eqP ->|ils]; first by rewrite h'.
      exact: IH.1.
    have: F a + \sum_(j <- s) F j < (size (a :: s))%:R.
      rewrite /= -nat1r.
      move: h.
      set x := \sum_(i <- s) F i.
      set y := size s.
      have := h1 a.
      lra.
    set x := F a + \sum_(j <- s) F j.
    set y := ((size (a :: s)))%:R.
    lra.
  + move=> h.
    rewrite /= -nat1r big_cons h.
      by apply: congr1; apply: IH.2 => i ias; apply: h; rewrite in_cons ias orbT.
    by rewrite in_cons eq_refl//.
Qed.

Lemma bigmin_eqP {R : realType}:
  forall (x : R) [I : eqType] (s : seq I) (F : I -> R),
  reflect (forall i : I, i \in s -> (x <= F i)) (\big[minr/x]_(i <- s) F i == x).
Proof.
move => x I s F.
have minrl : forall (x y : R), minr x y <= x => //. (* TODO: this should exist *)
  by move => v w; rewrite /minr; case: ifPn; rewrite ?le_refl -?leNgt.
apply: (iffP eqP) => [<- i|].
- elim: s => // a s IH.
  rewrite in_cons => /orP[/eqP<-|si].
  + by rewrite big_seq big_cons mem_head minrl.
  + by rewrite big_cons minC; apply: le_trans (IH si); exact: minrl.
- elim: s => [h|i l IH h].
  + by rewrite big_nil.
  + rewrite big_cons IH ?min_r ?h ?mem_head// => a al.
    by rewrite h// in_cons al orbT.
Qed.

Lemma le_pow_01 {R : realType} (x p0 : R ):
  0 <= x <= 1 -> (0 <= (1 - x) `^ p0).
Proof.
by rewrite powR_ge0.
Qed.
(*end the move to new document*)


(* NB(rei): this lemma exists in MathComp-Analysis but maybe in a slightly
   different form depending on your version, might be removed at to some point
   but no hurry *)
Lemma gt0_ltr_powR {R : realType} (r : R) : 0 < r ->
  {in `[0, +oo[ &, {homo (@powR R) ^~ r : x y / x < y >-> x < y}}.
Proof.
move=> r0 x y; rewrite !in_itv/= !andbT !le_eqVlt => /predU1P[<-|x0].
  move=> /predU1P[<-|y0 _]; first by rewrite ltxx//.
  by rewrite powR0 ?(gt_eqF r0)// powR_gt0.
move=> /predU1P[<-|y0]; first rewrite ltNge ltW//.
by rewrite /powR !gt_eqF// ltr_expR ltr_pmul2l// ltr_ln.
Qed.

Lemma prod1_01 {R : realFieldType} :
  forall [s : seq R], (forall e, e \in s -> 0 <= e <= 1) ->
    (\prod_(j <- s) j = 1 <-> (forall e, e \in s -> e = (1:R))).
Proof.
elim.
- by rewrite big_nil.
- move=> e s IH h.
  rewrite big_cons.
  split.
  + move/eqP.
    rewrite prod1; last 2 first.
      by apply: h; rewrite in_cons eq_refl.
      by apply: prod01 => e0 e0s; apply: h; rewrite in_cons e0s orbT.
    move/andP => [/eqP e1] /eqP.
    rewrite IH; last first.
      by move=> e0 e0s; apply: h; rewrite in_cons e0s orbT.
    move=> h' e0.
    rewrite in_cons => /orP [/eqP -> //|].
    apply: h'.
  + move=> es1. 
    apply /eqP. 
    rewrite prod1; last 2 first.
    - by apply: h; rewrite in_cons eq_refl.
    - by apply: prod01 => e0 e0s; apply: h; rewrite in_cons e0s orbT.
    apply/andP; split. 
    - by apply/eqP; apply: es1; rewrite in_cons eq_refl.
    - apply/eqP; rewrite IH => e0 e0s.
        by apply es1; rewrite in_cons e0s orbT.
      by apply: h; rewrite in_cons e0s orbT.
Qed.

Lemma mineC {R : realType} : commutative (fun (x y : \bar R) => mine x y).
Proof.
rewrite /commutative => x y.
rewrite /mine.
case: ifPn; rewrite ltNge le_eqVlt.
- by rewrite negb_or => /andP[_]; case: ifPn.
- by rewrite Bool.negb_involutive => /orP[/eqP|]->//; case: ifPn.
Qed.

Lemma mineA {R : realType} : associative (fun (x y : \bar R) => mine x y).
Proof.
rewrite /associative => x y z.
rewrite /mine.
repeat case: ifPn => //; rewrite -!leNgt => a b c d; apply/eqP; rewrite eq_le.
- by rewrite b andbT le_eqVlt (lt_trans a c) orbT.
- by rewrite a andbT (ltW (lt_le_trans d c)).
- by rewrite b andbT ltW.
- by rewrite (le_trans b a) ltW.
- by rewrite b ltW.
- by rewrite d ltW.
- by rewrite c ltW.
Qed.
