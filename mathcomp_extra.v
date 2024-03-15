Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.

(**md**************************************************************************)
(* # Additions to MathComp                                                    *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory Num.Def Num.Theory GRing.Theory.

Local Open Scope ring_scope.

Reserved Notation "u '``_' i" (at level 3, i at level 2,
  left associativity, format "u '``_' i").
Reserved Notation "u *d w" (at level 40).

Lemma In_in (I : eqType) (s : seq I) e : e \in s <-> List.In e s.
Proof.
elim: s => //= h t ih; split=> [|[<-|/ih] ].
- by rewrite inE => /predU1P[->|/ih]; [left|right].
- by rewrite mem_head.
- by rewrite inE => ->; rewrite orbT.
Qed.

Lemma card_ordS (n : nat) (i : 'I_n.+1) : #|(fun j : 'I_n.+1 => j != i)| = n.
Proof.
have := card_ord n.+1.
rewrite (cardD1 i) inE add1n => -[] hn.
rewrite -[RHS]hn.
apply: eq_card => x.
rewrite inE; apply/idP/idP.
  by rewrite inE andbT.
by move=> /andP[xi _].
Qed.

Lemma naddr_lt0 {R : realDomainType} (x y : R) :
  x <= 0 -> y <= 0 -> x + y < 0 -> (x < 0) || (y < 0).
Proof.
move=> x0 y0; rewrite !ltNge -negb_and; apply: contra.
by move=> /andP[x0' y0']; rewrite addr_ge0.
Qed.

Definition row_of_seq {R : numDomainType} (s : seq R) : 'rV[R]_(size s) :=
  (\row_(i < size s) tnth (in_tuple s) i).

(* TODO(rei): this notation breaks the display of ball predicates *)
Notation "u '``_' i" := (u 0%R i) : ring_scope.

Definition dotmul {R : ringType} n (u v : 'rV[R]_n) : R := (u *m v^T)``_0.
Notation "u *d w" := (dotmul u w).

Section alias_for_bigops.
Context {R : numDomainType}.
Implicit Types s : seq R.

Definition sumR s := \sum_(i <- s) i.
Definition prodR s := \prod_(i <- s) i.
Definition minR s : R := \big[minr/1]_(i <- s) i.
Definition maxR s : R := \big[maxr/0]_(i <- s) i.

End alias_for_bigops.

Lemma sum_01 {R : numDomainType} (I : eqType) (s : seq I) (f : I -> R) :
  (forall i, i \in s -> f i <= 1) -> \sum_(i <- s) f i <= (size s)%:R.
Proof.
move=> s01; rewrite -sum1_size natr_sum big_seq [leRHS]big_seq.
by rewrite ler_sum// => r /s01 /andP[].
Qed.

Lemma prodr_seq_eq0 {R : numDomainType} {I : Type} (r : seq I) (P : pred I)
    (F : I -> R) :
  (\big[*%R/1]_(i <- r | P i) F i == 0) = has (fun i => P i && (F i == 0)) r.
Proof.
elim: r => /= [|h t ih]; first by rewrite big_nil oner_eq0.
rewrite big_cons; case: ifPn => Ph /=; last by rewrite ih.
by rewrite mulf_eq0 ih.
Qed.

Lemma prodr_le0 {R : numDomainType} (A : Type) (l : seq A) (f: A -> R) :
  (forall i, f i <= 0) ->
  (((-1) ^+ (length l).+1) * \big[*%R/1]_(j <- l) f j <= 0).
Proof.
move=> fle0.
elim: l => [|a l IH].
  by rewrite /= big_nil mulr1 expr1 lerN10.
rewrite /= big_cons exprS (mulrC (f a)) -mulrA mulN1r.
by rewrite -!mulrN mulrA mulr_le0_ge0// oppr_ge0.
Qed.

Lemma prod1 {R : realDomainType} (e1 e2 : R) :
  0 <= e1 <= 1 -> 0 <= e2 <= 1 -> (e1 * e2 == 1) = ((e1 == 1) && (e2 == 1)).
Proof. nra. Qed.

Lemma prod01 {R : realDomainType} [s : seq R] :
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

Lemma psumr_eqsize {R : realDomainType} :
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
    by rewrite in_cons eq_refl.
Qed.

Lemma prod1_01 {R : realDomainType} :
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

Lemma prodrN1 {R : realDomainType} (T : eqType) (l : seq T) (f : T -> R) :
  (forall e, e \in l -> f e < 0)%R ->
  sgr (\prod_(e <- l) f e) = (- 1) ^+ (size l).
Proof.
elim: l => [|a l ih h]; first by rewrite big_nil/= expr0 sgr1.
rewrite big_cons sgrM ltr0_sg ?h ?mem_head//= exprS ih// => e el.
by rewrite h// in_cons el orbT.
Qed.

(* TODO(rei): not used *)
Lemma bigsum_0x {R : realDomainType} (T : eqType) f :
  forall [s : seq T], (forall e, e \in s -> 0 <= f e) ->
    (\sum_(j <- s) f j == 0 <-> (forall e, e \in s -> f e = (0:R))).
Proof.
elim.
- by rewrite big_nil.
- move => a l0 h1 h2 .
  rewrite big_cons big_seq.
  rewrite paddr_eq0; last 2 first.
  + by apply: h2; rewrite mem_head.
  + by apply: sumr_ge0 => i il0; apply: h2; rewrite in_cons il0 orbT.
  split.
  + move/andP => [/eqP a0].
    rewrite -big_seq h1 => h3 e.
      by rewrite in_cons => /orP[/eqP->//|el0]; exact: h3.
    by apply: h2; rewrite in_cons e orbT.
  + move=> h3.
    apply/andP; split.
      by apply/eqP; apply: h3; rewrite mem_head.
    rewrite psumr_eq0.
      by apply/allP => x xl0; apply/implyP => _; apply/eqP; apply: h3; rewrite in_cons xl0 orbT.
    by move=> i xl0; apply: h2; rewrite in_cons xl0 orbT.
Qed.

Lemma maxr0_le {R : realDomainType} (x : R) : - maxr x 0 = 0 -> x <= 0.
Proof.
rewrite /maxr. case: ifP.
- by lra.
- by move => h; lra.
Qed.

Lemma maxr01 {R : realDomainType} (x : R) : (maxr x 0 == 1) = (x == 1).
Proof. by rewrite/maxr; case: ifP=>//; lra. Qed.

Lemma minr10 {R : realDomainType} (x : R) : (minr x 1 == 0) = (x == 0).
Proof. by rewrite /minr; case: ifP=>//; lra. Qed.

Lemma minrxx {R : realDomainType} (x : R) : minr x x = x.
Proof. by rewrite /minr; case: ifPn; lra. Qed.

Lemma maxrxx {R : realDomainType} (x : R) : maxr x x = x.
Proof. by rewrite /maxr; case: ifPn; lra. Qed.

(* TODO(Nat): need new name *)
Lemma minrxxx {R : realDomainType} (x : R) : minr x (minr x x) = minr x x.
Proof. by rewrite !minrxx. Qed.

Lemma minrxyx {R : realDomainType} (x y : R) : minr x (minr y x) = minr x y.
Proof.
rewrite /minr.
by case: ifPn; case: ifPn; case: ifPn; lra.
Qed.

Lemma maxrxxx {R : realDomainType} (x : R) : maxr x (maxr x x) = maxr x x.
Proof. by rewrite !maxrxx. Qed.

Lemma maxrxyx {R : realDomainType} (x y : R) : maxr x (maxr y x) = maxr y x.
Proof. by rewrite /maxr; case: ifPn; case: ifPn; lra. Qed.

(* TODO(rei): should be on an ordered type *)
Lemma bigmin_eqP {R : realDomainType} (x : R) [I : eqType] (s : seq I) (F : I -> R) :
  reflect (forall i : I, i \in s -> (x <= F i)) (\big[minr/x]_(i <- s) F i == x).
Proof.
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

(* NB: not used *)
(* TODO(ab): not needed, but maybe worth having instead of bigmax_le? *)
(* TODO(rei): should be on an ordered type *)
Lemma bigmax_le' (R : realDomainType) :
  forall [I : eqType] (r : seq I) (f : I -> R) (P : pred I) (x0 x : R),
    reflect (x0 <= x /\ forall i, i \in r -> P i -> f i <= x)
      (\big[Order.max/x0]_(i <- r | P i) f i <= x).
Proof.
move=> I r f P x0.
elim: r => [x|]; first by rewrite big_nil; apply: (iffP idP);move=>//[->//].
move=> a l0 IH x.
apply: (iffP idP).
- rewrite big_cons {1}/maxr.
  case: ifPn => Pa.
  + case: ifPn => [fabig h|].
    * have /IH[-> h'] := h; split=>//i.
      rewrite in_cons => /orP[/eqP -> _|il0 Pi].
        by apply: le_trans (ltW fabig) h.
      exact: h'.
    rewrite -leNgt => fabig fax.
    have /IH[x0fa h] := fabig.
    split; first apply: (le_trans x0fa fax).
    move=> i.
    rewrite in_cons => /orP[/eqP ->//|il0 Pi].
    apply: le_trans.
    apply: h => //.
    apply: fax.
  + move=> /IH[-> h]; split=>// i.
    rewrite in_cons => /orP[/eqP ->|]; first by move: Pa=> /[swap]->.
    exact: h.
- move=>[x0x h].
  have h' : forall i, i \in l0 -> P i -> f i <= x.
    by move=> i il0 Pi; rewrite h ?in_cons ?il0 ?orbT.
  have /IH h'' := conj x0x h'.
  rewrite big_cons {1}/maxr.
  case: ifPn => Pa//.
  case: ifPn => //_.
  apply: h => //.
  exact: mem_head.
Qed.
