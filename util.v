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
Reserved Notation "u '``_' i" (at level 3, i at level 2,
  left associativity, format "u '``_' i").
Reserved Notation "'d f '/d i" (at level 10, f, i at next level,
  format "''d'  f  ''/d'  i").

Section alias_for_bigops.
Context {R : numDomainType}.
Implicit Types s : seq R.

Definition sumR s := \sum_(i <- s) i.
Definition prodR s := \prod_(i <- s) i.
Definition product_dl_mul (a b : R) := a + b - a * b.
Definition product_dl_prod s := \big[product_dl_mul/0]_(i <- s) i.
Definition minR s : R := \big[minr/1]_(i <- s) i.
Definition maxR s : R := \big[maxr/0]_(i <- s) i.

Definition sumE (Es : seq \bar R) : \bar R := \sum_(i <- Es) i.
Definition prodE (Es : seq \bar R) : \bar R := \big[*%E/1%E]_(i <- Es) i.
(* NB: this was used in the previous version of STL
Definition minE (Es : seq \bar R) : \bar R := \big[mine/+oo%E]_(i <- Es) i.
*)

End alias_for_bigops.

Lemma sum_01 {R : numDomainType} (I : eqType) (s : seq I) (f : I -> R) :
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
by rewrite /powR !gt_eqF// ltr_expR ltr_pM2l// ltr_ln.
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

Lemma minrxx {R : realType} :
   forall (x : R), minr x x = x.
Proof.
move => x.
rewrite /minr.
case: ifPn; lra.
Qed.


(*Nat: need new name*)
Lemma minrxxx {R : realType} :
   forall (x : R), minr x (minr x x) = minr x x.
Proof.
move => x.
by rewrite !minrxx.
Qed.

Lemma minrxyx {R : realType} :
   forall (x y : R), minr x (minr y x) = minr x y.
Proof.
move => x y.
rewrite /minr.
case: ifPn; case: ifPn; case: ifPn; lra.
Qed.

Lemma maxrxx {R : realType} :
   forall (x : R), maxr x x = x.
Proof.
move => x.
rewrite /maxr.
case: ifPn; lra.
Qed.

Lemma maxrxxx {R : realType} :
   forall (x : R), maxr x (maxr x x) = maxr x x.
Proof.
move => x.
by rewrite !maxrxx.
Qed.

Lemma maxrxyx {R : realType} :
   forall (x y : R), maxr x (maxr y x) = maxr y x.
Proof.
move => x y.
rewrite /maxr.
case: ifPn; case: ifPn; lra.
Qed.

Notation "u '``_' i" := (u 0%R i) : ring_scope.

Section partial.
Context {R : realType}.
Variables (n : nat) (f : 'rV[R^o]_n.+1 -> R^o).

Definition err_vec {R : ringType} (i : 'I_n.+1) : 'rV[R]_n.+1 :=
  \row_(j < n.+1) (i == j)%:R.

Definition partial (i : 'I_n.+1) (a : 'rV[R]_n.+1) :=
  lim (h^-1 * (f (a + h *: err_vec i) - f a) @[h --> (0:R)^']).

Lemma partialE (i : 'I_n.+1) (a : 'rV[R]_n.+1) :
  partial i a = 'D_(err_vec i) f a .
Proof.
rewrite /partial /derive/=.
by under eq_fun do rewrite (addrC a).
Qed.

End partial.
Notation "'d f '/d i" := (partial f i).

Lemma nonincreasing_at_right_cvgr {R : realType} (f : R -> R) a (b : itv_bound R) :
    (BRight a < b)%O ->
    {in Interval (BRight a) b &, nonincreasing_fun f} ->
    has_ubound (f @` [set` Interval (BRight a) b]) ->
  f x @[x --> a ^'+] --> sup (f @` [set` Interval (BRight a) b]).
Proof.
move=> ab nif ubf.
exact: realfun.nonincreasing_at_right_cvgr.
Qed.

Lemma nondecreasing_at_right_cvgr {R : realType} (f : R -> R) a (b : itv_bound R) :
    (BRight a < b)%O ->
    {in Interval (BRight a) b &, nondecreasing_fun f} ->
    has_lbound (f @` [set` Interval (BRight a) b]) ->
  f x @[x --> a ^'+] --> inf (f @` [set` Interval (BRight a) b]).
Proof.
move=> ab ndf lbf.
exact: realfun.nondecreasing_at_right_cvgr.
Qed.

Lemma monotonous_bounded_is_cvg {R : realType} (f : R -> R) x y :
  (BRight x < y)%O ->
  monotonous ([set` Interval (BRight x)(*NB(rei): was BSide b x*) y]) f ->
  has_ubound (f @` setT) -> has_lbound (f @` setT) ->
  cvg (f x @[x --> x^'+]).
Proof.
move=> xy [inc uf lf|dec uf lf].
  apply/cvg_ex; exists (inf (f @` [set` Interval (BRight x) y])).
  apply: nondecreasing_at_right_cvgr => //.
    by move=> a b axy bxy ab;rewrite inc//= inE.
  (* TODO(rei): need a lemma? *)
  case: lf => r fr; exists r => z/= [s].
  by rewrite in_itv/= => /andP[xs _] <-{z}; exact: fr.
apply/cvg_ex; exists (sup (f @` [set` Interval (BRight x)(*NB(rei): was (BSide b x)*) y])).
apply: nonincreasing_at_right_cvgr => //.
  by move=> a b axy bxy ab; rewrite dec// inE.
case: uf => r fr; exists r => z/= [s].
by rewrite in_itv/= => /andP[xs _] <-{z}; exact: fr.
Qed.

Section product_dl_mul.
Context {R : realType}.

Local Notation "x * y" := (product_dl_mul x y).

Lemma product_dl_mul_01 (x y : R) : 0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= x * y <= 1.
Proof. by rewrite /product_dl_mul; nra. Qed.

Lemma product_dl_mul_seq_01 (T : eqType) (f : T -> R) (l0 : seq T) :
  (forall i, i \in l0 -> 0 <= f i <= 1) -> (0 <= \big[product_dl_mul/0]_(i <- l0) f i <= 1).
Proof.
elim: l0.
- by rewrite big_nil lexx ler01.
- move=> a l0 IH h.
  rewrite big_cons product_dl_mul_01 ?h ?mem_head//.
  apply: IH => i il0; apply: h.
  by rewrite in_cons il0 orbT.
Qed.

Lemma product_dl_mul_inv (x y : R) :
  0 <= x <= 1 -> 0 <= y <= 1 ->
  reflect (x = 1 \/ y = 1) (x * y == 1).
Proof.
by move=> x01 y01; apply: (iffP eqP); rewrite /product_dl_mul; nra.
Qed.

Lemma product_dl_prod_inv0 (x y : R) :
  0 <= x <= 1 -> 0 <= y <= 1 ->
  reflect (x = 0 /\ y = 0) (x * y == 0).
Proof.
by move=> x01 y01; apply: (iffP eqP); rewrite /product_dl_mul; nra.
Qed.

Lemma bigsum_0x (T : eqType) f :
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

(* NB: not used *)
Lemma bigmax_le' : (* ab: not needed, but maybe worth having instead of bigmax_le? *)
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

End product_dl_mul.

Lemma prodrN1 {R : realDomainType} (T : eqType) (l : seq T) (f : T -> R) :
  (forall e, e \in l -> f e < 0)%R ->
  sgr (\prod_(e <- l) f e) = (- 1) ^+ (size l).
Proof.
elim: l => [|a l ih h]; first by rewrite big_nil/= expr0 sgr1.
rewrite big_cons sgrM ltr0_sg ?h ?mem_head//= exprS ih// => e el.
by rewrite h// in_cons el orbT.
Qed.

Definition sge {R : numDomainType} (x : \bar R) : R :=
  match x with | -oo%E => -1 | +oo%E => 1 | r%:E => sgr r end.

(* NB: this should be shorter *)
Lemma sgeM {R : realDomainType} (x y : \bar R) :
  sge (x * y) = sge x * sge y.
Proof.
move: x y => [x| |] [y| |] //=.
- by rewrite sgrM.
- rewrite mulry/=; have [x0|x0|->] := ltgtP x 0.
  + by rewrite ltr0_sg//= EFinN mulN1e/= mulN1r.
  + by rewrite gtr0_sg//= !mul1e mul1r.
  + by rewrite sgr0 mul0e mul0r/= sgr0.
- rewrite mulrNy/=; have [x0|x0|->] := ltgtP x 0.
  + by rewrite ltr0_sg//= EFinN mulN1e/= mulN1r opprK.
  + by rewrite gtr0_sg//= !mul1e mul1r.
  + by rewrite sgr0 mul0e mul0r/= sgr0.
- rewrite mulyr/=; have [x0|x0|->] := ltgtP y 0.
  + by rewrite ltr0_sg//= EFinN mulN1e/= mulrN1.
  + by rewrite gtr0_sg//= !mul1e mul1r.
  + by rewrite sgr0 mul0e mulr0/= sgr0.
- by rewrite mulyy mulr1.
- by rewrite mulyNy mulrN1.
- rewrite mulNyr/=; have [x0|x0|->] := ltgtP y 0.
  + by rewrite ltr0_sg//= EFinN mulN1e/= mulrN1 opprK.
  + by rewrite gtr0_sg//= !mul1e mulN1r.
  + by rewrite sgr0 mul0e mulr0/= sgr0.
- by rewrite mulNyy mulN1r.
- by rewrite mulrN1 opprK.
Qed.

Lemma lte0_sg {R : numDomainType} (x : \bar R) :
  (x < 0)%E -> sge x = -1.
Proof. by move: x => [x| |]//; rewrite lte_fin => /ltr0_sg. Qed.

Lemma sgeN1_lt0 {R : realDomainType} (x : \bar R) :
  sge x = -1 -> (x < 0)%E.
Proof.
move: x => [x| |]//=.
- by rewrite lte_fin => /eqP; rewrite sgr_cp0.
- by move=> /eqP; rewrite -subr_eq0 opprK -(natrD _ 1%N 1%N) pnatr_eq0.
Qed.

Lemma sge1_gt0 {R : realDomainType} (x : \bar R) : sge x = 1 -> (0 < x)%E.
Proof.
move: x => [x| |]//=.
- by rewrite lte_fin => /eqP; rewrite sgr_cp0.
- by move=> /eqP; rewrite eq_sym -subr_eq0 opprK -(natrD _ 1%N 1%N) pnatr_eq0.
Qed.

Lemma prodeN1 {R : realDomainType} (T : eqType) (l : seq T) (f : T -> \bar R) :
  (forall e, e \in l -> f e < 0)%E ->
  sge (\big[*%E/1%E]_(e <- l) f e) = (- 1) ^+ (size l).
Proof.
elim: l => [|h t ih H]; first by rewrite big_nil/= expr0 sgr1.
rewrite big_cons sgeM ih/=; last first.
  by move=> e et; rewrite H// inE et orbT.
by rewrite exprS lte0_sg// H// mem_head.
Qed.

Lemma prode_seq_eq0 {R : numDomainType} {I : Type} (r : seq I) (P : pred I)
    (F : I -> \bar R) :
  (\big[*%E/1]_(i <- r | P i) F i == 0)%E = has (fun i => P i && (F i == 0)) r.
Proof.
elim: r => /= [|h t ih]; first by rewrite big_nil onee_eq0.
rewrite big_cons; case: ifPn => Ph /=; last by rewrite ih.
by rewrite mule_eq0 ih.
Qed.

(* TODO(rei): move to analysis *)
Lemma nadde_lt0 {R : realFieldType} (x y : \bar R) :
  (x <= 0)%E -> (y <= 0)%E -> (x + y < 0)%E -> ((x < 0) || (y < 0))%E.
Proof.
move: x y => [x| |] [y| |]//; rewrite ?lee_fin ?lte_fin.
- move=> x0 y0; rewrite !ltNge -negb_and; apply: contra.
  by move=> /andP[x0' y0']; rewrite addr_ge0.
- by move=> x0 _ _; rewrite ltNyr orbT.
- by move=> _ y0 _; rewrite ltNyr.
- by move=> _ _ _; rewrite ltNy0.
Qed.

(*move to util once proven*)

Lemma psume_eq0 {R : realFieldType} (I : eqType) (r : seq I) (P : pred I) (F : I -> \bar R) :
    (forall i, P i -> 0 <= F i)%E ->
  (\sum_(i <- r | P i) (F i) == 0)%E = (all (fun i => (P i) ==> (F i == 0%E)) r).
Proof.
elim: r => [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
case: ifPn => pa /=; last exact: ihr.
have [Fa0|Fa0/=] := eqVneq (F a) 0; first by rewrite Fa0 add0r/= ihr.
by apply/negbTE; rewrite padde_eq0;
  [rewrite negb_and Fa0|exact: hr|exact: sume_ge0].
Qed.

Lemma prode_le0 {R : realFieldType} (A : Type) (l : seq A) (f: A -> \bar R) :
  (forall i, f i <= 0)%E ->
  (((-1) ^+ (length l).+1)%:E * \big[*%E/1]_(j <- l) f j <= 0%R)%E.
Proof.
move=> fle0.
elim: l => [|a l IH].
  by rewrite /= big_nil mule1 lee_fin expr1 lerN10.
rewrite /= big_cons exprS EFinM (muleC (f a)) -muleA mulN1e.
by rewrite -!muleN muleA mule_le0_ge0// oppe_ge0.
Qed.

Lemma maxr0_le {R : realFieldType} :
  forall x : R , (- maxr x 0)%:E = 0%E -> x <= 0.
Proof.
move => r.
rewrite /maxr. case: ifP.
- by lra.
- by move => h; case; lra.
Qed.

Section stl_helpers.
Context (R : realType).

Lemma mine_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (\big[mine/+oo]_(i <- s | P i) f i = +oo <-> forall i, i \in s -> P i -> f i = +oo)%E.
Proof.
elim s=>[|a l IH].
  by split; [move=> _ i; rewrite in_nil|move=>_; rewrite big_nil].
split.
- rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    move=> hlpoo i; rewrite inE => /orP[/eqP -> pa|il pi].
      by rewrite pa in npa.
    exact: IH.1 hlpoo i il pi.
  rewrite {1}/mine; case: ifPn.
    by move=>/[swap]->; rewrite lt_neqAle => /andP[]/[swap]; rewrite leye_eq => /eqP->; rewrite eq_refl.
  rewrite -leNgt=>/[swap] hlpoo. rewrite hlpoo leye_eq => /eqP fapoo i.
  rewrite inE => /orP[/eqP -> _|il pi]; first by rewrite fapoo.
  exact: IH.1 hlpoo i il pi.
- move=> hpoo.
  rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    by apply: IH.2 => i il pi; apply: hpoo => //; rewrite inE il orbT.
  rewrite {1}/mine; case: ifPn.
    rewrite IH.2 ?hpoo ?lt_neqAle ?inE ?eq_refl// => i il pi.
    by apply: hpoo=>//; rewrite inE il orbT.
  rewrite -leNgt IH.2// => i il pi.
  apply: hpoo => //.
  by rewrite inE il orbT.
Qed.

Lemma mine_geP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  (x <= \big[mine/+oo]_(i <- s | P i) f i <-> forall i, i \in s -> P i -> x <= f i)%E.
Proof.
elim s=>[|a l IH].
  by split; [move=> _ i; rewrite in_nil//|move=>h; rewrite big_nil leey].
split.
- rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    move=> hlpoo i; rewrite inE => /orP[/eqP -> pa|il pi].
      by rewrite pa in npa.
    exact: IH.1 hlpoo i il pi.
  rewrite {1}/mine; case: ifPn.
    move=>/[swap] le1 le2.
    move: (le_lt_trans le1 le2).
    rewrite lt_neqAle => /andP[] _.
    move/IH=> h1 i.
    rewrite inE => /orP[/eqP->//|il pi].
    exact: h1.
  rewrite -leNgt=>/[swap] hlpoo h2.
  move: (le_trans hlpoo h2) => xlefa i.
  rewrite inE => /orP[/eqP->//|il pi].
  exact: IH.1.
- move=> hpoo.
  rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    by apply: IH.2 => i il pi; apply: hpoo => //; rewrite inE il orbT.
  rewrite {1}/mine; case: ifPn => [_|].
    by rewrite hpoo// inE eq_refl.
  rewrite -leNgt IH.2// => i il pi.
  by rewrite hpoo// inE il orbT.
Qed.

Lemma sume_gt0 (I : eqType) (r : seq I) (P : pred I) (F : I -> \bar R) :
  (forall i : I, P i -> 0 <= F i)%E ->
  (exists i : I, i \in r /\ P i /\ 0 < F i)%E ->
  (0 < \sum_(i <- r | P i) F i)%E.
Proof.
elim: r; first by move=> _ [x[]]; rewrite in_nil.
move=> a l IH h [x []].
rewrite in_cons big_cons => /orP [/eqP ->[Pa Fa_gt0]|].
  by rewrite Pa -{1}(adde0 0) lte_le_add//sume_ge0.
move=> xl [Px Fx_gt0].
case: ifPn => Pa.
  rewrite -{1}(adde0 0) lee_lt_add// ?h//.
all: by apply: IH => //; exists x.
Qed.

Lemma sume_lt0 (I : eqType) (r : seq I) (P : pred I) (F : I -> \bar R) :
  (forall i : I, P i -> F i <= 0)%E ->
  (exists i : I, i \in r /\ P i /\ F i < 0)%E ->
  (\sum_(i <- r | P i) F i < 0)%E.
Proof.
elim: r; first by move=> _ [x[]]; rewrite in_nil.
move=> a l IH.
have [->//|] := eqVneq (\sum_(i <- (a :: l) | P i) F i) -oo%E.
rewrite !big_cons.
case: ifPn => Pa sumnoo Fi_le0 [x []].
  move: sumnoo; rewrite adde_eq_ninfty negb_or => /andP[Fanoo sumnoo].
  rewrite in_cons => /orP[/eqP->[_ Fa0]|xl [Px Fxlt0]].
    rewrite -{2}(adde0 0) lte_le_add ?Fa0 ?fin_numElt ?sume_le0//.
    by rewrite ltNye sumnoo/= (le_lt_trans (sume_le0 _ _)).
  rewrite -{2}(adde0 0) lee_lt_add ?Fi_le0 ?IH//.
    by rewrite fin_numElt ltNye Fanoo (le_lt_trans (Fi_le0 _ _)).
  by exists x; rewrite xl Px Fxlt0.
rewrite in_cons => /orP[/eqP->[Pa'//]|xl[Px Fxlt0]]; first by rewrite Pa' in Pa.
rewrite IH//.
by exists x; rewrite xl Px Fxlt0.
Qed.

Lemma mine_lt (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  (\big[mine/+oo]_(i <- r | P i) f i < x)%E
  <-> exists i, i \in r /\ P i /\ (f i < x)%E.
Proof.
elim: r.
  rewrite big_nil; split; first by rewrite ltNge leey.
  by move=> [i[]]; rewrite in_nil.
move=> a l IH; rewrite big_cons; case: ifPn => Pa; last first.
  split.
    by move/IH => [i[il[Pi fi]]]; exists i; rewrite in_cons il Pi fi orbT.
  move=> [i[]]; rewrite in_cons => /orP[/eqP->[Pa']|il[Pi fi]]; first by rewrite Pa' in Pa.
  by rewrite IH; exists i; rewrite il Pi fi.
rewrite {1}/mine.
case: ifPn => [h|].
  split; first by move=> h'; exists a; rewrite mem_head.
  move=>[i[]]; rewrite in_cons => /orP[/eqP->[]//|il [Pi fi]].
  rewrite (lt_trans h)//.
  by rewrite IH; exists i.
rewrite -leNgt => h.
split.
  by move/IH => [i[il [Pi fi]]]; exists i; rewrite in_cons il orbT Pi fi.
move=> [i[]]; rewrite in_cons => /orP[/eqP->[_ faltx]|il [Pi fi]].
  exact: (le_lt_trans h faltx).
by rewrite IH; exists i; rewrite il Pi fi.
Qed.

Lemma mine_gt (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  (x < \big[mine/+oo]_(i <- r | P i) f i)%E
  -> forall i, i \in r -> P i -> (x < f i)%E.
Proof.
elim: r; first by move=> _ i; rewrite in_nil.
move=> a l IH.
rewrite big_cons.
case: ifPn => Pa; last first.
  move/IH => h i; rewrite in_cons => /orP[/eqP->Pa'|]; first by rewrite Pa' in Pa.
  exact: h.
rewrite {1}/mine.
case: ifPn => [h1 h2|].
  move=> i. rewrite in_cons => /orP[/eqP->//|il Pi].
  by rewrite IH// (lt_trans h2 h1).
rewrite -leNgt=> h1 h2 i; rewrite in_cons => /orP[/eqP->_|il Pi].
  by rewrite (lt_le_trans h2 h1).
exact: IH.
Qed.

Lemma mine_eq (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  (x != +oo)%E ->
  (\big[mine/+oo]_(i <- r | P i) f i = x)%E
  -> exists i, i \in r /\ P i /\ (f i = x)%E.
Proof.
elim: r.
  by rewrite big_nil => /[swap]<-; rewrite eq_refl.
move=> a l IH xltpoo.
rewrite big_cons.
case: ifPn => Pa.
  rewrite {1}/mine.
  case: ifPn => [h1 h2|_].
    by exists a; rewrite mem_head Pa h2.
  move/(IH xltpoo) => [b[bl [Pb fb]]].
  by exists b; rewrite in_cons bl orbT.
move/(IH xltpoo) => [b[bl [Pb fb]]].
by exists b; rewrite in_cons bl orbT.
Qed.

Lemma expeR_lty (x : \bar R) : (x < +oo -> expeR x < +oo)%E.
Proof. by case: x => //=x; rewrite !ltry. Qed.

Lemma oppeey (x : \bar R) : ((- x == +oo) = (x == -oo))%E.
Proof. by case: x. Qed.

End stl_helpers.
