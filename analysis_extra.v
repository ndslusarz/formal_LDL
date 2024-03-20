From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals signed topology prodnormedzmodule.
From mathcomp Require Import constructive_ereal ereal normedtype landau forms.
From mathcomp Require Import derive sequences exp realfun.
From mathcomp Require Import lra.

(**md**************************************************************************)
(* # Additions to MathComp-Analysis                                           *)
(*                                                                            *)
(* - sinh == hyperbolic sine                                                  *)
(* - cosh == hyperbolic cosine                                                *)
(* - tanh == hyperbolic tangent                                               *)
(* - cauchy_MVT == Cauchy's mean value theorem                                *)
(* - lhopital_right == L'Hopital rule (limit taken on the right)              *)
(* - lhopital_left == L'Hopital rule (limit taken on the left)                *)
(* - err_vec i with i : 'I_n.+1 ==                                            *)
(*   a vector $\delta_i$ with $1$ at index $i$ and $0$ elsewhere              *)
(* - ('d f '/d i) a with f : rV[R]_n.+1 -> R ==                               *)
(*   $\lim_{h\to 0, h\neq 0} \frac{f(a + h\delta_i) - f(a)}{h}$               *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Notation "'nondecreasing_fun' f" := ({homo f : n m / (n <= m)%O >-> (n <= m)%O})
  (at level 10).
Notation "'nonincreasing_fun' f" := ({homo f : n m / (n <= m)%O >-> (n >= m)%O})
  (at level 10).
Notation "'increasing_fun' f" := ({mono f : n m / (n <= m)%O >-> (n <= m)%O})
  (at level 10).
Notation "'decreasing_fun' f" := ({mono f : n m / (n <= m)%O >-> (n >= m)%O})
  (at level 10).

Reserved Notation "'d f '/d i" (at level 10, f, i at next level,
  format "''d'  f  ''/d'  i").

Lemma sumr_lt0 {R : realDomainType} [I : eqType] [r : seq I]
    [P : pred I] [F : I -> R] :
  (forall i : I, i \in r -> P i -> (F i <= 0%R)) ->
  (exists i : I, i \in r /\ P i /\ (F i < 0%R)) ->
  ((\sum_(i <- r | P i) F i)%R < 0%R).
Proof.
elim: r => [h1 [x []]|]; first by rewrite in_nil.
move=> a l IH h1 [x[]].
rewrite in_cons => /orP[/eqP ->[Pa Fa0]|].
  rewrite big_seq_cond big_cons.
  case: ifPn; rewrite mem_head Pa// -{2}(addr0 0) ltr_leD//.
  by rewrite sumr_le0// => i /andP[? Pi]; rewrite h1.
move=> xl [Px Fx0].
rewrite big_cons.
case: ifPn => Pa.
  rewrite -{2}(addr0 0) ler_ltD ?h1 ?mem_head// IH//.
    by move=> i il Pi; rewrite h1// in_cons il orbT.
  by exists x; rewrite xl Px Fx0.
apply: IH.
  by move=> i il Pi; rewrite h1// in_cons il orbT.
by exists x; rewrite xl Px Fx0.
Qed.

Lemma sumr_gt0 {R : realDomainType} [I : eqType] [r : seq I]
    [P : pred I] [F : I -> R] :
  (forall i : I, i \in r -> P i -> (0 <= F i)) ->
  (exists i : I, i \in r /\ P i /\ (0 < F i)) ->
  (0 < \sum_(i <- r | P i) F i).
Proof.
elim: r => [h1 [x []]|]; first by rewrite in_nil.
move=> a l IH h1 [x[]].
rewrite in_cons => /orP[/eqP ->[Pa Fa0]|].
  rewrite big_seq_cond big_cons.
  case: ifPn; rewrite mem_head Pa// -{1}(addr0 0) ltr_leD//.
  by rewrite sumr_ge0// => i /andP[? Pi]; rewrite h1.
move=> xl [Px Fx0].
rewrite big_cons.
case: ifPn => Pa.
  rewrite -{1}(addr0 0) ler_ltD ?h1 ?mem_head// IH//.
    by move=> i il Pi; rewrite h1// in_cons il orbT.
  by exists x; rewrite xl Px Fx0.
apply: IH.
  by move=> i il Pi; rewrite h1// in_cons il orbT.
by exists x; rewrite xl Px Fx0.
Qed.

Lemma le_pow_01 {R : realType} (x p0 : R ):
  0 <= x <= 1 -> (0 <= (1 - x) `^ p0).
Proof.
by rewrite powR_ge0.
Qed.

(* NB(rei): this lemma exists in MathComp-Analysis but maybe in a slightly
   different form depending on your version, might be removed at to some point
   but no hurry *)
Lemma gt0_ltr_powR {R : realType} (r : R) : 0 < r ->
  {in `[0, +oo[ &, {homo (@powR R) ^~ r : x y / x < y >-> x < y}}.
Proof.
move=> r0 x y; rewrite !inE/= !in_itv/= !andbT !le_eqVlt => /predU1P[<-|x0].
  move=> /predU1P[<-|y0 _]; first by rewrite ltxx//.
  by rewrite powR0 ?(gt_eqF r0)// powR_gt0.
move=> /predU1P[<-|y0]; first rewrite ltNge ltW//.
by rewrite /powR !gt_eqF// ltr_expR ltr_pM2l// ltr_ln.
Qed.

Definition sumE {R : numDomainType} (Es : seq \bar R) : \bar R := \sum_(i <- Es) i.
Definition prodE {R : numDomainType} (Es : seq \bar R) : \bar R := \big[*%E/1%E]_(i <- Es) i.
(* NB: this was used in the previous version of STL
Definition minE (Es : seq \bar R) : \bar R := \big[mine/+oo%E]_(i <- Es) i.
*)

Lemma mineC {R : realFieldType} : commutative (fun (x y : \bar R) => mine x y).
Proof.
rewrite /commutative => x y.
rewrite /mine.
case: ifPn; rewrite ltNge le_eqVlt.
- by rewrite negb_or => /andP[_]; case: ifPn.
- by rewrite Bool.negb_involutive => /orP[/eqP|]->//; case: ifPn.
Qed.

Lemma mineA {R : realFieldType} : associative (fun (x y : \bar R) => mine x y).
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

Lemma maxe_eq (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  (-oo != x)%E ->
  (\big[maxe/-oo]_(i <- r | P i) f i = x)%E
  -> exists i, i \in r /\ P i /\ (f i = x)%E.
Proof.
elim: r.
  by rewrite big_nil => /[swap]<-; rewrite eq_refl.
move=> a l IH xltpoo.
rewrite big_cons.
case: ifPn => Pa.
  rewrite {1}/maxe.
  case: ifPn => [h1 h2|_ fax]; last first.
    by exists a; rewrite mem_head Pa fax.
  move: (IH xltpoo h2) => [b[bl [Pb fb]]].
  by exists b; rewrite in_cons bl orbT.
move/(IH xltpoo) => [b[bl [Pb fb]]].
by exists b; rewrite in_cons bl orbT.
Qed.

Lemma maxe_lt (T : eqType) (r : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  (-oo < x)%E ->
  (\big[maxe/-oo]_(i <- r | P i) f i < x <-> forall i, i \in r -> P i -> f i < x)%E.
Proof.
move=> ltNyx.
elim: r; first by rewrite big_nil; split.
move=> a l IH.
rewrite big_cons.
case: ifPn => Pa; last first.
  rewrite IH; split => h i.
    rewrite in_cons => /orP[/eqP -> Pa'| il Pi].
      by rewrite Pa' in Pa.
    exact: h.
  move=> il Pi.
  apply: h => //.
  by rewrite in_cons il orbT.
rewrite {1}/maxe.
case: ifPn=> [h1|].
  split => h2.
    move=> i; rewrite in_cons => /orP[/eqP-> _|il Pi].
      exact: (lt_trans h1 h2).
    exact: IH.1.
  by apply: IH.2 => i il Pi; rewrite h2// in_cons il orbT.
rewrite -leNgt=> h1; split => h2.
  move=> i; rewrite in_cons => /orP[/eqP->_//|il Pi].
  by rewrite IH.1// (le_lt_trans h1 h2).
by rewrite h2// mem_head.
Qed.

Lemma maxe_leP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  (\big[maxe/-oo]_(i <- s | P i) f i <= x <-> forall i, i \in s -> P i -> f i <= x)%E.
Proof.
elim s=>[|a l IH].
  by split; [move=> _ i; rewrite in_nil//|move=>h; rewrite big_nil leNye].
split.
- rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    move=> hlpoo i; rewrite inE => /orP[/eqP -> pa|il pi].
      by rewrite pa in npa.
    exact: IH.1 hlpoo i il pi.
  rewrite {1}/maxe; case: ifPn.
    move=>/[swap] le1 le2 i.
    rewrite in_cons=> /orP[/eqP -> Pa |il Pi].
      exact: (le_trans (ltW le2) le1).
    exact: IH.1.
  rewrite -leNgt=>/[swap] fax h2.
  move=> i. rewrite in_cons => /orP[/eqP -> _//|il pi].
  rewrite IH.1//.
  exact: (le_trans h2 fax).
- move=> filtx.
  rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    by apply: IH.2 => i il pi; apply: filtx => //; rewrite inE il orbT.
  rewrite {1}/maxe; case: ifPn => [_|].
  by apply: IH.2=> i il pi; rewrite filtx// in_cons il orbT.
rewrite -leNgt => ?.
by rewrite filtx// mem_head.
Qed.

Lemma maxe_ge (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) :
  forall x, x \in r -> P x -> (f x <= \big[maxe/-oo]_(i <- r | P i) f i)%E.
Proof.
elim: r; first by move=> x; rewrite in_nil.
move=> a l ih x.
rewrite in_cons => /orP[/eqP -> pa| xl px].
  rewrite big_cons pa {1}/maxe.
  case: ifPn => // h.
  exact: ltW.
rewrite big_cons.
case: ifPn => pa.
  rewrite {1}/maxe.
  case: ifPn => // [h|].
    rewrite ih//.
  rewrite -leNgt => h.
  apply: (le_trans _ h).
  rewrite ih//.
exact: ih.
Qed.

Lemma maxe_gt (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  (x < \big[maxe/-oo]_(i <- r | P i) f i)%E
  <-> exists i, i \in r /\ P i /\ (x < f i)%E.
Proof.
elim: r.
  rewrite big_nil; split; first by rewrite ltNge leNye.
  by move=> [i[]]; rewrite in_nil.
move=> a l IH; rewrite big_cons; case: ifPn => Pa; last first.
  split.
    by move/IH => [i[il[Pi fi]]]; exists i; rewrite in_cons il Pi fi orbT.
  move=> [i[]]; rewrite in_cons => /orP[/eqP->[Pa']|il[Pi fi]]; first by rewrite Pa' in Pa.
  by rewrite IH; exists i; rewrite il Pi fi.
rewrite {1}/maxe.
case: ifPn => [h|].
  split; first by move/IH => [i [il [Pi xfi] ] ]; exists i; rewrite in_cons il orbT Pi xfi.
  move=>[i[]]; rewrite in_cons => /orP[/eqP->[_ xfa]//|il [Pi fi]].
    exact: (lt_trans xfa h).
  by rewrite IH; exists i.
rewrite -leNgt => h.
split.
  by move=> xfa; exists a; rewrite mem_head Pa xfa.
move=> [i[]]; rewrite in_cons => /orP[/eqP->[_ //]|il [Pi fi]].
apply: (lt_le_trans fi).
apply: (le_trans _ h).
exact: maxe_ge.
Qed.

Lemma maxe_ge' (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  (x != -oo)%E ->
  (x <= \big[maxe/-oo]_(i <- r | P i) f i)%E
  <-> exists i, [/\ i \in r, P i & (x <= f i)%E].
Proof.
move=> /negPf xnoo.
elim: r.
  rewrite big_nil leeNy_eq xnoo; split => //.
  by move=> [i [] ]; rewrite in_nil.
move=> a l ih.
rewrite big_cons.
case: ifPn => pa.
  rewrite {1}/maxe.
  case: ifPn => [h|].
    split.
      move=> /ih [i [il pi xfi ] ].
      by exists i; rewrite in_cons il orbT pi xfi.
    move=> [i [] ]. rewrite in_cons=> /orP[/eqP -> _ xfa|il pi xfi ].
      by rewrite ltW// (le_lt_trans xfa h).
    by rewrite ih; exists i; rewrite il pi xfi.
  rewrite -leNgt => h.
  split.
    by move=> xfa; exists a; rewrite mem_head pa xfa.
  move=> [i].
  rewrite in_cons => [[/orP [/eqP -> | ] il pi]]  // xfi.
  rewrite (le_trans _ h)// ih.
  by exists i; rewrite il pi xfi.
split.
  rewrite ih => -[i [il pi xfi ] ].
  by exists i; rewrite in_cons il orbT pi xfi.
move=> [ i [] ].
rewrite in_cons => /orP[/eqP -> pa' | il pi xfi ].
  by rewrite pa' in pa.
by rewrite ih; exists i; rewrite il pi xfi.
Qed.

Lemma maxe_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (\big[maxe/-oo]_(i <- s | P i) f i = -oo <->
  forall i, i \in s -> P i -> f i = -oo)%E.
Proof.
elim: s; first by rewrite big_nil.
move=> a l ih.
rewrite big_cons.
case: ifPn => pa.
  rewrite {1}/maxe.
  case: ifPn => h.
    split.
      move=> h1 i.
      move: h; rewrite h1.
      by rewrite ltNge leNye.
    move=> h1.
    rewrite ih => i il pi.
    by rewrite h1// in_cons il orbT.
  split.
    move=> fanoo i.
    move: h.
    rewrite -leNgt fanoo leeNy_eq => /eqP.
    move/ih => h.
    rewrite in_cons => /orP[/eqP -> //| ].
    exact: h.
  by apply; rewrite ?mem_head ?pa.
split.
  move/ih => h i.
  rewrite in_cons => /orP[/eqP -> pa'| ].
    by rewrite pa' in pa.
  exact: h.
move=> h.
rewrite ih => i il pi.
by rewrite h// in_cons il orbT.
Qed.

End stl_helpers.

Section derive.
Context {R : realFieldType}.

Lemma derive_cst (p x : R) : 'D_1 (fun=> p) x = 0.
Proof. by rewrite -derive1E derive1_cst. Qed.

Lemma derive_id (v : R) (x : R) : 'D_v id x = v :> R.
Proof. exact: derive_val. Qed.

Lemma derivable_subr (x : R) : derivable -%R x 1.
Proof. by apply: derivableN; exact: derivable_id. Qed.

Lemma derivable_addr (p x : R) : derivable (+%R p) x 1.
Proof. by apply: derivableD; [exact: derivable_cst|exact: derivable_id]. Qed.

Lemma derive_comp (f g : R^o -> R^o) x :
  derivable f x 1 -> derivable g (f x) 1 ->
  'D_1 (g \o f) x = 'D_1 g (f x) * 'D_1 f x.
Proof.
move=> fx1 gfx1; rewrite -derive1E derive1_comp; last 2 first.
  exact: fx1.
  exact: gfx1.
by rewrite !derive1E.
Qed.

End derive.

Lemma derivable_comp {R : realType} (f g : R -> R) (x : R) :
  derivable f (g x) 1 -> derivable g x 1 -> derivable (f \o g) x 1.
Proof.
move=> fgx1 gx1.
apply: ex_derive.
apply: is_derive1_comp.
  by apply/derivableP; exact: fgx1.
exact/derivableP.
Qed.

Section partial.
Context {R : realType}.
Variables (n : nat) (f : 'rV[R]_n.+1 -> R).

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

Section hyperbolic_function.
Variable R : realType.

Definition sinh (x : R) := (expR x - expR (- x)) / 2.
Definition cosh (x : R) := (expR x + expR (- x)) / 2.
Definition tanh (x : R) := sinh x / cosh x.

End hyperbolic_function.

Section Cauchy_MVT.
Context {R : realType}.
Variables (f df g dg : R -> R) (a b c : R).
Hypothesis ab : a < b.
Hypotheses (cf : {within `[a, b], continuous f})
           (cg : {within `[a, b], continuous g}).
Hypotheses (fdf : forall x, x \in `]a, b[%R -> is_derive x 1 f (df x))
           (gdg : forall x, x \in `]a, b[%R -> is_derive x 1 g (dg x)).
Hypotheses (dg0 : forall x, x \in `]a, b[%R -> dg x != 0).

Lemma cauchy_MVT :
  exists2 c, c \in `]a, b[%R & df c / dg c = (f b - f a) / (g b - g a).
Proof.
have [r] := MVT ab gdg cg; rewrite in_itv/= => /andP[ar rb] dgg.
have gba0 : g b - g a != 0.
  by rewrite dgg mulf_neq0 ?dg0 ?in_itv/= ?ar// subr_eq0 gt_eqF.
pose h (x : R) := f x - ((f b - f a) / (g b - g a)) * g x.
have hder x : x \in `]a, b[%R -> derivable h x 1.
  move=> xab; apply: derivableB => /=.
    exact: (@ex_derive _ _ _ _ _ _ _ (fdf xab)).
  by apply: derivableM => //; exact: (@ex_derive _ _ _ _ _ _ _ (gdg xab)).
have ch : {within `[a, b], continuous h}.
  rewrite continuous_subspace_in => x xab.
  by apply: cvgB; [exact: cf|apply: cvgM; [exact: cvg_cst|exact: cg]].
have /(Rolle ab hder ch)[x xab derh] : h a = h b.
  rewrite /h; apply/eqP; rewrite subr_eq eq_sym -addrA eq_sym addrC -subr_eq.
  rewrite -mulrN -mulrDr -(addrC (g a)) -[X in _ * X]opprB mulrN -mulrA.
  by rewrite mulVf// mulr1 opprB.
pose dh (x : R) := df x - (f b - f a) / (g b - g a) * dg x.
have his_der y : y \in `]a, b[%R -> is_derive x 1 h (dh x).
  by move=> yab; apply: is_deriveB; [exact: fdf|apply: is_deriveZ; exact: gdg].
exists x => //.
have := @derive_val _ R _ _ _ _ _ (his_der _ xab).
have -> := @derive_val _ R _ _ _ _ _ derh.
move=> /eqP; rewrite eq_sym subr_eq add0r => /eqP ->.
by rewrite -mulrA divff ?mulr1//; exact: dg0.
Qed.

End Cauchy_MVT.

Section lhopital.
Context {R : realType}.
Variables (f df g dg : R -> R) (a : R) (U : set R) (Ua : nbhs a U).
Hypotheses (fdf : forall x, x \in U -> is_derive x 1 f (df x))
           (gdg : forall x, x \in U -> is_derive x 1 g (dg x)).
Hypotheses (fa0 : f a = 0) (ga0 : g a = 0)
           (cdg : \forall x \near a^', dg x != 0).

Lemma lhopital_right (l : R) :
  df x / dg x @[x --> a^'+] --> l -> f x / g x @[x --> a^'+] --> l.
Proof.
case: cdg => r/= r0 cdg'.
move: Ua; rewrite filter_of_nearI => -[D /= D0 aDU].
near a^'+ => b.
have abf x : x \in `]a, b[%R -> {within `[a, x], continuous f}.
  rewrite in_itv/= => /andP[ax xb].
  apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[ay yx].
  apply: ex_derive.
  apply: fdf.
  rewrite inE; apply: aDU => /=.
  rewrite ler0_norm? subr_le0//.
  rewrite opprD opprK addrC ltrBlDr (le_lt_trans yx)// (lt_trans xb)//.
  near: b; apply: nbhs_right_lt.
  by rewrite ltrDr.
have abg x : x \in `]a, b[%R -> {within `[a, x], continuous g}.
  rewrite in_itv/= => /andP[ax xb].
  apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[ay yx].
  apply: ex_derive.
  apply: gdg.
  rewrite inE; apply: aDU => /=.
  rewrite ler0_norm? subr_le0//.
  rewrite opprD opprK addrC ltrBlDr (le_lt_trans yx)// (lt_trans xb)//.
  near: b; apply: nbhs_right_lt.
  by rewrite ltrDr.
have fdf' y : y \in `]a, b[%R -> is_derive y 1 f (df y).
  rewrite in_itv/= => /andP[ay yb]; apply: fdf.
  rewrite inE; apply: aDU => /=.
  rewrite ltr0_norm ?subr_lt0//.
  rewrite opprD opprK addrC ltrBlDr (lt_le_trans yb)//.
  near: b; apply: nbhs_right_le.
  by rewrite ltrDr.
have gdg' y : y \in `]a, b[%R -> is_derive y 1 g (dg y).
  rewrite in_itv/= => /andP[ay yb]; apply: gdg.
  rewrite inE; apply: aDU => /=.
  rewrite ltr0_norm ?subr_lt0//.
  rewrite opprD opprK addrC ltrBlDr (lt_le_trans yb)//.
  near: b; apply: nbhs_right_le.
  by rewrite ltrDr.
have {}dg0 y : y \in `]a, b[%R -> dg y != 0.
  rewrite in_itv/= => /andP[ay yb].
  apply: (cdg' y) => /=; last by rewrite gt_eqF.
  rewrite ltr0_norm; last by rewrite subr_lt0.
  rewrite opprB ltrBlDl (lt_trans yb)//.
  near: b; apply: nbhs_right_lt.
  by rewrite ltrDl.
move=> fgal.
have L : \forall x \near a^'+,
  exists2 c, c \in `]a, x[%R & df c / dg c = f x / g x.
  near=> x.
  have /andP[ax xb] : a < x < b by exact/andP.
  have {}fdf' y : y \in `]a, x[%R -> is_derive y 1 f (df y).
    rewrite !in_itv/= => /andP[ay yx].
    by apply: fdf'; rewrite in_itv/= ay/= (lt_trans yx).
  have {}gdg' y : y \in `]a, x[%R -> is_derive y 1 g (dg y).
    rewrite !in_itv/= => /andP[ay yx].
    by apply: gdg'; rewrite in_itv/= ay/= (lt_trans yx).
  have {}dg0 y : y \in `]a, x[%R -> dg y != 0.
    rewrite in_itv/= => /andP[ya yx].
    by apply: dg0; rewrite in_itv/= ya/= (lt_trans yx).
  have {}axf : {within `[a, x], continuous f}.
    rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[ay yx].
    by apply: abf; rewrite in_itv/= xb andbT.
  have {}axg : {within `[a, x], continuous g}.
    rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[ay yx].
    by apply: abg; rewrite in_itv/= xb andbT.
  have := @cauchy_MVT _ f df g dg _ _ ax axf axg fdf' gdg' dg0.
  by rewrite fa0 ga0 2!subr0.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : fgal.
move=> /(_ _ e0)[r'/= r'0 fagl].
case: L => d /= d0 L.
near=> t.
have /= := L t.
have atd : `|a - t| < d.
  rewrite ltr0_norm; last by rewrite subr_lt0.
  rewrite opprB ltrBlDl.
  near: t; apply: nbhs_right_lt.
  by rewrite ltrDl.
have at_ : a < t by [].
move=> /(_ atd)/(_ at_)[c]; rewrite in_itv/= => /andP[ac ct <-].
apply: fagl => //=.
rewrite ltr0_norm; last by rewrite subr_lt0.
rewrite opprB ltrBlDl (lt_trans ct)//.
near: t; apply: nbhs_right_lt.
by rewrite ltrDl.
Unshelve. all: by end_near. Qed.

Lemma lhopital_left (l : R) :
  df x / dg x @[x --> a^'-] --> l -> f x / g x @[x --> a^'-] --> l.
Proof.
case: cdg => r/= r0 cdg'.
move: Ua; rewrite filter_of_nearI => -[D /= D0 aDU].
near a^'- => b.
have baf x : x \in `]b, a[%R -> {within `[x, a], continuous f}.
  rewrite in_itv/= => /andP[bx xa].
  apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[xy ya].
  apply: ex_derive.
  apply: fdf.
  rewrite inE; apply: aDU => /=.
  rewrite ger0_norm ?subr_ge0//.
  rewrite ltrBlDr -ltrBlDl (lt_le_trans _ xy)// (le_lt_trans _ bx)//.
  near: b; apply: nbhs_left_ge.
  by rewrite ltrBlDl ltrDr.
have bag x : x \in `]b, a[%R -> {within `[x, a], continuous g}.
  rewrite in_itv/= => /andP[bx xa].
  apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[xy ya].
  apply: ex_derive.
  apply: gdg.
  rewrite inE; apply: aDU => /=.
  rewrite ger0_norm ?subr_ge0//.
  rewrite ltrBlDr -ltrBlDl (lt_le_trans _ xy)// (lt_trans _ bx)//.
  near: b; apply: nbhs_left_gt.
  by rewrite ltrBlDl ltrDr.
have fdf' y : y \in `]b, a[%R -> is_derive y 1 f (df y).
  rewrite in_itv/= => /andP[by_ ya]; apply: fdf.
  rewrite inE.
  apply: aDU => /=.
  rewrite gtr0_norm ?subr_gt0//.
  rewrite ltrBlDl -ltrBlDr (le_lt_trans _ by_)//.
  near: b; apply: nbhs_left_ge.
  by rewrite ltrBlDr ltrDl.
have gdg' y : y \in `]b, a[%R -> is_derive y 1 g (dg y).
  rewrite in_itv/= => /andP[by_ ya]; apply: gdg.
  rewrite inE; apply: aDU => /=.
  rewrite gtr0_norm ?subr_gt0//.
  rewrite ltrBlDl -ltrBlDr (le_lt_trans _ by_)//.
  near: b; apply: nbhs_left_ge.
  by rewrite ltrBlDr ltrDl.
have {}dg0 y : y \in `]b, a[%R -> dg y != 0.
  rewrite in_itv/= => /andP[by_ ya].
  apply: (cdg' y) => /=; last by rewrite lt_eqF.
  rewrite gtr0_norm; last by rewrite subr_gt0.
  rewrite ltrBlDr -ltrBlDl (lt_trans _ by_)//.
  near: b; apply: nbhs_left_gt.
  by rewrite ltrBlDl ltrDr.
move=> fgal.
have L : \forall x \near a^'-,
  exists2 c, c \in `]x, a[%R & df c / dg c = f x / g x.
  near=> x.
  have /andP[bx xa] : b < x < a by exact/andP.
  have {}fdf' y : y \in `]x, a[%R -> is_derive y 1 f (df y).
    rewrite in_itv/= => /andP[xy ya].
    by apply: fdf'; rewrite in_itv/= ya andbT (lt_trans bx).
  have {}gdg' y : y \in `]x, a[%R -> is_derive y 1 g (dg y).
    rewrite in_itv/= => /andP[xy ya].
    by apply: gdg'; rewrite in_itv/= ya andbT (lt_trans _ xy).
  have {}dg0 y : y \in `]x, a[%R -> dg y != 0.
    rewrite in_itv/= => /andP[xy ya].
    by apply: dg0; rewrite in_itv/= ya andbT (lt_trans bx).
  have {}xaf : {within `[x, a], continuous f}.
    rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[xy ya].
    by apply: baf; rewrite in_itv/= bx.
  have {}xag : {within `[x, a], continuous g}.
    rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[xy ya].
    by apply: bag; rewrite in_itv/= bx.
  have := @cauchy_MVT _ f df g dg _ _ xa xaf xag fdf' gdg' dg0.
  by rewrite fa0 ga0 !sub0r divrN mulNr opprK.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : fgal.
move=> /(_ _ e0)[r'/= r'0 fagl].
case: L => d /= d0 L.
near=> t.
have /= := L t.
have atd : `|a - t| < d.
  rewrite gtr0_norm; last by rewrite subr_gt0.
  rewrite ltrBlDr -ltrBlDl.
  near: t; apply: nbhs_left_gt.
  by rewrite ltrBlDl ltrDr.
have ta : t < a by [].
move=> /(_ atd)/(_ ta)[c]; rewrite in_itv/= => /andP[tc ca <-].
apply: fagl => //=.
rewrite gtr0_norm; last by rewrite subr_gt0.
rewrite ltrBlDr -ltrBlDl (lt_trans _ tc)//.
near: t; apply: nbhs_left_gt.
by rewrite ltrBlDl ltrDr.
Unshelve. all: by end_near. Qed.

End lhopital.
