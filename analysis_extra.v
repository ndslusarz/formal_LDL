From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals topology prodnormedzmodule.
From mathcomp Require Import constructive_ereal ereal normedtype ereal_normedtype landau forms.
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

Reserved Notation "'d f '/d i" (at level 10, f, i at next level,
  format "''d'  f  ''/d'  i").

Lemma sumr_lt0 {R : realDomainType} [I : eqType] [r : seq I]
    [P : pred I] [F : I -> R] :
  (forall i, i \in r -> P i -> F i <= 0) ->
  (exists i, [/\ i \in r, P i & F i < 0]) ->
  \sum_(i <- r | P i) F i < 0.
Proof.
elim: r => [h1 [x []]|]; first by rewrite in_nil.
move=> a l IH h1 [x []]; rewrite inE => /predU1P[-> Pa Fa0|].
  rewrite big_seq_cond big_cons.
  case: ifPn; rewrite mem_head Pa// -{2}(addr0 0) ltr_leD//.
  by rewrite sumr_le0// => i /andP[? Pi]; rewrite h1.
move=> xl Px Fx0; rewrite big_cons; case: ifPn => Pa.
  rewrite -{2}(addr0 0) ler_ltD ?h1 ?mem_head// IH//.
    by move=> i il Pi; rewrite h1// in_cons il orbT.
  by exists x; rewrite xl Px Fx0.
apply: IH.
  by move=> i il Pi; rewrite h1// in_cons il orbT.
by exists x; rewrite xl Px Fx0.
Qed.

Lemma sumr_gt0 {R : realDomainType} [I : eqType] [r : seq I]
    [P : pred I] [F : I -> R] :
  (forall i, i \in r -> P i -> 0 <= F i) ->
  (exists i, [/\ i \in r, P i & 0 < F i]) ->
  0 < \sum_(i <- r | P i) F i.
Proof.
elim: r => [h1 [x []]|]; first by rewrite in_nil.
move=> a l IH h1 [x []].
rewrite in_cons => /predU1P[-> Pa Fa0|].
  rewrite big_seq_cond big_cons.
  case: ifPn; rewrite mem_head Pa// -{1}(addr0 0) ltr_leD//.
  by rewrite sumr_ge0// => i /andP[? Pi]; rewrite h1.
move=> xl Px Fx0; rewrite big_cons; case: ifPn => Pa.
  rewrite -{1}(addr0 0) ler_ltD ?h1 ?mem_head// IH//.
    by move=> i il Pi; rewrite h1// in_cons il orbT.
  by exists x; rewrite xl Px Fx0.
apply: IH.
  by move=> i il Pi; rewrite h1// in_cons il orbT.
by exists x; rewrite xl Px Fx0.
Qed.

Local Open Scope ereal_scope.

(* TODO: PR*)
Lemma lteNy {R : numDomainType} (x : \bar R) : (x < -oo) = false.
Proof. by case: x. Qed.

(* TODO: PR*)
Lemma ltye {R : numDomainType} (x : \bar R) : (+oo < x) = false.
Proof. by case: x. Qed.

(* TODO: PR *)
Lemma mule_natr {R : realDomainType} (x : \bar R) (n : nat) :
  x * (n%:R)%:E = x *+ n.
Proof. by rewrite muleC mule_natl. Qed.

(* TODO: PR *)
Lemma inve_eqy {K : realDomainType} (x : \bar K) : (x^-1 == +oo) = (x == 0).
Proof.
case: x => [r| |] //=; apply/idP/idP => [|].
  by rewrite inver; case: ifPn.
by rewrite eqe => /eqP ->/=; rewrite inver//= eqxx.
Qed.

(* TODO: PR *)
Lemma inve_eqNy {K : realDomainType} (x : \bar K) : (x^-1 == -oo) = (x == -oo).
Proof.
by case: x => [r| |] //=; rewrite inver; case: ifPn.
Qed.

(*move to analysis/mathcomp*)
Lemma powRpinv {R : realType} (r : R) : (1 = 1 `^ r)%R.
Proof. by rewrite powR1. Qed.

Lemma powR_le1 {R : realType} (x r : R) :
  (r >= 0 -> 0 <= x ->  x <= 1 -> x `^ r <= 1)%R.
Proof.
move=> r0 x0 x1; rewrite (powRpinv r)//=.
by apply ge0_ler_powR; rewrite ?nnegrE ?invr_ge0//=.
Qed.

Lemma pow_le01 {R : realType} (x r : R) :
  (r > 0 -> 0 <= x <= 1 -> 0 <= x `^ r <= 1)%R.
Proof. by move=> r0 H; rewrite powR_ge0/= powR_le1//=; lra. Qed.

Lemma mine_gexy {R : realDomainType} (a b c : \bar R) :
  a <= b -> mine a c <= mine b c.
Proof.
move=> ab; rewrite /mine; case: ifPn => // ac; case: ifPn => //.
- by move/ltW : ac.
- by move=> _; rewrite (le_trans _ ab)// leNgt.
Qed.

Lemma maxe_gexy {R : realDomainType} (a b c : \bar R) :
  a <= b -> maxe a c <= maxe b c.
Proof.
move=> ab; rewrite /maxe; case: ifPn => // ac; case: ifPn => //.
- by rewrite -leNgt.
- by move=> bc; rewrite (le_trans ab)// ltW.
Qed.

(* TODO: PR *)
HB.instance Definition _ {R : realDomainType} :=
  Monoid.isLaw.Build (\bar R) +oo mine minA minye miney.

(* TODO: PR *)
Lemma big_miney {R : numDomainType} (T : eqType) (v : seq T) (f : T -> \bar R) :
  (forall x, x \in v -> f x = +oo) -> \big[mine/+oo]_(j <- v) f j = +oo.
Proof.
elim: v => [|h t ih H].
  by rewrite big_nil.
rewrite big_cons ih ?miney ?H ?mem_head// => x xt.
by rewrite H// inE xt orbT.
Qed.

(* TODO: PR *)
Lemma big_maxeNy {R : numDomainType} (T : eqType) (v : seq T) (f : T -> \bar R) :
  (forall x, x \in v -> f x = -oo) -> \big[maxe/-oo]_(j <- v) f j = -oo.
Proof.
elim: v => [|h t ih H].
  by rewrite big_nil.
rewrite big_cons ih ?maxey ?H ?mem_head// => x xt.
by rewrite H// inE xt orbT.
Qed.

(* TODO: PR *)
Lemma big_maxey {R : realDomainType} T (v : seq T) (f : T -> \bar R) :
  +oo \in map f v -> \big[maxe/-oo]_(j <- v) f j = +oo.
Proof.
elim: v => // h t ih.
by rewrite inE big_cons => /predU1P[<-|/ih ->]; rewrite ?(maxye,maxey).
Qed.

(* TODO: PR *)
Lemma big_mineNy {R : realDomainType} T (v : seq T) (f : T -> \bar R) :
  -oo \in map f v -> \big[mine/+oo]_(j <- v) f j = -oo.
Proof.
elim: v => // h t ih.
by rewrite inE big_cons => /predU1P[<-|/ih ->]; rewrite ?(minNye,mineNy).
Qed.

Local Close Scope ereal_scope.

Section mine_extra.
Local Open Scope ereal_scope.
Context {R : realDomainType}.

(*
(* TODO: PR? *)
Lemma mineC : commutative (fun x y : \bar R => mine x y).
Proof. exact: minC. Qed.

(* TODO: PR *)
Lemma mineA : associative (fun x y : \bar R => mine x y).
Proof. exact: minA. Qed.
*)

Lemma mine_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  \big[mine/+oo]_(i <- s | P i) f i = +oo <->
  forall i, i \in s -> P i -> f i = +oo.
Proof.
elim s => [|a l IH].
  by split; [move=> _ i; rewrite in_nil|move=>_; rewrite big_nil].
split.
- rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    move=> hlpoo i; rewrite inE => /predU1P[-> pa|il pi].
      by rewrite pa in npa.
    exact: IH.1 hlpoo i il pi.
  rewrite {1}/mine; case: ifPn.
    by move=>/[swap]->; rewrite lt_neqAle => /andP[]/[swap]; rewrite leye_eq => /eqP->; rewrite eqxx.
  rewrite -leNgt=>/[swap] hlpoo. rewrite hlpoo leye_eq => /eqP fapoo i.
  rewrite inE => /predU1P[-> _|il pi]; first by rewrite fapoo.
  exact: IH.1 hlpoo i il pi.
- move=> hpoo.
  rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    by apply: IH.2 => i il pi; apply: hpoo => //; rewrite inE il orbT.
  rewrite {1}/mine; case: ifPn.
    rewrite IH.2 ?hpoo ?lt_neqAle ?inE ?eqxx// => i il pi.
    by apply: hpoo=>//; rewrite inE il orbT.
  rewrite -leNgt IH.2// => i il pi.
  by apply: hpoo => //; rewrite inE il orbT.
Qed.

Lemma mine_geP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  x <= \big[mine/+oo]_(i <- s | P i) f i <-> forall i, i \in s -> P i -> x <= f i.
Proof.
elim s=>[|a l IH].
  by split; [move=> _ i; rewrite in_nil//|move=>h; rewrite big_nil leey].
split.
- rewrite big_cons; case: ifPn => [pa|npa]; last first.
    move=> hlpoo i; rewrite inE => /predU1P[-> pa|il pi].
      by rewrite pa in npa.
    exact: IH.1 hlpoo i il pi.
  rewrite {1}/mine; case: ifPn.
    move=>/[swap] le1 le2.
    move: (le_lt_trans le1 le2).
    rewrite lt_neqAle => /andP[] _.
    move/IH=> h1 i.
    rewrite inE => /predU1P[-> //|il pi].
    exact: h1.
  rewrite -leNgt=>/[swap] hlpoo h2.
  move: (le_trans hlpoo h2) => xlefa i.
  rewrite inE => /predU1P[-> //|il pi].
  exact: IH.1.
- move=> hpoo.
  rewrite big_cons; case: ifPn => [pa|npa]; last first.
    by apply: IH.2 => i il pi; apply: hpoo => //; rewrite inE il orbT.
  rewrite {1}/mine; case: ifPn => [_|].
    by rewrite hpoo// inE eqxx.
  rewrite -leNgt IH.2// => i il pi.
  by rewrite hpoo// inE il orbT.
Qed.

Lemma mine_lt (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  \big[mine/+oo]_(i <- r | P i) f i < x <->
  exists i, [/\ i \in r, P i & f i < x].
Proof.
elim: r.
  rewrite big_nil; split; first by rewrite ltNge leey.
  by move=> [i[]]; rewrite in_nil.
move=> a l IH; rewrite big_cons; case: ifPn => Pa; last first.
  split.
    by move/IH => [i[il Pi fi]]; exists i; rewrite in_cons il Pi fi orbT.
  move=> [i[]]; rewrite in_cons => /predU1P[-> Pa'|il Pi fi]; first by rewrite Pa' in Pa.
  by rewrite IH; exists i; rewrite il Pi fi.
rewrite {1}/mine.
case: ifPn => [h|].
  split; first by move=> h'; exists a; rewrite mem_head.
  move=>[i[]]; rewrite in_cons => /predU1P[-> //|il Pi fi].
  by rewrite (lt_trans h)// IH; exists i.
rewrite -leNgt => h.
split.
  by move/IH => [i [il Pi fi]]; exists i; rewrite in_cons il orbT Pi fi.
move=> [i[]]; rewrite in_cons => /predU1P[-> _ faltx|il Pi fi].
  exact: (le_lt_trans h faltx).
by rewrite IH; exists i; rewrite il Pi fi.
Qed.

Lemma mine_gt (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  x < \big[mine/+oo]_(i <- r | P i) f i ->
  forall i, i \in r -> P i -> x < f i.
Proof.
elim: r; first by move=> _ i; rewrite in_nil.
move=> a l IH.
rewrite big_cons.
case: ifPn => Pa; last first.
  move/IH => h i; rewrite in_cons => /predU1P[-> Pa'|]; first by rewrite Pa' in Pa.
  exact: h.
rewrite {1}/mine.
case: ifPn => [h1 h2 i|].
  rewrite in_cons => /predU1P[->//|il Pi].
  by rewrite IH// (lt_trans h2 h1).
rewrite -leNgt=> h1 h2 i; rewrite in_cons => /predU1P[-> _|il Pi].
  by rewrite (lt_le_trans h2 h1).
exact: IH.
Qed.

Lemma mine_eq (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  x != +oo ->
  \big[mine/+oo]_(i <- r | P i) f i = x ->
  exists i, [/\ i \in r, P i & f i = x].
Proof.
elim: r => [|a l IH xltpoo].
  by rewrite big_nil => /[swap]<-; rewrite eqxx.
rewrite big_cons; case: ifPn => Pa.
  rewrite {1}/mine; case: ifPn => [h1 h2|_].
    by exists a; rewrite mem_head Pa h2.
  move/(IH xltpoo) => [b [bl Pb fb]].
  by exists b; rewrite in_cons bl orbT.
move/(IH xltpoo) => [b [bl Pb fb]].
by exists b; rewrite in_cons bl orbT.
Qed.

End mine_extra.

Section maxe_extra.
Local Open Scope ereal_scope.
Context {R : realDomainType}.

Lemma maxe_eq (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  -oo != x ->
  \big[maxe/-oo]_(i <- r | P i) f i = x
  -> exists i, [/\ i \in r, P i & f i = x].
Proof.
elim: r => [|a l IH xltpoo].
  by rewrite big_nil => /[swap]<-; rewrite eqxx.
rewrite big_cons; case: ifPn => Pa.
  rewrite {1}/maxe; case: ifPn => [h1 h2|_ fax]; last first.
    by exists a; rewrite mem_head Pa fax.
  move: (IH xltpoo h2) => [b[bl Pb fb]].
  by exists b; rewrite in_cons bl orbT.
move/(IH xltpoo) => [b[bl Pb fb]].
by exists b; rewrite in_cons bl orbT.
Qed.

Lemma maxe_lt (T : eqType) (r : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  -oo < x ->
  \big[maxe/-oo]_(i <- r | P i) f i < x <->
  forall i, i \in r -> P i -> f i < x.
Proof.
move=> ltNyx.
elim: r; first by rewrite big_nil; split.
move=> a l IH.
rewrite big_cons.
case: ifPn => Pa; last first.
  rewrite IH; split => h i.
    rewrite in_cons => /predU1P[-> Pa'| il Pi].
      by rewrite Pa' in Pa.
    exact: h.
  move=> il Pi; apply: h => //.
  by rewrite in_cons il orbT.
rewrite {1}/maxe; case: ifPn=> [h1|].
  split => h2.
    move=> i; rewrite in_cons => /predU1P[-> _|il Pi].
      exact: (lt_trans h1 h2).
    exact: IH.1.
  by apply: IH.2 => i il Pi; rewrite h2// in_cons il orbT.
rewrite -leNgt=> h1; split => h2.
  move=> i; rewrite in_cons => /predU1P[-> _//|il Pi].
  by rewrite IH.1// (le_lt_trans h1 h2).
by rewrite h2// mem_head.
Qed.

Lemma maxe_leP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  \big[maxe/-oo]_(i <- s | P i) f i <= x <-> forall i, i \in s -> P i -> f i <= x.
Proof.
elim s=>[|a l IH].
  by split; [move=> _ i; rewrite in_nil//|move=>h; rewrite big_nil leNye].
split.
- rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    move=> hlpoo i; rewrite inE => /predU1P[-> pa|il pi].
      by rewrite pa in npa.
    exact: IH.1 hlpoo i il pi.
  rewrite {1}/maxe; case: ifPn.
    move=>/[swap] le1 le2 i.
    rewrite in_cons=> /predU1P[-> Pa |il Pi].
      exact: (le_trans (ltW le2) le1).
    exact: IH.1.
  rewrite -leNgt=>/[swap] fax h2.
  move=> i. rewrite in_cons => /predU1P[-> _//|il pi].
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
  forall x, x \in r -> P x -> f x <= \big[maxe/-oo]_(i <- r | P i) f i.
Proof.
elim: r; first by move=> x; rewrite in_nil.
move=> a l ih x.
rewrite in_cons => /predU1P[-> pa| xl px].
  rewrite big_cons pa {1}/maxe.
  case: ifPn => // h.
  exact: ltW.
rewrite big_cons; case: ifPn => pa.
  rewrite {1}/maxe; case: ifPn => // [h|].
    by rewrite ih.
  rewrite -leNgt => h.
  apply: (le_trans _ h).
  by rewrite ih.
exact: ih.
Qed.

Lemma maxe_gt (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  x < \big[maxe/-oo]_(i <- r | P i) f i <->
  exists i, [/\ i \in r, P i & x < f i].
Proof.
elim: r.
  rewrite big_nil; split; first by rewrite ltNge leNye.
  by move=> [i[]]; rewrite in_nil.
move=> a l IH; rewrite big_cons; case: ifPn => Pa; last first.
  split.
    by move/IH => [i[il Pi fi]]; exists i; rewrite in_cons il Pi fi orbT.
  move=> [i[]]; rewrite in_cons => /predU1P[-> Pa'|il Pi fi]; first by rewrite Pa' in Pa.
  by rewrite IH; exists i; rewrite il Pi fi.
rewrite {1}/maxe; case: ifPn => [h|].
  split; first by move/IH => [i [il Pi xfi]]; exists i; rewrite in_cons il orbT Pi xfi.
  move=>[i[]]; rewrite in_cons => /predU1P[-> _ xfa//|il Pi fi].
    exact: (lt_trans xfa h).
  by rewrite IH; exists i.
rewrite -leNgt => h.
split.
  by move=> xfa; exists a; rewrite mem_head Pa xfa.
move=> [i[]]; rewrite in_cons => /predU1P[-> _ //|il Pi fi].
apply: (lt_le_trans fi).
apply: (le_trans _ h).
exact: maxe_ge.
Qed.

Lemma maxe_ge' (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  x != -oo ->
  x <= \big[maxe/-oo]_(i <- r | P i) f i <->
  exists i, [/\ i \in r, P i & x <= f i].
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
    move=> [i [] ]. rewrite in_cons => /predU1P[-> _ xfa|il pi xfi ].
      by rewrite ltW// (le_lt_trans xfa h).
    by rewrite ih; exists i; rewrite il pi xfi.
  rewrite -leNgt => h.
  split.
    by move=> xfa; exists a; rewrite mem_head pa xfa.
  move=> [i].
  rewrite in_cons => [[/predU1P[-> | ] il pi]]  // xfi.
  rewrite (le_trans _ h)// ih.
  by exists i; rewrite il pi xfi.
split.
  rewrite ih => -[i [il pi xfi ] ].
  by exists i; rewrite in_cons il orbT pi xfi.
move=> [ i [] ].
rewrite in_cons => /predU1P[-> pa' | il pi xfi].
  by rewrite pa' in pa.
by rewrite ih; exists i; rewrite il pi xfi.
Qed.

Lemma maxe_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  \big[maxe/-oo]_(i <- s | P i) f i = -oo <->
  forall i, i \in s -> P i -> f i = -oo.
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
    rewrite in_cons => /predU1P[-> //| ].
    exact: h.
  by apply; rewrite ?mem_head ?pa.
split.
  move/ih => h i.
  rewrite in_cons => /predU1P[-> pa'| ].
    by rewrite pa' in pa.
  exact: h.
move=> h.
rewrite ih => i il pi.
by rewrite h// in_cons il orbT.
Qed.

End maxe_extra.

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
- by rewrite  mulr1.
- by rewrite  mulrN1.
- rewrite mulNyr/=; have [x0|x0|->] := ltgtP y 0.
  + by rewrite ltr0_sg//= EFinN mulN1e/= mulrN1 opprK.
  + by rewrite gtr0_sg//= !mul1e mulN1r.
  + by rewrite sgr0 mul0e mulr0/= sgr0.
- by rewrite  mulN1r.
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
- by move => _; rewrite ltNge//=.
Qed.

Lemma sge1_gt0 {R : realDomainType} (x : \bar R) : sge x = 1 -> (0 < x)%E.
Proof.
move: x => [x| |]//=.
- by rewrite lte_fin => /eqP; rewrite sgr_cp0.
- by move => _; rewrite ltNge//=.
- by move=> /eqP; rewrite eq_sym -subr_eq0 opprK -(natrD _ 1%N 1%N) pnatr_eq0.
Qed.

Lemma prode_seq_eq0 {R : numDomainType} {I : Type} (r : seq I) (P : pred I)
    (F : I -> \bar R) :
  (\big[*%E/1]_(i <- r | P i) F i == 0)%E = has (fun i => P i && (F i == 0)) r.
Proof.
elim: r => /= [|h t ih]; first by rewrite big_nil onee_eq0.
rewrite big_cons; case: ifPn => Ph /=; last by rewrite ih.
by rewrite mule_eq0 ih.
Qed.

Section ereal_extra.
Local Open Scope ereal_scope.
Context (R : realDomainType).

Lemma nadde_lt0 (x y : \bar R) :
  x <= 0 -> y <= 0 -> x + y < 0 -> (x < 0) || (y < 0).
Proof.
move: x y => [x| |] [y| |]//; rewrite ?lee_fin ?lte_fin.
- move=> x0 y0; rewrite !ltNge -negb_and; apply: contra.
  by move=> /andP[x0' y0']; rewrite addr_ge0.
- by move=> x0 _ _; rewrite ltNyr orbT.
- by move=> _ y0 _; rewrite ltNyr.
- by move=> _ _ _; rewrite ltNy0.
Qed.

Lemma prodeN1 (T : eqType) (l : seq T) (f : T -> \bar R) :
  (forall e, e \in l -> f e < 0) ->
  sge (\big[*%E/1%E]_(e <- l) f e) = ((- 1) ^+ (size l))%R.
Proof.
elim: l => [|h t ih H]; first by rewrite big_nil/= expr0 sgr1.
rewrite big_cons sgeM ih/=; last first.
  by move=> e et; rewrite H// inE et orbT.
by rewrite exprS lte0_sg// H// mem_head.
Qed.

Lemma psume_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> \bar R) :
    (forall i, P i -> 0 <= F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Proof.
elim: r => [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
case: ifPn => pa /=; last exact: ihr.
have [Fa0|Fa0/=] := eqVneq (F a) 0; first by rewrite Fa0 add0r/= ihr.
by apply/negbTE; rewrite padde_eq0;
  [rewrite negb_and Fa0|exact: hr|exact: sume_ge0].
Qed.

Lemma prode_le0 (A : Type) (l : seq A) (f: A -> \bar R) :
  (forall i, f i <= 0) ->
  ((-1) ^+ (size l).+1)%:E * \big[*%E/1]_(j <- l) f j <= 0%R.
Proof.
move=> fle0.
elim: l => [|a l IH].
  by rewrite /= big_nil mule1 lee_fin expr1 lerN10.
rewrite /= big_cons exprS EFinM (muleC (f a)) -muleA mulN1e.
by rewrite -!muleN muleA mule_le0_ge0// oppe_ge0.
Qed.

Lemma sume_gt0 (I : eqType) (r : seq I) (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> 0 <= F i) ->
  (exists i, [/\ i \in r, P i & 0 < F i]) ->
  0 < \sum_(i <- r | P i) F i.
Proof.
elim: r; first by move=> _ [x []]; rewrite in_nil.
move=> a l IH h [x []].
rewrite in_cons big_cons => /predU1P[ -> Pa Fa_gt0|].
  by rewrite Pa -{1}(adde0 0) lte_leD// sume_ge0.
move=> xl Px Fx_gt0.
case: ifPn => Pa.
  rewrite -{1}(adde0 0) lee_ltD// ?h//.
all: by apply: IH => //; exists x.
Qed.

Lemma sume_lt0 (I : eqType) (r : seq I) (P : pred I) (F : I -> \bar R) :
  (forall i, P i -> F i <= 0) ->
  (exists i, [/\ i \in r, P i & F i < 0]) ->
  \sum_(i <- r | P i) F i < 0.
Proof.
elim: r; first by move=> _ [x []]; rewrite in_nil.
move=> a l IH .
have [->//|] := eqVneq (\sum_(i <- (a :: l) | P i) F i) -oo;
first by move => _; rewrite ltNge//=.
rewrite !big_cons.
case: ifPn => Pa sumnoo Fi_le0 [x []].
  move: sumnoo; rewrite adde_eq_ninfty negb_or => /andP[Fanoo sumnoo].
  rewrite in_cons => /predU1P[-> _ Fa0|xl Px Fxlt0].
    rewrite -{2}(adde0 0) lte_leD ?Fa0 ?fin_numElt ?sume_le0//.
    rewrite ltNye sumnoo/= (le_lt_trans (sume_le0 _ _)) ?ltNge//=.
  rewrite -{2}(adde0 0) lee_ltD ?Fi_le0 ?IH//.
    by rewrite fin_numElt ltNye Fanoo (le_lt_trans (Fi_le0 _ _)) ?ltNge//=.
  by exists x; rewrite xl Px Fxlt0.
rewrite in_cons => /predU1P[-> Pa'//|xl Px Fxlt0]; first by rewrite Pa' in Pa.
rewrite IH//.
by exists x; rewrite xl Px Fxlt0.
Qed.

Lemma oppeey (x : \bar R) : ((- x == +oo) = (x == -oo)).
Proof. by case: x. Qed.

End ereal_extra.

Lemma adde_eq_pinfty {R : numDomainType} (x y : \bar R) :
  ((x + y == +oo) = ((x == +oo) && (y != -oo)) || ((y == +oo) && (x != -oo)))%E.
Proof. by move: x y => [?| |] [?| |]. Qed.

Lemma expeR_lty {R : realType} (x : \bar R) : (x < +oo -> expeR x < +oo)%E.
Proof. by case: x => //=x; rewrite !ltry. Qed.

Definition expR_cvg0 {R : realType} K :
  expR (K * t) @[t --> nbhs 0^'+] --> (1:R)%R.
Proof.
rewrite -expR0; apply: continuous_cvg; first exact: continuous_expR.
rewrite -[X in _ --> X](mulr0 K).
apply: cvgM; first exact: cvg_cst.
exact/cvg_at_right_filter/cvg_id.
Qed.

Section derive.
Context {R : realFieldType}.

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
