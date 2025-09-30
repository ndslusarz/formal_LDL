Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import perm.

(**md**************************************************************************)
(* # Additions to MathComp                                                    *)
(*                                                                            *)
(* TODO: to be cleaned                                                        *)
(*                                                                            *)
(* row_of_seq s == row-vector of size "size s" where s is a list              *)
(*      u ``_ i == notation to address the ith element of a row-vector        *)
(*       minR s := \big[minr/1]_(i <- s) i                                    *)
(*       maxR s := \big[maxr/1]_(i <- s) i                                    *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory Num.Def Num.Theory GRing.Theory.

Local Open Scope ring_scope.

Reserved Notation "u '``_' i" (at level 3, i at level 2,
  left associativity, format "u '``_' i").
Reserved Notation "u *d w" (at level 40).

Lemma cat_cons4 T (I L M N : seq T * seq T):
 [:: I; L; M; N] = [:: I] ++ [:: L] ++ [:: M] ++ [:: N].
Proof. by []. Qed.

Lemma cat_cons_xyz_xy {T} (I L M N : seq T * seq T):
 [:: I; L; M; N] = [:: I; L] ++ [::M; N] .
Proof. by rewrite //=. Qed.

Lemma cat_cons_xyz_xyz {T} (I L M N : seq T * seq T):
 [:: I; L; M; N] = [:: I; L; M] ++ [:: N] .
Proof. by rewrite //=. Qed.

Lemma In_in (I : eqType) (s : seq I) e : e \in s <-> List.In e s.
Proof.
elim: s => //= h t ih; split=> [|[<-|/ih] ].
- by rewrite inE => /predU1P[->|/ih]; [left|right].
- by rewrite mem_head.
- by rewrite inE => ->; rewrite orbT.
Qed.

Lemma map_cons T1 T2 (f : T1 -> T2) a l :
  f a :: [seq f x | x <- l] = [seq f x | x <- a :: l].
Proof. by []. Qed.

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

Lemma invrM' {R : realFieldType} (x y : R) : x != 0 -> (x * y)^-1 = x^-1 * y^-1.
Proof. nra. Qed.

(* TODO: PR to MathComp *)
Lemma scalerN1 {R : ringType} (p : R^o) : p *: -1 = - p.
Proof. by transitivity (p * -1) => //; rewrite mulrN1. Qed.

(* TODO: PR to MathComp *)
Lemma naddr_lt0 {R : realDomainType} (x y : R) :
  x <= 0 -> y <= 0 -> x + y < 0 -> (x < 0) || (y < 0).
Proof.
move=> x0 y0; rewrite !ltNge -negb_and; apply: contra.
by move=> /andP[x0' y0']; rewrite addr_ge0.
Qed.

Definition row_of_seq {R : numDomainType} (s : seq R) : 'rV[R]_(size s) :=
  (\row_(i < size s) tnth (in_tuple s) i).

Lemma seq_of_rV_const {R : fieldType} (p : R) n :
  @MatrixFormula.seq_of_rV R n (const_mx p) = nseq n p.
Proof.
apply: (@eq_from_nth _ 0).
  by rewrite MatrixFormula.size_seq_of_rV size_nseq.
move=> k; rewrite MatrixFormula.size_seq_of_rV => kM.
have -> := @MatrixFormula.nth_seq_of_rV R _ 0 (const_mx p) (Ordinal kM).
by rewrite mxE nth_nseq kM.
Qed.

(* TODO(rei): this notation breaks the display of ball predicates *)
Notation "u '``_' i" := (u 0%R i) : ring_scope.

Section alias_for_bigops.
Context {R : numDomainType}.
Implicit Types s : seq R.

(*Definition sumR s := \sum_(i <- s) i.*)
(*Definition prodR s := \prod_(i <- s) i.*)
Definition minR n f : R := \big[minr/1]_(i < n) f i.
Definition maxR n f : R := \big[maxr/0]_(i < n) f i.

End alias_for_bigops.

Lemma sum_01 {R : numDomainType} n (f : 'I_n -> R) :
  (forall i, f i <= 1) -> \sum_i f i <= n%:R.
Proof.
move: f; elim: n => [f h | n ih f h]; first by rewrite big_ord0.
by rewrite big_ord_recl -nat1r lerD// ih.
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

Lemma prod01 {R : realDomainType} n [s : 'I_n -> R] :
  (forall i, 0 <= s i <= 1) -> (0 <= \prod_(j < n) s j <= 1).
Proof.
move: s; elim: n => [s h|n ih s h]; first by rewrite big_ord0 ler01 lexx.
rewrite big_ord_recl.
have h0 : forall i, 0 <= s (lift ord0 i) <= 1 by move=> i; apply: h.
have := ih (s \o lift ord0) h0.
have := h ord0.
nra.
Qed.

Lemma psumr_eqsize {R : realDomainType} :
  forall n [F : 'I_n -> R],
  (forall i, F i <= 1)%R ->
  (\sum_(i < n) F i = n%:R) <-> forall i, F i = 1.
Proof.
elim; first by move=> F h; rewrite big_ord0; split => // _; case.
move => n ih F h1; split.
- rewrite big_ord_recl/=.
  have : (\sum_(i < n) F (lift ord0 i) <= n%:R)%R.
    by apply/(@sum_01 _ _ (fun i => F (lift ord0 i))) => i; exact: h1.
  rewrite /= le_eqVlt => /predU1P[h|h].
    rewrite -natr1 h addrC.
    move/addrI => h' i.
    have [->//|/eqP i0] := eqVneq i ord0.
    move: i0; case: (unliftP ord0 i) => //= j -> _.
    by have /= -> := ((@ih (F \o lift ord0) _).1).
  rewrite /= -nat1r.
  move: h.
  set x := \sum_(i < n) F (lift ord0 i).
  set y := n.
  have := h1 ord0.
  lra.
move=> h.
rewrite /= -nat1r big_ord_recr h/= addrC.
congr +%R.
exact/ih.
Qed.

Lemma prod1_01 {R : realDomainType} :
  forall n [s : 'I_n -> R], (forall i, 0 <= s i <= 1) ->
    (\prod_(j < n) s j = 1 <-> (forall i, s i = (1:R))).
Proof.
elim => [s h|n ih s h]; first by rewrite big_ord0; split => // _; case.
rewrite big_ord_recl.
split.
  move/eqP.
  rewrite prod1; last 2 first.
  - by apply: h; rewrite in_cons eqxx.
  - by apply: prod01 => i; apply: h.
  move/andP => [/eqP e1] /eqP.
  rewrite ih; last first.
    by move=> i; apply: h.
  move=> h' i0.
  by case: (unliftP ord0 i0) => /= [j ->|->].
by move=> h'; rewrite h' mul1r ih.
Qed.

Lemma prodrN1 {R : realDomainType} (T : eqType) (l : seq T) (f : T -> R) :
  (forall e, e \in l -> f e < 0)%R ->
  sgr (\prod_(e <- l) f e) = (- 1) ^+ (size l).
Proof.
elim: l => [|a l ih h]; first by rewrite big_nil/= expr0 sgr1.
rewrite big_cons sgrM ltr0_sg ?h ?mem_head//= exprS ih// => e el.
by rewrite h// in_cons el orbT.
Qed.

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
      by rewrite in_cons => /predU1P[->//|el0]; exact: h3.
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

Section maxmin.
Context {d} {R : orderType d}.

Lemma minrxyx (x y : R) : Order.min x (Order.min y x) = Order.min x y.
Proof. by rewrite (minC y) minA minxx. Qed.

Lemma maxrxyx (x y : R) : Order.max x (Order.max y x) = Order.max y x.
Proof. by rewrite (maxC y) maxA maxxx. Qed.

End maxmin.

Lemma iter_minr {R : realDomainType} k p p' : k != 0%N ->
  p' >= p -> iter k (minr p) p' = p :> R.
Proof.
elim: k p p' => //= -[_ /= p' p _ p'p|k ih p p' _ pp'].
  rewrite /minr; case: ifPn => //.
  by rewrite -leNgt => pp'; apply/eqP; rewrite eq_le p'p pp'.
by rewrite ih// minxx.
Qed.

Lemma iter_minr' {R : realDomainType} k p p' : k != 0%N ->
  p' <= p -> iter k (minr p) p' = p' :> R.
Proof.
elim: k p p' => //= -[_ /= p p' _ p'p|n ih p p' _ p'p].
  by rewrite /minr ltNge p'p.
by rewrite ih// /minr ltNge p'p.
Qed.

Lemma big_min_def_cons {d} {R : orderType d} (T : Type) (f : T -> R) a l :
  \big[Order.min/f a]_(j <- a :: l) f j =
  \big[Order.min/f a]_(j <- l) f j.
Proof.
elim: l; first by rewrite big_cons big_nil minxx.
by move=> a0 l; rewrite !big_cons => IH; rewrite minCA IH.
Qed.

Lemma big_max_def_cons {d} {R : orderType d} (T : Type) (f : T -> R) a l :
  \big[Order.max/f a]_(j <- a :: l) f j =
  \big[Order.max/f a]_(j <- l) f j.
Proof.
elim: l; first by rewrite big_cons big_nil maxxx.
by move=> a0 l; rewrite !big_cons => IH; rewrite maxCA IH.
Qed.

Lemma big_min_def_swap {d} {R : orderType d} (T : Type) (f : T -> R) a a0 l :
  Order.min a (\big[Order.min/a0]_(j <- l) f j) =
  Order.min a0 (\big[Order.min/a]_(j <- l) f j).
Proof.
elim: l; first by rewrite !big_nil minC.
by move=> a1 l ih; rewrite !big_cons minCA ih minCA.
Qed.

Lemma big_max_def_swap {d} {R : orderType d} (T : Type) (f : T -> R) a a0 l :
  Order.max a (\big[Order.max/a0]_(j <- l) f j) =
  Order.max a0 (\big[Order.max/a]_(j <- l) f j).
Proof.
elim: l; first by rewrite !big_nil maxC.
by move=> a1 l ih; rewrite !big_cons maxCA ih maxCA.
Qed.

Section big_order_maxmin.
Local Open Scope order_scope.
Context {d} {R : orderType d}.

Lemma big_min_cons (T : eqType) (f : T -> R) (a : T) l :
  forall i, i \in a :: l ->
  \big[Order.min/f i]_(j <- a :: l) f j =
  \big[Order.min/f a]_(j <- l) f j.
Proof.
elim: l.
  by move=> i; rewrite mem_seq1 => /eqP ->; rewrite big_cons !big_nil minxx.
move=> a0 l ih i.
have h a' : Order.min (f a') (\big[Order.min/f a']_(j <- l) f j) =
            \big[Order.min/f a']_(j <- a' :: l) f j by rewrite big_cons.
have h' : Order.min (f a) (\big[Order.min/f i]_(j <- l) f j) =
          \big[Order.min/f i]_(j <- a :: l) f j by rewrite big_cons.
rewrite in_cons => /predU1P[->|]; first by rewrite big_min_def_cons.
rewrite in_cons => /predU1P[->|il]; first by rewrite !big_cons h big_min_def_cons big_min_def_swap.
by rewrite !big_cons minCA h' ih// in_cons il orbT.
Qed.

Lemma big_max_cons (T : eqType) (f : T -> R) (a : T) l :
  forall i, i \in a :: l ->
  \big[Order.max/f i]_(j <- a :: l) f j =
  \big[Order.max/f a]_(j <- l) f j.
Proof.
elim: l.
  by move=> i; rewrite mem_seq1 => /eqP ->; rewrite big_cons !big_nil maxxx.
move=> a0 l ih i.
have h a' : Order.max (f a') (\big[Order.max/f a']_(j <- l) f j) =
            \big[Order.max/f a']_(j <- a' :: l) f j by rewrite big_cons.
have h' : Order.max (f a) (\big[Order.max/f i]_(j <- l) f j) =
          (\big[Order.max/f i]_(j <- a :: l) f j) by rewrite big_cons.
rewrite in_cons => /predU1P[->|]; first by rewrite big_max_def_cons.
rewrite in_cons => /predU1P[->|il]; first by rewrite !big_cons h big_max_def_cons big_max_def_swap.
by rewrite !big_cons maxCA h' ih// in_cons il orbT.
Qed.

(* TODO: rename, this is not on minr anymore but Order.min *)
(* NB: shouldn7t this be a consequence of bigmin_le_cond? *)
Lemma minrgex [I : eqType] x (f : I -> R) a l:
  x <= \big[Order.min/f a]_(j <- l) f j -> forall i, i \in a :: l -> x <= f i.
Proof.
elim: l; first by rewrite big_nil => xfa i; rewrite mem_seq1 => /eqP ->.
move=> a' l IH h i.
rewrite !in_cons => h'.
have {h'} : i \in [:: a', a & l] by rewrite !in_cons orbCA.
rewrite in_cons => /predU1P[->|].
  move: h. rewrite big_cons.
  rewrite /Order.min; case: ifPn => //.
  rewrite -leNgt => h1 h2.
  exact: (le_trans h2 h1).
apply: IH.
move: h. rewrite big_cons /Order.min; case: ifPn => // h1 h2.
exact: (le_trans h2 (ltW h1)).
Qed.

Lemma minrltx [I : eqType] x (f : I -> R) a l:
  \big[Order.min/f a]_(j <- l) f j < x -> exists2 i, i \in a :: l & f i < x.
Proof.
elim: l; first by rewrite big_nil => fax; exists a; rewrite ?mem_head.
move=> a' l IH.
rewrite big_cons {1}/Order.min.
case: ifPn => [_ fax|_]; first by exists a' => //; rewrite ?inE ?eqxx ?orbT.
move/IH => [i ial ?].
by exists i => //; rewrite inE in ial; rewrite !inE orbCA ial orbT.
Qed.

Lemma maxrltx [I : eqType] x (f : I -> R) a l:
  \big[Order.max/f a]_(j <- l) f j < x -> forall i, i \in a :: l -> f i < x.
Proof.
elim: l; first by rewrite big_nil => fax i; rewrite mem_seq1 => /eqP ->.
move=> a' l IH.
rewrite big_cons {1}/Order.max.
case: ifPn => [fa'lt maxltx i|].
  rewrite in_cons => /predU1P[->|]; first by apply IH => //; rewrite mem_head.
  rewrite in_cons => /predU1P[->|il]; first exact: (lt_trans fa'lt maxltx).
  by apply: IH => //; rewrite in_cons il orbT.
rewrite -leNgt => fmaxltfa' fa'ltx i.
rewrite in_cons => /predU1P[->|].
  by apply: IH; rewrite ?mem_head// (le_lt_trans fmaxltfa' fa'ltx).
rewrite in_cons => /predU1P[->//|il].
by rewrite IH// ?(le_lt_trans fmaxltfa' fa'ltx)// in_cons il orbT.
Qed.

Lemma maxrlex [I : eqType] x (f : I -> R) a l:
  \big[Order.max/f a]_(j <- l) f j <= x -> forall i, i \in a :: l -> f i <= x.
Proof.
elim: l; first by rewrite big_nil => fax i; rewrite mem_seq1 => /eqP ->.
move=> a' l IH.
rewrite big_cons {1}/Order.max.
case: ifPn => [fa'lt maxltx i|].
  rewrite in_cons => /predU1P[->|]; first by apply IH => //; rewrite mem_head.
  rewrite in_cons => /predU1P[->|il]; first exact: (ltW (lt_le_trans fa'lt maxltx)).
  by apply: IH => //; rewrite in_cons il orbT.
rewrite -leNgt => fmaxltfa' fa'ltx i.
rewrite in_cons => /predU1P[->|].
  by apply: IH; rewrite ?mem_head// (le_trans fmaxltfa' fa'ltx).
rewrite in_cons => /predU1P[->//|il].
by rewrite IH// ?(le_trans fmaxltfa' fa'ltx)// in_cons il orbT.
Qed.

Lemma maxrgtx [I : eqType] x (f : I -> R) a l:
  x < \big[Order.max/f a]_(j <- l) f j -> exists2 i, i \in a :: l & x < f i.
Proof.
elim: l; first by rewrite big_nil => fax; exists a => //; rewrite mem_head.
move=> a' l IH.
rewrite big_cons {1}/Order.max.
case: ifPn => [_|_ fax]; last by exists a' => //; rewrite !in_cons eqxx/= orbT.
move/IH => [i ial filex].
by eexists i => //; rewrite !in_cons orbCA -in_cons ial orbT.
Qed.

Lemma maxrgex [I : eqType] x (f : I -> R) a l:
  x <= \big[Order.max/f a]_(j <- l) f j -> exists2 i, i \in a :: l & x <= f i.
Proof.
elim: l; first by rewrite big_nil => fax; exists a => //; rewrite mem_seq1 eqxx.
move=> a' l IH.
rewrite big_cons {1}/Order.max.
case: ifPn => [_|_ fax]; last by exists a' => //; rewrite !in_cons eqxx/= orbT.
move/IH => [i ial filex].
by exists i => //; rewrite !in_cons orbCA -in_cons ial orbT.
Qed.

Lemma bigmin_eqP (x : R) [I : eqType] (s : seq I) (F : I -> R) :
  reflect (forall i : I, i \in s -> x <= F i)
          (\big[Order.min/x]_(i <- s) F i == x).
Proof.
apply: (iffP eqP) => [<- i|].
- elim: s => // a s IH.
  rewrite in_cons => /predU1P[<-|si].
  + by rewrite big_seq big_cons mem_head ge_min lexx.
  + by rewrite big_cons minC ge_min IH.
- elim: s => [h|i l IH h].
  + by rewrite big_nil.
  + rewrite big_cons IH ?min_r ?h ?mem_head// => a al.
    by rewrite h// in_cons al orbT.
Qed.

(* NB: not used *)
(* TODO(ab): not needed, but maybe worth having instead of bigmax_le? *)
Lemma bigmax_le' :
  forall [I : eqType] (r : seq I) (f : I -> R) (P : pred I) (x0 x : R),
    reflect (x0 <= x /\ forall i, i \in r -> P i -> f i <= x)
      (\big[Order.max/x0]_(i <- r | P i) f i <= x).
Proof.
move=> I r f P x0.
elim: r => [x|]; first by rewrite big_nil; apply: (iffP idP);move=>//[->//].
move=> a l0 IH x.
apply: (iffP idP).
- rewrite big_cons {1}/Order.max.
  case: ifPn => Pa.
  + case: ifPn => [fabig h|].
    * have /IH[-> h'] := h; split=>//i.
      rewrite in_cons => /predU1P[-> _|il0 Pi].
        by apply: le_trans (ltW fabig) h.
      exact: h'.
    rewrite -leNgt => fabig fax.
    have /IH[x0fa h] := fabig.
    split; first apply: (le_trans x0fa fax).
    move=> i.
    rewrite in_cons => /predU1P[->//|il0 Pi].
    apply: le_trans.
    apply: h => //.
    apply: fax.
  + move=> /IH[-> h]; split=>// i.
    rewrite in_cons => /predU1P[->|]; first by move: Pa=> /[swap]->.
    exact: h.
- move=>[x0x h].
  have h' i : i \in l0 -> P i -> f i <= x.
    by move=> il0 Pi; rewrite h ?in_cons ?il0 ?orbT.
  have /IH h'' := conj x0x h'.
  rewrite big_cons {1}/Order.max.
  case: ifPn => Pa //.
  case: ifPn => //_.
  apply: h => //.
  exact: mem_head.
Qed.

End big_order_maxmin.

Lemma min_big_min {d} {R : orderType d} (a : R) (s : seq R) :
  Order.min a (\big[Order.min/a]_(i <- s) i) = \big[Order.min/a]_(i <- s) i.
Proof.
have := big_min_def_cons idfun a s.
by rewrite big_cons.
Qed.

Lemma mem_min_big_min {d} {R : orderType d} (a1 a2 : R) (s : seq R) :
  a1 \in s ->
  Order.min a1 (\big[Order.min/a2]_(i <- s) i) = \big[Order.min/a2]_(i <- s) i.
Proof.
elim: s => [|a3 l ih]; first by rewrite in_nil.
rewrite inE => /predU1P[-> | a1l].
  by rewrite !big_cons minA minxx.
by rewrite !big_cons minCA ih.
Qed.

Lemma big_min_def {d} {R : orderType d} (a1 a2 : R) (s : seq R) :
  a1 \in s -> a2 \in s ->
  \big[Order.min/a1]_(i <- s) i = \big[Order.min/a2]_(i <- s) i.
Proof.
elim: s => [|a l ih]; first by rewrite in_nil.
rewrite inE => /predU1P[-> |a1l].
  rewrite inE => /predU1P[-> //|a2l].
  by rewrite big_cons min_big_min big_cons big_min_def_swap mem_min_big_min.
rewrite inE => /predU1P[-> |a2l].
  by rewrite big_cons big_min_def_swap big_cons mem_min_big_min// min_big_min.
by rewrite !big_cons ih.
Qed.

Lemma perm_eq_big_min {d} {R : orderType d}  (a1 a2 : R) (l1 l2 : seq R) :
  perm_eq (a1 :: l1) (a2 :: l2) ->
  \big[Order.min/a1]_(i <- l1) i = \big[Order.min/a2]_(i <- l2) i.
Proof.
move=> pi.
rewrite -big_min_def_cons (perm_big _ pi)/= (@big_min_def _ _ a1 a2).
- by rewrite big_min_def_cons.
- by rewrite -(perm_mem pi) inE eqxx.
- by rewrite mem_head.
Qed.

Lemma perm_eq_fun (n : nat) (pi : {perm 'I_n}) :
  perm_eq (index_enum 'I_n) [seq pi i | i <- index_enum 'I_n].
Proof.
apply/allP => i/=.
rewrite mem_cat => /orP[ hi | hi ].
  rewrite !count_uniq_mem//.
  - rewrite hi (_ : i \in map pi (index_enum 'I_n))//.
    by apply/mapP; exists ((perm_inv pi) i); [ exact/mem_index_enum | rewrite permKV].
  - by rewrite map_inj_uniq ?index_enum_uniq//; exact/perm_inj.
  - by rewrite index_enum_uniq.
rewrite !count_uniq_mem.
- by rewrite hi mem_index_enum.
- by rewrite map_inj_uniq ?index_enum_uniq//; exact/perm_inj.
- by rewrite index_enum_uniq.
Qed.
