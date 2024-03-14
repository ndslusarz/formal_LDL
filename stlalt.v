From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import util ldl.
Require Import lhopital.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Section stl_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (nu : R).
Hypothesis nu0 : 0 < nu.

Lemma andI_stl (e : expr Bool_N) :
  nu.-[[e `/\ e]]_stl' = nu.-[[e]]_stl'.
Proof.
rewrite /= /stl_and_gt0 /stl_and_lt0 /min_dev /sumR.
rewrite !big_cons !big_nil/=.
rewrite !minrxxx.
set a_min := minr (nu.-[[e]]_stl') (nu.-[[e]]_stl').
set a := ((nu.-[[e]]_stl' - a_min) * a_min^-1).
have a_min_e : a_min = nu.-[[e]]_stl'.
  by rewrite /a_min /minr; repeat case: ifPn => //; rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0.
  by rewrite /a a_min_e subrr ?mul0r.
rewrite !addr0 !mulr0 expR0 !mulr1/= a_min_e.
have -> : ((nu.-[[e]]_stl' + nu.-[[e]]_stl') * (1 + 1)^-1) = nu.-[[e]]_stl'.
  have -> : 1 + 1 = (2 : R) by lra.
  by rewrite mulrDl -splitr.
case: ifPn => //h1.
case: ifPn => //h2.
by apply le_anti; rewrite !leNgt; rewrite h1 h2.
Qed.

Lemma andC_stl (e1 e2 : expr Bool_N) :
  nu.-[[e1 `/\ e2]]_stl' = nu.-[[e2 `/\ e1]]_stl'.
Proof.
rewrite /= /stl_and_gt0/stl_and_lt0 /min_dev
/sumR !big_cons !big_nil/= !addr0/=.
rewrite !minrxyx !minrxx. 
set a_min := minr (nu.-[[e1]]_stl') (nu.-[[e2]]_stl').
have -> : (minr (nu.-[[e2]]_stl') (nu.-[[e1]]_stl')) = a_min.
  by rewrite /a_min/minr; case: ifPn => h1; case: ifPn => h2//; lra.
set a1 := ((nu.-[[e1]]_stl' - a_min) * a_min^-1).
set a2 := ((nu.-[[e2]]_stl' - a_min) * a_min^-1).
set d1 := (expR (nu * a1) + expR (nu * a2))%R.
have -> : (expR (nu * a2) + expR (nu * a1))%R = d1.
  by rewrite addrC.
case: ifPn; first by rewrite addrC .
case: ifPn; first by rewrite addrC (addrC (expR (- nu * a1)) (expR (- nu * a2))) .
lra. 
Qed.


Lemma orI_stl (e : expr Bool_N) :
  nu.-[[e `\/ e]]_stl' = nu.-[[e]]_stl'.
Proof.
rewrite /= /stl_or_gt0 /stl_or_lt0 /max_dev
/sumR !big_cons !big_nil/= !addr0.
rewrite !maxrxxx.
set a_max := maxr (nu.-[[e]]_stl') (nu.-[[e]]_stl').
set a :=  ((a_max - nu.-[[e]]_stl') / a_max).
have a_max_e : a_max = nu.-[[e]]_stl'.
  by rewrite /a_max /maxr; repeat case: ifPn => //; rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0.
  by rewrite /a a_max_e subrr ?mul0r.
rewrite !mulr0 expR0 !mulr1/= a_max_e.
have -> : ((nu.-[[e]]_stl' + nu.-[[e]]_stl') * (1 + 1)^-1) = nu.-[[e]]_stl'.
  have -> : 1 + 1 = (2 : R) by lra.
  by rewrite mulrDl -splitr.
case: ifPn => //h1.
case: ifPn => //h2.
by apply le_anti; rewrite !leNgt h1 h2.
Qed.

Lemma orC_stl (e1 e2 : expr Bool_N) :
  nu.-[[e1 `\/ e2]]_stl'  = nu.-[[e2 `\/ e1]]_stl'.
Proof.
rewrite /=/stl_or_gt0 /stl_or_lt0 /max_dev
/sumR !big_cons !big_nil/= !addr0.
rewrite !maxrxyx !maxrxx.
set a_max := maxr (nu.-[[e2]]_stl') (nu.-[[e1]]_stl').
have -> : maxr (nu.-[[e1]]_stl') (nu.-[[e2]]_stl') = a_max.
  by rewrite /a_max/maxr; case: ifPn => //; case: ifPn => //; lra.
set a1 := ((a_max - nu.-[[e1]]_stl') * a_max^-1).
set a2 := ((a_max - nu.-[[e2]]_stl') * a_max^-1).
set d1 := (expR (nu * a1) + expR (nu * a2))%R.
have -> : (expR (nu * a2) + expR (nu * a1))%R = d1.
  by rewrite addrC.
case: ifPn; first by rewrite addrC.
by case: ifPn; first by rewrite addrC.
Qed.

Lemma stl_translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  nu.-[[ e ]]_stl' = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ _ e2 erefl JMeq_refl).
Qed.

Lemma stl_translations_Index_coincide: forall n (e : expr (Index_T n)),
  nu.-[[ e ]]_stl' = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma stl_translations_Real_coincide (e : expr Real_T):
  nu.-[[ e ]]_stl' = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite stl_translations_Vector_coincide stl_translations_Index_coincide.
Qed.

Definition is_stl b (x : R) := (if b then x >= 0 else x < 0).

Lemma sumr_lt0 [I : eqType] [r : seq I]
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

Lemma sumr_gt0 [I : eqType] [r : seq I]
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

Lemma minrgex [I : eqType] x (f : I -> R) a l:
  x <= \big[minr/f a]_(j <- l) f j -> forall i, i \in (a :: l) -> x <= f i.
Proof.
elim: l; first by rewrite big_nil => xfa i; rewrite mem_seq1 => /eqP ->.
move=> a' l IH h i.
rewrite !in_cons => h'.
have {h'} : i \in [:: a', a & l] by rewrite !in_cons orbCA.
rewrite in_cons => /orP[/eqP ->|].
  move: h. rewrite big_cons /minr. case: ifPn => //.
  rewrite -leNgt => h1 h2.
  exact: (le_trans h2 h1).
apply: IH.
move: h. rewrite big_cons /minr. case: ifPn => // h1 h2.
exact: (le_trans h2 (ltW h1)).
Qed.

Lemma minrltx [I : eqType] x (f : I -> R) a l:
  \big[minr/f a]_(j <- l) f j < x -> exists i, i \in (a :: l) /\ f i < x.
Proof.
elim: l; first by rewrite big_nil => fax; exists a; rewrite mem_seq1 eq_refl fax.
move=> a' l IH.
rewrite big_cons {1}/minr.
case: ifPn => [_ fax|_]; first by exists a'; rewrite !in_cons eq_refl/= orbT fax.
move/IH => [i[ial filex]].
exists i.
by rewrite !in_cons orbCA -in_cons ial orbT filex.
Qed.

Lemma maxrltx [I : eqType] x (f : I -> R) a l:
  \big[maxr/f a]_(j <- l) f j < x -> forall i, i \in (a :: l) -> f i < x.
Proof.
elim: l; first by rewrite big_nil => fax i; rewrite mem_seq1 => /eqP ->.
move=> a' l IH.
rewrite big_cons {1}/maxr.
case: ifPn => [fa'lt maxltx i|].
  rewrite in_cons => /orP[/eqP ->|]; first by apply IH => //; rewrite mem_head.
  rewrite in_cons => /orP[/eqP ->|il]; first exact: (lt_trans fa'lt maxltx).
  by apply: IH => //; rewrite in_cons il orbT.
rewrite -leNgt => fmaxltfa' fa'ltx i.
rewrite in_cons => /orP[/eqP ->|].
  by apply: IH; rewrite ?mem_head// (le_lt_trans fmaxltfa' fa'ltx).
rewrite in_cons => /orP[/eqP ->//|il].
by rewrite IH// ?(le_lt_trans fmaxltfa' fa'ltx)// in_cons il orbT.
Qed.

Lemma maxrlex [I : eqType] x (f : I -> R) a l:
  \big[maxr/f a]_(j <- l) f j <= x -> forall i, i \in (a :: l) -> f i <= x.
Proof.
elim: l; first by rewrite big_nil => fax i; rewrite mem_seq1 => /eqP ->.
move=> a' l IH.
rewrite big_cons {1}/maxr.
case: ifPn => [fa'lt maxltx i|].
  rewrite in_cons => /orP[/eqP ->|]; first by apply IH => //; rewrite mem_head.
  rewrite in_cons => /orP[/eqP ->|il]; first exact: (ltW (lt_le_trans fa'lt maxltx)).
  by apply: IH => //; rewrite in_cons il orbT.
rewrite -leNgt => fmaxltfa' fa'ltx i.
rewrite in_cons => /orP[/eqP ->|].
  by apply: IH; rewrite ?mem_head// (le_trans fmaxltfa' fa'ltx).
rewrite in_cons => /orP[/eqP ->//|il].
by rewrite IH// ?(le_trans fmaxltfa' fa'ltx)// in_cons il orbT.
Qed.

Lemma maxrgtx [I : eqType] x (f : I -> R) a l:
  x < \big[maxr/f a]_(j <- l) f j -> exists i, i \in (a :: l) /\ x < f i.
Proof.
elim: l; first by rewrite big_nil => fax; exists a; rewrite mem_seq1 eq_refl fax.
move=> a' l IH.
rewrite big_cons {1}/maxr.
case: ifPn => [_|_ fax]; last by exists a'; rewrite !in_cons eq_refl/= orbT fax.
move/IH => [i[ial filex]].
exists i.
by rewrite !in_cons orbCA -in_cons ial orbT filex.
Qed.

Lemma maxrgex [I : eqType] x (f : I -> R) a l:
  x <= \big[maxr/f a]_(j <- l) f j -> exists i, i \in (a :: l) /\ x <= f i.
Proof.
elim: l; first by rewrite big_nil => fax; exists a; rewrite mem_seq1 eq_refl fax.
move=> a' l IH.
rewrite big_cons {1}/maxr.
case: ifPn => [_|_ fax]; last by exists a'; rewrite !in_cons eq_refl/= orbT fax.
move/IH => [i[ial filex]].
exists i.
by rewrite !in_cons orbCA -in_cons ial orbT filex.
Qed.

Lemma seq_cons T1 T2 (f : T1 -> T2) a l : f a :: [seq f x | x <- l] = [seq f x | x <- a :: l].
Proof. by []. Qed.

Lemma minrAC : forall (x y z : R), minr x (minr y z) = minr y (minr x z).
Proof. move=> x y z; rewrite/minr; repeat case: ifPn; lra. Qed.

Lemma minrC : forall (x y : R), minr x y = minr y x.
Proof. rewrite /minr=>x y. case: ifPn; case: ifPn; lra. Qed.

Lemma big_min_helper (T : eqType) (f : T -> R) a l :
  \big[minr/f a]_(j <- (a :: l)) f j =
    \big[minr/f a]_(j <- l) f j.
Proof.
elim: l; first by rewrite big_cons big_nil minrxx.
by move=> a0 l; rewrite !big_cons => IH; rewrite minrAC IH.
Qed.

Lemma big_min_helper2 (T : eqType) (f : T -> R) a a0 l :
  minr (f a) (\big[minr/f a0]_(j <- l) f j) = minr (f a0) (\big[minr/f a]_(j <- l) f j).
Proof.
elim: l; first by rewrite !big_nil minrC.
by move=> a1 l ih; rewrite !big_cons minrAC ih minrAC.
Qed.

Lemma big_min_cons (T : eqType) (f : T -> R) (a : T) l :
  forall i, i \in (a :: l) ->
        \big[minr/f i]_(j <- (a :: l)) f j =
          \big[minr/f a]_(j <- l) f j.
Proof.
elim: l.
  by move=> i; rewrite mem_seq1 => /eqP ->; rewrite big_cons !big_nil minrxx.
move=> a0 l ih i.
have h a' : minr (f a') (\big[minr/f a']_(j <- l) f j) = \big[minr/f a']_(j <- (a'::l)) f j by rewrite big_cons.
have h' : minr (f a) (\big[minr/f i]_(j <- l) f j) = (\big[minr/f i]_(j <- (a::l)) f j) by rewrite big_cons.
rewrite in_cons => /orP[/eqP ->|]; first by rewrite big_min_helper.
rewrite in_cons => /orP[/eqP ->|il]; first by rewrite !big_cons h big_min_helper big_min_helper2.
by rewrite !big_cons minrAC h' ih// in_cons il orbT.
Qed.

Lemma maxrAC : forall (x y z : R), maxr x (maxr y z) = maxr y (maxr x z).
Proof. move=> x y z; rewrite/maxr; repeat case: ifPn; lra. Qed.

Lemma maxrC : forall (x y : R), maxr x y = maxr y x.
Proof. rewrite /maxr=>x y. case: ifPn; case: ifPn; lra. Qed.

Lemma big_max_helper (T : eqType) (f : T -> R) a l :
  \big[maxr/f a]_(j <- (a :: l)) f j =
    \big[maxr/f a]_(j <- l) f j.
Proof.
elim: l; first by rewrite big_cons big_nil maxrxx.
by move=> a0 l; rewrite !big_cons => IH; rewrite maxrAC IH.
Qed.

Lemma big_max_helper2 (T : eqType) (f : T -> R) a a0 l :
  maxr (f a) (\big[maxr/f a0]_(j <- l) f j) = maxr (f a0) (\big[maxr/f a]_(j <- l) f j).
Proof.
elim: l; first by rewrite !big_nil maxrC.
by move=> a1 l ih; rewrite !big_cons maxrAC ih maxrAC.
Qed.

Lemma big_max_cons (T : eqType) (f : T -> R) (a : T) l :
  forall i, i \in (a :: l) ->
        \big[maxr/f i]_(j <- (a :: l)) f j =
          \big[maxr/f a]_(j <- l) f j.
Proof.
elim: l.
  by move=> i; rewrite mem_seq1 => /eqP ->; rewrite big_cons !big_nil maxrxx.
move=> a0 l ih i.
have h a' : maxr (f a') (\big[maxr/f a']_(j <- l) f j) = \big[maxr/f a']_(j <- (a'::l)) f j by rewrite big_cons.
have h' : maxr (f a) (\big[maxr/f i]_(j <- l) f j) = (\big[maxr/f i]_(j <- (a::l)) f j) by rewrite big_cons.
rewrite in_cons => /orP[/eqP ->|]; first by rewrite big_max_helper.
rewrite in_cons => /orP[/eqP ->|il]; first by rewrite !big_cons h big_max_helper big_max_helper2.
by rewrite !big_cons maxrAC h' ih// in_cons il orbT.
Qed.

Lemma stl_nary_inversion_andE1 (Es : seq (expr Bool_P) ) :
  is_stl true (nu.-[[ ldl_and Es ]]_stl') -> (forall i, (i < size Es)%N -> is_stl true (nu.-[[ nth (ldl_bool pos false) Es i ]]_stl')).
Proof.
case: Es => // a l.
rewrite/is_stl/= /stl_and_gt0/stl_and_lt0 /min_dev (* !foldrE *) (* !big_map *).
rewrite /sumR !seq_cons !big_map.
set a_min := \big[minr/nu.-[[a]]_stl']_(j <- l) nu.-[[j]]_stl'.
case: ifPn=>[hminlt0|].
  have /=[y[ymem ylt0]] := minrltx _ _ _ _ hminlt0.
  rewrite !big_seq.
  under eq_bigr => i il do rewrite seq_cons big_map big_min_cons//.
  under [X in _ / X]eq_bigr => i il do rewrite seq_cons big_map big_min_cons//.
  rewrite/= leNgt.
  rewrite pmulr_llt0 ?invr_gt0; last first.
    rewrite sumr_gt0//=.
      by move => i _ _; rewrite expR_ge0.
    by exists y; rewrite ymem expR_gt0.
  rewrite sumr_lt0//.
    by move => i _ _; rewrite nmulr_rle0 ?expR_ge0// nmulr_rlt0// expR_gt0.
  by exists y; rewrite !nmulr_rlt0 ?expR_gt0//.
rewrite -leNgt; move/minrgex => h.
by case: ifPn => _ _ i isize; rewrite h// mem_nth.
Qed.

Lemma stl_nary_inversion_andE0 (Es : seq (expr Bool_P) ) :
  is_stl false (nu.-[[ ldl_and Es ]]_stl') -> (exists (i : nat), is_stl false (nu.-[[ nth (ldl_bool pos false) Es i ]]_stl') && (i < size Es)%nat).
Proof.
case: Es => [|a l]; first by rewrite /= ltr10.
rewrite/is_stl/= big_map.
set a_min := \big[minr/nu.-[[a]]_stl']_(j <- l) nu.-[[j]]_stl'.
case: ifPn=>[hminlt0 _|].
  have [x [xmem hlt0]] := minrltx _ _ _ _ hminlt0.
  exists (index x (a :: l)).
  by rewrite nth_index ?xmem// hlt0 index_mem xmem.
rewrite -leNgt => hminge0.
case: ifPn => _; last by rewrite lt_irreflexive.
rewrite ltNge mulr_ge0// ?invr_ge0 /sumR big_cons !big_map big_seq_cond addr_ge0 ?mulr_ge0 ?expR_ge0 ?sumr_ge0//=.
  by apply: (minrgex _ _ _ _ hminge0); rewrite mem_head.
all: move=> i /andP[il _]; rewrite ?mulr_ge0 ?expR_ge0//.
by apply: (minrgex _ _ _ _ hminge0); rewrite in_cons il orbT.
Qed.

Lemma stl_nary_inversion_orE1 (Es : seq (expr Bool_P) ) :
  is_stl true (nu.-[[ ldl_or Es ]]_stl') -> (exists i, is_stl true (nu.-[[ nth (ldl_bool _ false) Es i ]]_stl') && (i < size Es)%nat).
Proof.
case: Es => [|a l]; first by rewrite /= ler0N1.
rewrite/is_stl/= /stl_or_gt0/stl_or_lt0/max_dev /sumR !seq_cons !big_map.
set a_max := \big[maxr/nu.-[[a]]_stl']_(j <- l) nu.-[[j]]_stl'.
case: ifPn=>[hmaxgt0 _|].
  have [x [xmem hgt0]] := maxrgtx _ _ _ _ hmaxgt0.
  exists (index x (a :: l)).
  by rewrite nth_index ?xmem// (ltW hgt0) index_mem xmem.
rewrite -leNgt => hmaxle0.
case: ifPn=>[hmaxlt0|].
  have /= := maxrltx _ _ _ _ hmaxlt0.
  rewrite !big_seq.
  under eq_bigr => i il do rewrite seq_cons big_map big_max_cons//.
  under [X in _ / X]eq_bigr => i il do rewrite seq_cons big_map big_max_cons//.
  rewrite leNgt=> hilt0.
  rewrite pmulr_llt0 ?invr_gt0; last first.
    rewrite sumr_gt0//=.
      by move => i _ _; rewrite expR_ge0.
    by exists a; rewrite mem_head expR_gt0.
  rewrite sumr_lt0//.
    by move => i imem _; rewrite nmulr_rle0 ?expR_ge0 ?hilt0//. 
  exists a.
  by rewrite mem_head nmulr_rlt0 ?expR_gt0 ?hilt0 ?mem_head.
rewrite -leNgt => hmaxge0 _.
have /=[x [xmem hxge0]] := maxrgex _ _ _ _ hmaxge0.
exists (index x (a :: l)).
by rewrite nth_index ?xmem// hxge0 index_mem xmem.
Qed.

Lemma stl_nary_inversion_orE0 (Es : seq (expr Bool_P) ) :
    is_stl false (nu.-[[ ldl_or Es ]]_stl') -> (forall i, (i < size Es)%nat -> is_stl false (nu.-[[ nth (ldl_bool pos false) Es i ]]_stl')).
Proof.
case: Es => // a l.
rewrite/is_stl/= /stl_or_gt0/stl_or_lt0 big_map.
set a_max := \big[maxr/nu.-[[a]]_stl']_(j <- l) nu.-[[j]]_stl'.
case: ifPn=>[hmaxgt0|].
  rewrite !seq_cons/sumR !big_map!big_seq.
  under eq_bigr => i il do rewrite big_map big_max_cons// -/a_max.
  rewrite ltNge mulr_ge0// /sumR ?invr_ge0 ?sumr_ge0// => [i _/=|i _/=]; rewrite ?mulr_ge0// ?expR_ge0// ltW//.
rewrite -leNgt => h.
case: ifPn; last by rewrite ltxx.
move => hmaxlt0 _ i isize.
by apply: (maxrltx _ _ _ _ hmaxlt0); rewrite mem_nth.
Qed.

Lemma stl_soundness (e : expr Bool_P) b :
  is_stl b (nu.-[[ e ]]_stl') -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind'.
- by move: b b0 => [] [] //=; rewrite ?leNgt ?ltrN10 ?ltr10.
- rewrite List.Forall_forall in H.
  move: b => []. rewrite /is_stl.
  + move/stl_nary_inversion_andE1.
    rewrite [bool_translation (ldl_and l)]/= big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    by apply: H => //; rewrite ?h// -In_in mem_nth.
  + move/stl_nary_inversion_andE0.
    rewrite [bool_translation (ldl_and l)]/= big_map big_all.
    elim=>// i /andP[i0 isize].
    apply/allPn; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    by rewrite -In_in mem_nth.
- rewrite List.Forall_forall in H.
  move: b => [|].
  + move/stl_nary_inversion_orE1.
    rewrite [bool_translation (ldl_or l)]/= big_map big_has.
    elim=>// i /andP[i0 isize].
    apply/hasP; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
  + move/stl_nary_inversion_orE0.
    rewrite [bool_translation (ldl_or l)]/= big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    by apply/negPf; apply: H => //; rewrite ?h// -In_in mem_nth.
- case: c.
  + by case: b; rewrite /is_stl/= ?lee_fin ?lte_fin ?ltNge subr_ge0 !stl_translations_Real_coincide// => /negbTE.
  + case: b; rewrite /is_stl/= ?lee_fin ?lte_fin !stl_translations_Real_coincide.
    by rewrite oppr_ge0 normr_le0 subr_eq0.
    by rewrite oppr_lt0 normr_gt0 subr_eq0 => /negbTE.
Qed.


End stl_lemmas.

From mathcomp Require Import realfun.

Section shadow_lifting_stl_and.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variable nu : R.
Variable M : nat.
Hypothesis M0 : M != 0%N.
(*add hypothesis nu>0 if needed*)

Local Notation seq_of_rV := (@MatrixFormula.seq_of_rV _ M.+1).
Local Notation stl_and_gt0 := (stl_and_gt0 nu).
Local Notation stl_and_lt0 := (stl_and_lt0 nu).

Lemma iter_minr k p p' : k != 0%N -> p' >= p -> iter k (minr p) p' = p :> R.
Proof.
elim: k p p' => //= -[_ /= p' p _ p'p|k ih p p' _ pp'].
  rewrite /minr; case: ifPn => //.
  by rewrite -leNgt => pp'; apply/eqP; rewrite eq_le p'p pp'.
by rewrite ih// minrxx.
Qed.

(* TODO: rename *)
Lemma iter_minr' k p p' : k != 0%N -> p' <= p -> iter k (minr p) p' = p' :> R.
Proof.
elim: k p p' => //= -[_ /= p p' _ p'p|n ih p p' _ p'p].
  by rewrite /minr ltNge p'p.
by rewrite ih// /minr ltNge p'p.
Qed.

Let exp0 K : expR (K * t) @[t --> nbhs 0^'+] --> (1:R)%R.
Proof.
rewrite -expR0; apply: continuous_cvg; first exact: continuous_expR.
rewrite -[X in _ --> X](mulr0 K).
apply: cvgM; first exact: cvg_cst.
exact/cvg_at_right_filter/cvg_id.
Qed.

Lemma shadowlifting_stl_and_gt0 (p : R) : p > 0 -> forall i,
  ('d (stl_and_gt0 \o seq_of_rV) '/d i) (const_mx p) = M.+1%:R^-1.
Proof.
move=> p0 i.
rewrite /partial.
have cpE : seq_of_rV (@const_mx _ _ M.+1 p) = nseq M.+1 p.
  apply: (@eq_from_nth _ 0).
    by rewrite MatrixFormula.size_seq_of_rV size_nseq.
  move=> k; rewrite MatrixFormula.size_seq_of_rV => kM.
  have -> := @MatrixFormula.nth_seq_of_rV R M.+1 0 (const_mx p) (Ordinal kM).
  by rewrite mxE nth_nseq kM.
have H1 : stl_and_gt0 (seq_of_rV (const_mx p)) = p.
  rewrite /stl_and_gt0/= {1}/sumR big_map cpE big_nseq.
  have K1 : min_dev p (nseq M.+1 p) = 0.
    by rewrite /min_dev big_nseq iter_minr// subrr mul0r.
  rewrite K1.
  rewrite mulr0 expR0 mulr1.
  rewrite iter_addr addr0.
  rewrite /sumR big_map big_nseq.
  rewrite K1 mulr0 expR0 iter_addr addr0.
  by rewrite -(mulr_natr p) -mulrA divff ?mulr1.
rewrite /= H1.
have cardM : #|(fun j : 'I_M.+1 => j != i)| = M.
  have := card_ord M.+1.
  rewrite (cardD1 i) inE add1n => -[] hM.
  rewrite -[RHS]hM.
  apply: eq_card => x.
  rewrite inE; apply/idP/idP.
    by rewrite inE andbT.
  by move=> /andP[xi _].
have H2 h : h > 0 ->
  stl_and_gt0 (seq_of_rV (const_mx p + h *: err_vec i)) =
  (p * M%:R + (p + h) * expR (- nu * (h / p))) / (M%:R + expR (-nu * (h / p))).
  move=> h0.
  have mip :
      \big[minr/(p + h)%E]_(i <- seq_of_rV (const_mx p + h *: err_vec i)%R) i = p.
    rewrite big_map/= big_enum/= (bigminD1 i)//.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite big_const/=.
    rewrite iter_minr//; last 2 first.
      by rewrite cardM.
      by rewrite lerDl// ltW.
    by rewrite /minr ltNge lerDl (ltW h0)/=.
  have mip' : \big[minr/p]_(i0 <- seq_of_rV (const_mx p + h *: err_vec i)%E) i0 = p.
    (* NB: almost the same proof as above *)
    rewrite big_map/= big_enum/= (bigminD1 i)//.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite big_const/=.
    rewrite iter_minr//; last first.
      by rewrite cardM.
    by rewrite /minr ltNge lerDl (ltW h0).
  rewrite /stl_and_gt0/= {1}/sumR big_map.
  congr (_ / _).
    rewrite big_map/= big_enum/= (bigD1 i)//=.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (_ : min_dev _ _ = h / p); last first.
      rewrite /min_dev.
      rewrite mip.
      by rewrite -addrA addrCA subrr addr0.
    rewrite (eq_bigr (fun=> p)); last first.
      move=> j ji.
      rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
      rewrite (_ : min_dev _ _ = 0); last first.
        rewrite /min_dev.
        by rewrite mip' subrr mul0r.
      by rewrite mulr0 expR0 mulr1.
    rewrite big_const/= iter_addr addr0 cardM.
    by rewrite addrC mulr_natr.
  rewrite /sumR !big_map/= -enumT /= big_enum/= (bigD1 i)//=.
  rewrite ffunE !mxE eqxx mulr1.
  rewrite (_ : min_dev _ _ = h / p); last first.
    rewrite /min_dev.
    rewrite mip.
    by rewrite -addrA addrCA subrr addr0.
  rewrite (eq_bigr (fun=> 1)); last first.
    move=> j ji.
    rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite (_ : min_dev _ _ = 0); last first.
      rewrite /min_dev.
      by rewrite mip' subrr mul0r.
    by rewrite mulr0 expR0.
  rewrite big_const/= iter_addr addr0 cardM.
  by rewrite [LHS]addrC.

have H3 h : h < 0 -> (stl_and_gt0 (seq_of_rV  (const_mx p + h *: err_vec i))) =
                     (p * M%:R * expR (- nu * (- h / (p + h))) + (p + h))
                     /
                     (M%:R * expR (- nu * (- h / (p + h))) + 1). 
  move=> h0.
  have mip :
      \big[minr/(p + h)%E]_(i <- seq_of_rV (const_mx p + h *: err_vec i)%R) i = p + h.
    rewrite big_map/= big_enum/= (bigminD1 i)//.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    by rewrite big_const/= cardM iter_minr' ?minxx//(*NB: why %E?!*) gerDl ltW.
have mip' : \big[minr/p]_(i0 <- seq_of_rV (const_mx p + h *: err_vec i)%E) i0 = p + h.
    (* NB: almost the same proof as above *)
    rewrite big_map/= big_enum/= (bigminD1 i)//.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    by rewrite big_const/= cardM iter_minr'// /minr ifT// gtrDl.
  rewrite /stl_and_gt0/= /sumR/= !big_map -enumT !big_enum/= (bigD1 i)//=.
  congr (_ / _).
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (_ : min_dev _ _ = 0); last first.
      rewrite /min_dev.
      rewrite mip.
      lra.
    rewrite mulr0 expR0 mulr1 addrC.
    rewrite (eq_bigr (fun=> p * expR (- nu * (- h / (p + h)%E)))); last first.
      move=> j ji.
      rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
      rewrite (_ : min_dev _ _ = -h/(p+h)); last first.
        rewrite /min_dev.
        rewrite mip'. lra.
      done.
    rewrite big_const/= iter_addr addr0 cardM.
    by rewrite -[in LHS]mulr_natr mulrAC.
  rewrite /= (bigD1 i)//=.
  rewrite ffunE !mxE eqxx mulr1.
  rewrite (_ : min_dev _ _ = 0); last first.
    rewrite /min_dev.
    rewrite mip.
    lra.
  rewrite (eq_bigr (fun=> (expR (- nu * (- h / (p + h)%E))))); last first.
    move=> j ji.
    rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite (_ : min_dev _ _ = -h/(p+h)); last first.
      rewrite /min_dev.
      rewrite mip'. lra.
    done.
  rewrite big_const/= iter_addr addr0 cardM.
  by rewrite mulr0 expR0 addrC -[in LHS]mulr_natr mulrC.
have /cvg_lim : h^-1 * ((stl_and_gt0 (seq_of_rV (const_mx p + h *: err_vec i))) -
                        (stl_and_gt0 (seq_of_rV (const_mx p))))
       @[h --> (0:R)^'] --> ((M%:R + 1)^-1:R).
  apply/cvg_at_right_left_dnbhs; rewrite H1.
    apply/cvgrPdist_le => /= e e0.
    near=> t.
    rewrite H2//=.
    rewrite -[X in (_ / _ - X)](mul1r p).
    rewrite -[X in (_ / _ - X * _)](@divff _ (M%:R + expR (- nu * (t / p)))); last first.
      by rewrite lt0r_neq0// addr_gt0// ?expR_gt0// ltr0n lt0n.
    rewrite (mulrAC _ (_^-1) p) -mulrBl.
    have -> : ((p * M%:R)%R + ((p + t)%E * expR (- nu * (t / p)))%R)%E - (M%:R + expR (- nu * (t / p)))%E * p = t * expR (- nu * (t / p)) by lra.
    rewrite !mulrA mulVf// mul1r -(mul1r ((_ + _)^-1)).
    have -> : expR (- nu * t / p) / (M%:R + expR (- nu * t / p))%E = 
((fun t => expR (- nu * t / p)) \* (fun t => (M%:R + expR (- nu * t / p))%E ^-1)) t by [].
    near: t; move: e e0; apply/cvgrPdist_le.
    apply: cvgM.
      by under eq_fun do rewrite mulrAC; exact: exp0.
    apply: cvgV; first by rewrite lt0r_neq0.
    apply: cvgD; first exact: cvg_cst.
    by under eq_fun do rewrite mulrAC; exact: exp0.
  apply/cvgrPdist_le => /= e e0.
  near=> t.
  rewrite H3//=.
  rewrite -[X in (_ / _ - X)](mul1r p).
  rewrite -[X in (_ / _ - X * _)](@divff _ (M%:R * expR (- nu * (- t / (p + t))) + 1)); last first.
    rewrite lt0r_neq0// addr_gt0// ?expR_gt0// mulr_gt0//.
      by rewrite ltr0n lt0n.
      by rewrite expR_gt0.
    rewrite (mulrAC _ (_^-1) p) -mulrBl.
    have -> : (((p * M%:R * expR (- nu * (- t / (p + t)%E)))%R + (p + t))%E -
     ((M%:R * expR (- nu * (- t / (p + t)%E)))%R + 1%R)%E * p) = t by lra.
    have -> : t^-1 * (t / ((M%:R * expR (- nu * (- t / (p + t)%E)))%R + 1%R)%E) =
      1 / ((M%:R * expR (- nu * (- t / (p + t)%E)))%R + 1%R).
      by rewrite (mulrA (t^-1)) mulVf.
    rewrite div1r.
    near: t; move: e e0; apply/cvgrPdist_le.
    apply: cvgV.
      by rewrite gt_eqF.
    apply: cvgD; last exact: cvg_cst.
    rewrite -[X in _ --> X]mulr1; apply: cvgM; first exact: cvg_cst.
    (* expR (- nu * (- x / (p + x)%E)) @[x --> nbhs 0^'-] --> 1 *)
    rewrite -expR0; apply: continuous_cvg; first exact: continuous_expR.
    rewrite -[X in _ --> X](mulr0 (- nu)).
    apply: cvgM; first exact: cvg_cst.
    rewrite [X in _ --> X](_ : _ = (- 0) * p^-1); last by rewrite oppr0 mul0r.
    apply: cvgM.
      apply: cvgN.
      apply: cvg_at_left_filter.
      exact: cvg_id.
    apply: cvgV.
      by rewrite gt_eqF.
    rewrite -[X in _ --> X]addr0.
    apply: cvgD.
      exact: cvg_cst.
    apply: cvg_at_left_filter.
    exact: cvg_id.
rewrite H1 natr1.
apply. exact: Rhausdorff.
Unshelve. all: end_near.
Qed.

Lemma invrM' (x y : R) : x != 0 -> (x * y)^-1 = x^-1 * y^-1.
Proof. nra. Qed.

Lemma scalerN1 (p : R^o) : p *: -1 = - p.
Proof. by transitivity (p * -1) => //; rewrite mulrN1. Qed.

Lemma derive_cst (p x : R) : 'D_1 (fun=> p) x = 0.
Proof. by rewrite -derive1E derive1_cst. Qed.

Lemma derive_id (v : R^o) (x : R) : 'D_v id x = v :> R.
Proof. exact: derive_val. Qed.

Lemma derive_comp (R' : realFieldType) (f g : R'^o -> R'^o) x :
  derivable f x 1 -> derivable g (f x) 1 ->
  'D_1 (g \o f) x = 'D_1 g (f x) * 'D_1 f x.
Proof.
move=> fx1 gfx1.
rewrite -derive1E.
rewrite derive1_comp; last 2 first.
  exact: fx1.
  exact: gfx1.
by rewrite !derive1E.
Qed.

Lemma derivable_comp (f g : R^o -> R^o) (x : R^o) :
  derivable f (g x) 1 -> derivable g x 1 -> derivable (f \o g) x 1.
Proof.
move=> fgx1 gx1.
apply: ex_derive.
apply: is_derive1_comp.
  apply/derivableP.
  exact: fgx1.
exact/derivableP.
Qed.

Lemma shadowlifting_stl_and_lt0 (p : R) : p > 0 -> forall i,
  ('d (stl_and_lt0 \o seq_of_rV) '/d i) (const_mx p) = M.+1%:R^-1.
Proof.
move=> p0 i.
rewrite /partial.
have cpE : seq_of_rV (@const_mx _ _ M.+1 p) = nseq M.+1 p.
  apply: (@eq_from_nth _ 0).
    by rewrite MatrixFormula.size_seq_of_rV size_nseq.
  move=> k; rewrite MatrixFormula.size_seq_of_rV => kM.
  have -> := @MatrixFormula.nth_seq_of_rV R M.+1 0 (const_mx p) (Ordinal kM).
  by rewrite mxE nth_nseq kM.
have H1 : stl_and_lt0 (seq_of_rV (const_mx p)) = p.
  rewrite /stl_and_lt0/= {1}/sumR big_map cpE big_nseq.
  have K1 : min_dev p (nseq M.+1 p) = 0.
    by rewrite /min_dev big_nseq iter_minr// subrr mul0r.
  rewrite K1.
  rewrite mulr0 expR0 !mulr1.
  rewrite iter_addr addr0.
  rewrite /sumR big_map !big_nseq.
  rewrite K1 mulr0 expR0 iter_addr addr0.
  rewrite iter_minr.
    by rewrite -(mulr_natr p) -mulrA divff ?mulr1.
    done.
    lra.
rewrite /= H1.
have cardM : #|(fun j : 'I_M.+1 => j != i)| = M.
  have := card_ord M.+1.
  rewrite (cardD1 i) inE add1n => -[] hM.
  rewrite -[RHS]hM.
  apply: eq_card => x.
  rewrite inE; apply/idP/idP.
    by rewrite inE andbT.
  by move=> /andP[xi _].

have H2 : forall h, h > 0 ->
  stl_and_lt0 (seq_of_rV (const_mx p + h *: err_vec i)) =
  (M%:R  * p + (p (*+ h*)) * expR (h/p) * expR (nu * (h / p))) /
  (M%:R + expR (nu * (h / p))).
  move=> h h0.
  have mip :
      \big[minr/(p + h)%E]_(i <- seq_of_rV (const_mx p + h *: err_vec i)%R) i = p.
    rewrite big_map/= big_enum/= (bigminD1 i)//.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite big_const/=.
    rewrite iter_minr//; last 2 first.
      by rewrite cardM.
      by rewrite lerDl// ltW.
    by rewrite /minr ltNge lerDl (ltW h0)/=. 
  have mip' : \big[minr/p]_(i0 <- seq_of_rV (const_mx p + h *: err_vec i)%E) i0 = p.
    rewrite big_map/= big_enum/= (bigminD1 i)//.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite big_const/=.
    rewrite iter_minr//; last first.
      by rewrite cardM.
    by rewrite /minr ltNge lerDl (ltW h0).
  rewrite /stl_and_lt0/= {1}/sumR big_map.
  congr (_ / _).
    rewrite big_map/= big_enum/= (bigD1 i)//=.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (_ : min_dev _ _ = h / p); last first.
      rewrite /min_dev.
      rewrite mip.
      by rewrite -addrA addrCA subrr addr0.
      rewrite mip.
    rewrite (eq_bigr (fun=> p)); last first. 
      move=> j ji.
      rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
      rewrite (_ : min_dev _ _ = 0); last first.
        rewrite /min_dev.
        by rewrite mip' subrr mul0r.
      by rewrite mip' mulr0 expR0 !mulr1. 
    rewrite big_const/= iter_addr addr0 cardM.
    rewrite addrC.
    by rewrite (mulrC M%:R p) mulr_natr.
  rewrite /sumR !big_map/= -enumT big_enum/= (bigD1 i)//=.
  rewrite ffunE !mxE eqxx mulr1.
  rewrite (_ : min_dev _ _ = h / p); last first.
    rewrite /min_dev.
    rewrite mip.
    by rewrite -addrA addrCA subrr addr0.
  rewrite addrC; congr (_ + _).
  rewrite (eq_bigr (fun=> 1)).
    by rewrite big_const/= cardM iter_addr addr0.
  move=> j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
  rewrite (_ : min_dev _ _ = 0); last first.
    rewrite /min_dev.
    by rewrite mip' subrr mul0r.
  by rewrite mulr0 expR0.

have H3 h : h < 0 ->
  stl_and_lt0 (seq_of_rV (const_mx p + h *: err_vec i)) =
  (((p+h) * M%:R * expR (- h / (p + h)) * expR (nu * (- h / (p+h))) + p + h)/
  (M%:R * expR (nu * (- h / (p+h))) + 1)).
  move=> h0.
    have mip :
      \big[minr/(p + h)%E]_(i <- seq_of_rV (const_mx p + h *: err_vec i)%R) i = p + h.
    rewrite big_map/= big_enum/= (bigminD1 i)//.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    by rewrite big_const/= cardM iter_minr' ?minxx//gerDl ltW.
    have mip' : \big[minr/p]_(i0 <- seq_of_rV (const_mx p + h *: err_vec i)%E) i0 = p + h.
    rewrite big_map/= big_enum/= (bigminD1 i)//.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    by rewrite big_const/= cardM iter_minr'// /minr ifT// gtrDl.
    rewrite /stl_and_lt0/= /sumR/= !big_map -enumT !big_enum/= (bigD1 i)//=.
  congr (_ / _).
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (_ : min_dev _ _ = 0); last first.
      rewrite /min_dev.
      rewrite mip.
      lra.
    rewrite mulr0 expR0 !mulr1 addrC.
    rewrite (eq_bigr (fun=> (p + h) * expR (- h / (p + h)) * expR (nu * (- h / (p+h))))); last first.
      move=> j ji.
      rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
      rewrite (_ : min_dev _ _ = -h/(p+h)); last first.
        rewrite /min_dev.
        rewrite mip'. lra.
      rewrite mip'.
      done.
    rewrite big_const/= iter_addr addr0 cardM mip.
    by rewrite -[in LHS]mulr_natl !mulrA (mulrC (M%:R)) addrA.
  rewrite /= (bigD1 i)//=.
  rewrite ffunE !mxE eqxx mulr1.
  rewrite (_ : min_dev _ _ = 0); last first.
    rewrite /min_dev.
    rewrite mip.
    lra.
  rewrite (eq_bigr (fun=> (expR (nu * (- h / (p + h)%E))))); last first.
    move=> j ji.
    rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite (_ : min_dev _ _ = -h/(p+h)); last first.
      rewrite /min_dev.
      rewrite mip'. lra.
    done.
  rewrite big_const/= iter_addr addr0 cardM.
  by rewrite mulr0 expR0 addrC -[in LHS]mulr_natr mulrC.

have /cvg_lim : h^-1 * ((stl_and_lt0 (seq_of_rV (const_mx p + h *: err_vec i))) -
                        (stl_and_lt0 (seq_of_rV (const_mx p))))
       @[h --> (0:R)^'] --> (M.+1%:R^-1:R).
  apply/cvg_at_right_left_dnbhs.
    rewrite H1.
    apply/cvgrPdist_le => /= eps eps0.
    near=> x.
    rewrite [X in normr (_ - X)](_ : _ =
      (M%:R + expR (nu * (x / p)))^-1 *
      expR (nu * (x / p)) *
      ((expR (x / p) - 1) / (x / p))); last first.
      rewrite H2//.
      set a := expR (x / p).
      set b := expR (nu * (x / p)).
      rewrite invf_div !mulrA mulrC.
      congr (_ / _).
      rewrite -[X in _ - X](mulr1 p).
      rewrite -[X in _ - (_ * X)](@mulVf _ ((M%:R + b)%E)).

      rewrite mulrCA mulrC -mulrBr -!mulrA.
      congr (_ * _).
      rewrite -mulrC -mulrDr -mulrBr.
      nra.
      by rewrite gt_eqF// addr_gt0// ?ltr0n ?lt0n// expR_gt0.
    near: x.
  move: eps eps0.
  apply/cvgrPdist_le.
    rewrite -(mulr1 M.+1%:R^-1).
    rewrite -(mulr1 (M.+1%:R^-1 * 1)).
    apply: cvgM.
      apply: cvgM.
        apply: cvgV => //.
        rewrite -natr1.
        apply: cvgD => //.
          exact: cvg_cst.
        by under eq_fun do rewrite mulrCA mulrC; exact: exp0.
      by under eq_fun do rewrite mulrCA mulrC; exact: exp0.
    have L1 : forall x : R, x \in (ball 0 1 : set R^o) -> is_derive x 1 ( *%R^~ p^-1) p^-1.
      move=> x _.
      rewrite [X in is_derive _ _ X _](_ : _ = p^-1 *: id); last first.
        by apply/funext => y /=; rewrite mulrC.
      rewrite [X in is_derive _ _ _ X](_ : _ = p^-1 *: (1:R^o))//.
        exact: is_deriveZ.
      by rewrite /GRing.scale/= mulr1.
    apply: (@lhopital_right R (fun x => expR (x / p) - 1)
        (fun x => p^-1 * expR (x / p)) (fun x => x / p) (fun=> p^-1) 0 _
        (nbhsx_ballx _ _ ltr01)).
      move=> x xU.
      rewrite -[X in is_derive _ _ _ X]subr0.
      apply: is_deriveB => /=.
      rewrite mulrC.
      apply: is_derive1_comp.
      exact: L1.
      by rewrite mul0r expR0 subrr.
      by rewrite mul0r.
      by near=> t; rewrite gt_eqF// invr_gt0.
    under eq_fun.
      move=> x; rewrite mulrAC divff ?gt_eqF ?invr_gt0// mul1r.
      over.
    rewrite -expR0; apply: continuous_cvg; first exact: continuous_expR.
    rewrite -[X in _ --> X](mul0r p^-1).
    apply: cvgM; last exact: cvg_cst.
    exact/cvg_at_right_filter/cvg_id.
  rewrite H1.
  apply/cvgrPdist_le => /= eps eps0.
  near=> x.
  pose a x := expR (nu * - x / (p + x)%E).
  pose b x := expR (- x / (p + x)).
  pose num x := M%:R * (p + x) * b x - M%:R * p.
  pose den x := x * (M%:R + (a x)^-1).
  have ? : a x != 0 by rewrite ?gt_eqF ?expR_gt0.
  have ? : ((M%:R * a x)%R + 1%R)%E != 0 by rewrite gt_eqF// addr_gt0// mulr_gt0// ?expR_gt0// ltr0n// lt0n.
  rewrite [X in normr (_ - X)](_ : _ =
    (a x * (M%:R + (a x)^-1))^-1 + num x / den x); last first.
    rewrite /= H3// mulrA -/(b x) -/(a x).
    rewrite -[X in _ - X](mul1r p) -[X in _ - (X * p)](@mulfV _ (((M%:R * a x)%R + 1%R)))//.
    rewrite -(mulrAC _ p) -mulrBl (mulrDl _ _ p) mul1r opprD !addrA.
    rewrite [X in _ * (X / _)](_ : _ = (p + x) * M%:R * b x * a x + x - M%:R * a x * p); last first.
      by rewrite -!addrA !(addrC p) -!addrA (addrC (-p)) subrr addr0.
    rewrite (_ : _ / _ = (a x * ((p + x) * M%:R * b x + x * (a x)^-1 - M%:R * p) / (a x * (M%:R + (a x)^-1)))); last first.
      congr (_ / _); last by rewrite mulrDr mulfV// mulrC.
      rewrite !mulrDr (mulrC (a x) (_ / _)) -(mulrA x) (@mulVf _ (a x))// mulr1.
      by rewrite !mulrN {1}(mulrC (a x)) [in RHS](mulrC (a x)) -!mulrA (mulrC p).
    rewrite -addrAC mulrDr (mulrC (a x) (_ / _)) -(mulrA x) (@mulVf _ (a x))// mulr1.
    rewrite mulrA (mulrDr (x^-1)) mulrDl addrC.
    congr (_ + _).
      by rewrite mulVf// mul1r.
    rewrite !invrM'// (mulrC (a x)) !mulrA; congr(_/_).
    rewrite -mulrA mulfV// mulr1 mulrC; congr(_/_).
    by rewrite /num [in RHS](mulrC (M%:R)).
  near: x.
  move: eps eps0.
  apply/cvgrPdist_le.
  have ? : a x @[x --> nbhs 0^'-] --> (1:R).
    rewrite /a -expR0; apply: continuous_cvg; first apply: continuous_expR.
    rewrite -[X in _ --> X](mul0r p^-1).
    apply: cvgM; last first.
    apply: cvgV; first by rewrite gt_eqF.
      rewrite -{2}(addr0 p).
      apply: cvgD; first exact: cvg_cst.
      exact/cvg_at_left_filter/cvg_id.
    rewrite -{2}(mulr0 nu) -{2}oppr0.
    apply: cvgM; first exact: cvg_cst.
    apply: cvgN.
    exact/cvg_at_left_filter/cvg_id.
  rewrite -[X in _ --> X]addr0.
  apply: cvgD.
    apply: cvgV => //.
    rewrite -(mul1r (M.+1%:R)).
    apply: cvgM => //.
    rewrite -natr1.
    apply: cvgD; first exact: cvg_cst.
    rewrite -invr1 /a.
    exact: cvgV.
  rewrite /num/den/a/b.
  pose num' (x : R) : R := M%:R * expR (- x / (p + x)) +
                           expR (- x / (p + x)) * x * M%:R * (x / (x + p)^+2 - (x + p)^-1) +
                           expR (- x / (p + x)) * M%:R * p * (x / (x + p)^+2 - (x + p)^-1).
  pose den' (x : R) : R := expR (nu * (x / (x + p))) +
                           M%:R +
                           expR (nu * (x / (x + p))) * x * (- x * nu / (x + p)^+2 + nu / (x + p)).

  have Hint6 (x : R) : derivable -%R x 1.
    by apply: derivableN; exact: derivable_id.
  have px_neq0 (x : R) : x \in (ball 0 p : set R^o) -> (p + x)%R != 0.
    rewrite inE /ball/= sub0r normrN lter_norml => /andP[Npx xp].
    by rewrite gt_eqF// -ltrBlDl sub0r.
  have Hint3 (x : R) : derivable (+%R p) x 1.
    by apply: derivableD; [exact: derivable_cst|exact: derivable_id].
  have Hint4 (x : R) : x \in (ball 0 p : set R^o) ->
    derivable (fun x0 => (p + x0)%E^-1) x 1.
    by move=> x0p; apply: derivableV; [exact: px_neq0|exact: Hint3].
  have Hint5 (x : R) : x \in (ball 0 p : set R^o) ->
      derivable (fun x0 : R^o => - x0 / (p + x0)%E) x 1.
    move=> x0p; apply: derivableM; last exact: Hint4.
    by apply: derivableN; exact: derivable_id.
  have Hint2 (x : R) : x \in (ball 0 p : set R^o) ->
    derivable (fun x0 : R => expR (- x0 / (p + x0)%E)) x 1.
    move=> x0p.
    by apply: derivable_comp; [exact: derivable_expR|exact: Hint5].
  apply: (@lhopital_left R _ num' _ den' 0 _ (nbhsx_ballx _ _ p0)).
    move=> x x0p.
    rewrite /num'.
    rewrite -[X in is_derive _ _ _ X]subr0.
    apply: is_deriveB.
    move=> [:H1].
    apply: DeriveDef.
      apply: derivableM.
        abstract: H1.
        apply: derivableM; first exact: derivable_cst.
        apply: derivableD; first exact: derivable_cst.
        exact: derivable_id.
      exact: Hint2.
    rewrite deriveM; last 2 first.
      exact: H1.
      exact: Hint2.
    rewrite deriveM; last 2 first.
      exact: derivable_cst.
      exact: Hint3.
    rewrite derive_comp; last 2 first.
      exact: Hint5.
      exact: derivable_expR.
    rewrite (_ : 'D_1 expR (- x / (p + x)%E) = expR (- x / (p + x)%E)); last first.
      by rewrite -[in RHS](@derive_expR R).
    rewrite deriveD; last 2 first.
      exact: derivable_cst.
      exact: derivable_id.
    rewrite derive_cst add0r.
    rewrite derive_id.
    set tmp := GRing.scale (GRing.natmul (V:=R) (GRing.one R) M) (GRing.one R).
    rewrite (_ : tmp = M%:R)//; last first.
      rewrite /tmp.
      rewrite /GRing.scale/=.
      by rewrite mulr1.
    rewrite {tmp}.
    rewrite derive_cst scaler0 addr0.
    rewrite deriveM/=; last 2 first.
      exact: Hint6.
      exact: Hint4.
    rewrite deriveV; last 2 first.
      exact: px_neq0.
      exact: Hint3.
    rewrite deriveD; last 2 first.
      exact: derivable_cst.
      exact: derivable_id.
    rewrite derive_cst add0r.
    rewrite derive_id.
    set tmp := (X in - x *: X).
    rewrite (_ : tmp = (- (p + x)%E ^- 2))//; last first.
      rewrite /tmp.
      rewrite /GRing.scale/=.
      by rewrite mulr1.
    rewrite deriveN; last first.
      exact: derivable_id.
    rewrite derive_id.
    rewrite scalerN1.
    rewrite [X in X + _ = _]scalerAl.
    rewrite scalerCA.
    rewrite -[LHS]mulrDr.
    rewrite [X in _ = X + _ + _]mulrC.
    rewrite -!mulrA.
    rewrite -2!mulrDr.
    congr (_ * _).
    rewrite [in LHS]addrC.
    rewrite -!addrA; congr (_ + _).
    rewrite mulrCA -mulrDr.
    rewrite -[LHS]mulrA.
    congr (M%:R * _).
    rewrite -mulrDl (addrC p).
    congr (_ * _).
    congr (_ - _).
    rewrite scaleNr.
    rewrite -mulrN.
    by rewrite opprK.

    move=> x x0p.
    move=> [:H1].
    apply: DeriveDef.
      apply: derivableM.
        exact: derivable_id.
      apply: derivableD.
        exact: derivable_cst.
      apply: derivableV.
        by rewrite expR_eq0.
      abstract: H1.
      apply: derivable_comp.
        exact: derivable_expR.
      apply: derivableM.
        apply: derivableM.
          exact: derivable_cst.
        exact: Hint6.
      exact: Hint4.
    rewrite /den' deriveM; last 2 first.
      exact: derivable_id.
      apply: derivableD.
        exact: derivable_cst.
      apply: derivableV.
        by rewrite expR_eq0.
      exact: H1.
    rewrite deriveD; last 2 first.
      exact: derivable_cst.
      apply: derivableV.
        by rewrite expR_eq0.
      exact: H1.
    rewrite derive_cst add0r/=.
    rewrite deriveV/=; last 2 first.
      by rewrite expR_eq0.
      exact: H1.
    rewrite derive_comp; last 2 first.
      under eq_fun.
        move=> z.
        rewrite -mulrA.
        over.
      apply: derivableM.
        exact: derivable_cst.
      exact: Hint5.
      exact: derivable_expR.
    rewrite (_ : 'D_1 expR (nu * - x / (p + x)%E) = expR (nu * - x / (p + x)%E)); last first.
      by rewrite -[in RHS](@derive_expR R).
    rewrite deriveM; last 2 first.
      apply: derivableM.
        exact: derivable_cst.
      exact: Hint6.
      exact: Hint4.
    rewrite deriveV; last 2 first.
      exact: px_neq0.
      exact: Hint3.
    rewrite deriveM; last 2 first.
      exact: derivable_cst.
      exact: Hint6.
    rewrite derive_cst scaler0 addr0.
    rewrite deriveN; last first.
      exact: derivable_id.
    rewrite deriveD; last 2 first.
      exact: derivable_cst.
      exact: derivable_id.
    rewrite derive_id derive_cst add0r.
    rewrite scalerN1.
    rewrite [X in _ + X = _]/GRing.scale/= mulr1.
    rewrite addrCA.
    rewrite -[RHS]addrA [RHS]addrCA.
    congr (_ + _).
    rewrite [LHS]addrC.
    congr (_ + _).
      rewrite -expRN mulrN mulNr opprK (addrC p).
      by rewrite mulrA.
    rewrite -[RHS]mulrA.
    rewrite [RHS]mulrCA.
    congr (_ * _).
    rewrite [in LHS]scaleNr.
    rewrite [X in - X]mulrA.
    rewrite -[in LHS]mulrN.
    congr (_ * _).
      rewrite !(mulrN,mulNr) !expRN.
      rewrite -exprVn invrK expr2.
      rewrite -[LHS]mulrA divff ?mulr1//.
      rewrite (addrC p)//.
      by rewrite mulrA.
      by rewrite expR_eq0.
    rewrite !(mulrN,mulNr,scaleNr,scalerN,opprK) opprB.
    rewrite [RHS]addrC; congr (_ - _).
      by rewrite [LHS]mulrC (addrC p).
    rewrite (mulrC nu) scalerA (addrC p).
    by rewrite /GRing.scale/= mulr1.
    by rewrite oppr0 mul0r expR0 mulr1 addr0 subrr.
    by rewrite mul0r.
    near=> x.
      rewrite /den'.
      admit.
    rewrite -{2}(mul0r ((den' 0)^-1)).
    apply: cvgM; last first.
      apply: cvgV.
        by rewrite /den' !mul0r !mulr0 !mul0r addr0 gt_eqF// addr_gt0// ?expR_gt0 ?ltr0n ?lt0n.
      apply: continuous_cvg. admit.
      exact/cvg_at_left_filter/cvg_id.
    rewrite /num'.
    pose c x := expR (nu * (x / (x + p)%E)).
    under eq_fun=> x.
      rewrite -/(b x) -/(c x).
      over.
    apply/cvgrPdist_le => eps eps0.
    near=> x.
    admit.
rewrite H1.
apply. exact: Rhausdorff.
Unshelve. all: end_near.
Admitted.

End shadow_lifting_stl_and.
