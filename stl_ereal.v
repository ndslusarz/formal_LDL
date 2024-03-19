From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra ldl.

(**md**************************************************************************)
(* # STL                                                                      *)
(*                                                                            *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Section stl_lemmas.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (nu : R).
Hypothesis nu0 : 0 < nu.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.

Lemma andI_stl (e : expr Bool_N) :
  nu.-[[e `/\ e]]_stle = nu.-[[e]]_stle.
Proof.
rewrite /=/sumE !big_cons !big_nil/=.
have [->//|epoo] := eqVneq (nu.-[[e]]_stle) (+oo)%E.
have [->//=|enoo] := eqVneq (nu.-[[e]]_stle) (-oo)%E.
rewrite /mine_dev.
set a_min := mine (nu.-[[e]]_stle) (mine (nu.-[[e]]_stle) +oo)%E.
set a := ((nu.-[[e]]_stle - a_min) * ((fine a_min)^-1)%:E)%E.
have a_min_e : a_min = nu.-[[e]]_stle.
  by rewrite /a_min /mine; repeat case: ifPn => //; rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0%E.
  by rewrite /a a_min_e subee ?mul0e// fin_numE epoo enoo.
rewrite !adde0 !mule0 expeR0 !mule1/= a_min_e.
have : ((nu.-[[e]]_stle + nu.-[[e]]_stle) * ((1 + 1)^-1)%:E)%E = nu.-[[e]]_stle.
  have -> : 1 + 1 = (2 : R) by lra.
  rewrite -(@fineK _ (nu.-[[e]]_stle)); last by rewrite fin_numE epoo enoo.
  by rewrite -EFinD -EFinM mulrDl -splitr.
case: ifPn => [/eqP h|_ ->]; first by rewrite !h.
case: ifPn => [/eqP ->//|?].
case: ifPn => //; rewrite -leNgt => ege0.
case: ifPn => //; rewrite -leNgt => ele0.
by apply le_anti_ereal; apply/andP; split.
Qed.

Lemma andC_stl (e1 e2 : expr Bool_N) :
  nu.-[[e1 `/\ e2]]_stle = nu.-[[e2 `/\ e1]]_stle.
Proof.
rewrite /=/sumE !big_cons !big_nil /=.
set a_min := mine (nu.-[[e1]]_stle) (mine (nu.-[[e2]]_stle) +oo)%E.
have -> : (mine (nu.-[[e2]]_stle) (mine (nu.-[[e1]]_stle) +oo))%E = a_min.
  by rewrite mineA [X in mine X _]mineC -mineA.
set a1 := ((nu.-[[e1]]_stle - a_min) * ((fine a_min)^-1)%:E)%E.
set a2 := ((nu.-[[e2]]_stle - a_min) * ((fine a_min)^-1)%:E)%E.
set d1 := ((fine (expeR (nu%:E * a1) + (expeR (nu%:E * a2) + 0)))^-1)%:E.
have -> : ((fine (expeR (nu%:E * a2) + (expeR (nu%:E * a1) + 0)))^-1)%:E = d1.
  by rewrite addeCA.
case: ifPn => //.
case: ifPn => //.
case: ifPn => _; first by rewrite addeCA.
by case: ifPn => _; first rewrite addeCA.
Qed.

Lemma orI_stl (e : expr Bool_N) :
  nu.-[[e `\/ e]]_stle = nu.-[[e]]_stle.
Proof.
rewrite /=/sumE !big_cons !big_nil/=.
rewrite /maxe_dev.
have [->//|enoo] := eqVneq (nu.-[[e]]_stle) (-oo)%E.
have [->//=|epoo] := eqVneq (nu.-[[e]]_stle) (+oo)%E.
set a_max := maxe (nu.-[[e]]_stle) (maxe (nu.-[[e]]_stle) -oo)%E.
set a := (((a_max - nu.-[[e]]_stle) * ((fine a_max)^-1)%:E))%E.
have a_max_e : a_max = nu.-[[e]]_stle.
  by rewrite /a_max /maxe; repeat case: ifPn; rewrite ltNge leNye.
have -> : a = 0%E.
  by rewrite /a a_max_e subee ?mul0e// fin_numE epoo enoo.
rewrite !adde0 !mule0 expeR0 !mule1/= a_max_e.
have -> : ((nu.-[[e]]_stle + nu.-[[e]]_stle) * ((1 + 1)^-1)%:E)%E = nu.-[[e]]_stle.
  have -> : 1 + 1 = (2 : R) by lra.
  rewrite -(@fineK _ (nu.-[[e]]_stle)); last by rewrite fin_numE epoo enoo.
  by rewrite -EFinD -EFinM mulrDl -splitr.
case: ifPn => [/eqP->//|?].
case: ifPn => [/eqP->//|?].
case: ifPn => [//|]; rewrite -leNgt => ege0.
case: ifPn => [//|]; rewrite -leNgt => ele0.
by apply/eqP; rewrite eq_le ege0 ele0.
Qed.

Lemma orC_stl (e1 e2 : expr Bool_N) :
  nu.-[[e1 `\/ e2]]_stle  = nu.-[[e2 `\/ e1]]_stle.
Proof.
rewrite /=/sumE !big_cons !big_nil /=.
set a_max := maxe (nu.-[[e1]]_stle) (maxe (nu.-[[e2]]_stle) -oo)%E.
have -> : (maxe (nu.-[[e2]]_stle) (maxe (nu.-[[e1]]_stle) -oo))%E = a_max.
  by rewrite maxA [X in maxe X _]maxC -maxA.
set a1 := ((a_max - nu.-[[e1]]_stle) * ((fine a_max)^-1)%:E)%E.
set a2 := (((a_max - nu.-[[e2]]_stle) * ((fine a_max)^-1)%:E))%E.
set d1 := ((fine (expeR (nu%:E * a1) + (expeR (nu%:E * a2) + 0)))^-1)%:E.
have -> : ((fine (expeR (nu%:E * a2) + (expeR (nu%:E * a1) + 0)))^-1)%:E = d1.
  by rewrite addeCA.
case: ifPn => // ?.
case: ifPn => // ?.
case: ifPn => [|?].
  by rewrite addeCA.
case: ifPn => // ?.
by rewrite addeCA.
Qed.

Lemma stl_ereal_translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  nu.-[[ e ]]_stle = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ _ e2 erefl JMeq_refl).
Qed.

Lemma stl_ereal_translations_Index_coincide: forall n (e : expr (Index_T n)),
  nu.-[[ e ]]_stle = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma stl_ereal_translations_Real_coincide (e : expr Real_T):
  nu.-[[ e ]]_stle = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite stl_ereal_translations_Vector_coincide stl_ereal_translations_Index_coincide.
Qed.

Definition is_stl b (x : \bar R) := (if b then x >= 0 else x < 0)%E.

Lemma stl_nary_inversion_andE1 (Es : seq (expr Bool_P) ) :
  is_stl true (nu.-[[ ldl_and Es ]]_stle) -> (forall i, (i < size Es)%N -> is_stl true (nu.-[[ nth (ldl_bool pos false) Es i ]]_stle)).
Proof.
rewrite/is_stl/= big_map.
case: ifPn => [//|hnoo].
case: ifPn => [/eqP min_apoo _|hpoo].
  move=> i isize.
  move: ((mine_eqyP _ _ _).1 min_apoo (nth (ldl_bool pos false) Es i)).
  by rewrite mem_nth// => ->.
case: ifPn=>[hminlt0|].
  rewrite/sumE.
  rewrite leNgt !big_map.
  rewrite mule_lt0_gt0//; last first.
    rewrite lte_fin invr_gt0 fine_gt0//.
    apply/andP;split.
      rewrite big_seq_cond sume_gt0//.
      move=> i /andP[iEs _]; apply: expeR_ge0.
      have := hminlt0; rewrite big_seq_cond.
      move/mine_lt => [i[iEs[_ hilt0]]].
      exists i; split; first exact: iEs.
      rewrite expeR_gt0 ?iEs//.
      rewrite ltNye !mule_eq_ninfty.
      rewrite !lte_fin !nu0/=.
      rewrite !negb_or !negb_and -!leNgt/= andbT !orbT/= (ltW nu0)/= -!big_seq_cond.
      rewrite andbT invr_le0 invr_ge0 fine_le0 ?orbT ?(ltW hminlt0)//=.
      rewrite -ltey lte_add_pinfty//.
        by apply: lt_trans; first exact: hilt0.
      by rewrite lte_oppl/= ltNye.
    rewrite big_seq_cond.
    apply: lte_sum_pinfty => i /andP[iEs _].
    apply: expeR_lty.
    rewrite ltey !mule_eq_pinfty/= !negb_or !negb_and !negb_or !negb_and.
    rewrite -!leNgt !lee_fin !(ltW nu0)/= !orbT !andbT/=.
    rewrite invr_le0 fine_le0 ?(ltW hminlt0)// orbT/=.
    rewrite adde_eq_ninfty negb_or; apply/orP; right.
    apply/orP; left; apply/andP; split.
    rewrite gt_eqF//.
    have := hnoo; rewrite -ltNye.
    move/mine_gt; apply => //.
    by rewrite eqe_oppLR/=.
  apply sume_lt0.
    move=> i _.
    rewrite !mule_le0_ge0//; last 2 first.
      by apply expeR_ge0.
      by apply expeR_ge0.
    exact: ltW.
  have := hminlt0.
  rewrite {1}big_seq_cond.
  move/mine_lt => [i [iEs [_ hilt0]]].
  exists i; split => //.
  rewrite mule_lt0_gt0//; last first.
    rewrite expeR_gt0// ltNye !mule_eq_ninfty/= !negb_or !negb_and !negb_or !negb_and.
    rewrite -!leNgt !lee_fin/= (ltW nu0)/= !andbT !orbT/=.
    rewrite invr_le0 fine_le0 ?(ltW hminlt0)// orbT/=.
    rewrite adde_Neq_pinfty; last by rewrite eqe_oppLR/=.
      rewrite eqe_oppLR/= hnoo andbT.
      by rewrite -ltey (lt_trans hilt0)//= orbT.
    rewrite -ltNye.
    move: hnoo; rewrite -ltNye.
    by move/mine_gt; apply.
  rewrite mule_lt0 hminlt0/= {1}lt_eqF//= {1}gt_eqF//=.
    by rewrite -leNgt expeR_ge0.
  rewrite expeR_gt0// ltNye mule_eq_ninfty !negb_or !negb_and -!leNgt.
  rewrite -!ltNye -!ltey !ltNyr !orbT/=.
  rewrite lee_fin invr_le0 fine_le0 ?(ltW hminlt0)// orbT/=.
  rewrite ltey adde_Neq_pinfty ?eqe_oppLR/= ?hpoo ?hnoo//.
    by rewrite -ltey (lt_trans hilt0).
  rewrite -ltNye.
  move: hnoo; rewrite -ltNye.
  by move/mine_gt; apply.
rewrite -leNgt => hminge0.
case: ifPn => [hmingt0 _ i isize|].
  have := hminge0.
  by move/mine_geP; apply => //; rewrite mem_nth.
rewrite -leNgt => hminle0 _ i isize.
have := hminge0.
rewrite big_seq_cond.
by move/mine_geP; apply; rewrite mem_nth.
Qed.

Lemma stl_nary_inversion_andE0 (Es : seq (expr Bool_P) ) :
  is_stl false (nu.-[[ ldl_and Es ]]_stle) -> (exists (i : nat), is_stl false (nu.-[[ nth (ldl_bool pos false) Es i ]]_stle)%E && (i < size Es)%nat).
Proof.
rewrite/is_stl/= !big_map.
have h0 : (-oo != +oo)%E by [].
case: ifPn => [/eqP|hnoo].
  rewrite big_seq_cond.
  move/(mine_eq (h0 _)) => [x [xEs [_ hxnoo]]].
  move: xEs.
  exists (index x Es).
  by rewrite nth_index// hxnoo ltNy0/= index_mem.
case: ifPn => [/eqP|hpoo].
  by rewrite lt_neqAle leye_eq => _ /andP[_ /eqP].
case: ifPn => [|].
  rewrite {1}big_seq_cond.
  move/mine_lt => [x [xEs [_ xlt0]]].
  exists (index x Es).
  by rewrite nth_index// xlt0 index_mem.
rewrite -leNgt => hge0.
case: ifPn => [hgt0|].
  apply: contraPP.
  move/forallNP => h.
  have {}h : forall i : nat,
      (i < size Es)%N ->
      (0 <= nu.-[[nth (ldl_bool pos false) Es i]]_stle)%E.
    move=> i iEs.
    move: (h i) => /negP.
    by rewrite negb_and -leNgt iEs/= orbF.
  apply/negP; rewrite -leNgt mule_ge0//.
    rewrite /sumE !big_map big_seq_cond sume_ge0// => x /andP[xEs _].
    rewrite mule_ge0//.
      move: (h (index x Es)).
      by rewrite index_mem xEs nth_index//; apply.
    exact: expeR_ge0.
  rewrite lee_fin invr_ge0 fine_ge0// /sumE !big_map sume_ge0// => x _.
  exact: expeR_ge0.
by rewrite lt_irreflexive.
Qed.

Lemma leye_eq' :
  forall (x : \bar R), (x <= -oo)%E = (x == -oo%E).
Proof.
Admitted.

Lemma maxe_eq_inf (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) :
  (\big[maxe/-oo]_(i <- r | P i) f i = +oo)%E
  -> exists i, i \in r /\ P i /\ (f i = +oo)%E.
Admitted.

Lemma maxe_eq_inf' (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) :
  (\big[maxe/-oo]_(i <- r | P i) f i = -oo)%E
  -> forall i, i \in r /\ P i /\ (f i = -oo)%E.
Admitted.

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
  case: ifP => [h1 h2| h3].
    exists a. rewrite mem_head Pa. 
    split. done. split. done. (* h2.
  move/(IH xltpoo) => [b[bl [Pb fb]]].
  by exists b; rewrite in_cons bl orbT.
move/(IH xltpoo) => [b[bl [Pb fb]]].
by exists b; rewrite in_cons bl orbT. *)
Admitted.

Lemma maxe_ge (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  (x <= \big[maxe/+oo]_(i <- s | P i) f i  <-> exists i, i \in s -> P i -> x <= f i)%E.
Proof.
elim: s.
  rewrite big_nil; split; first rewrite leey. 
Admitted.

Lemma maxe_lt (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  (\big[maxe/-oo]_(i <- s | P i) f i < x <-> forall i, i \in s -> P i -> f i < x)%E.
Proof.

Admitted.

Lemma maxe_gt (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  (x < \big[maxe/-oo]_(i <- r | P i) f i)%E
  <-> exists i, i \in r /\ P i /\ (x < f i)%E.
Proof.
Admitted.

Lemma maxe_ge' (I : eqType) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  (x <= \big[maxe/-oo]_(i <- r | P i) f i)%E
  <-> exists i, i \in r /\ P i /\ (x <= f i)%E.
Proof.
Admitted.

Lemma maxe_neq_infty (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  (\big[maxe/-oo]_(i <- s | P i) f i != +oo <-> forall i, i \in s -> P i -> f i != +oo)%E.
Admitted.

Lemma maxe_neq_infty' (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  (\big[maxe/-oo]_(i <- s | P i) f i != -oo <-> forall i, i \in s -> P i -> f i != -oo)%E.
Admitted.


Lemma nglt (x y : \bar R) :
(x <= y)%E = ~~ (y < x)%E.
Proof.
Admitted.

Lemma mule_neq_ninfty (x y : \bar R) : (x * y != -oo)%E = ((x != -oo)%E && (y != -oo)%E).
Admitted.

Lemma maxe_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (\big[maxe/-oo]_(i <- s | P i) f i = -oo <-> forall i, i \in s -> P i -> f i = -oo)%E.
Admitted.

Lemma stl_nary_inversion_orE1 (Es : seq (expr Bool_P) ) :
  is_stl true (nu.-[[ ldl_or Es ]]_stle) -> (exists i, is_stl true (nu.-[[ nth (ldl_bool _ false) Es i ]]_stle) && (i < size Es)%nat).
Proof.

rewrite/is_stl/= !big_map.
have h0 : (-oo != +oo)%E by [].
case: ifPn => [/eqP|hnoo].
  rewrite big_seq_cond. move => _.
  rewrite leye_eq' //=.
case: ifPn => [/eqP|hpoo].
rewrite big_seq_cond. 
  move/maxe_eq_inf => [x [xEs [_ xlt0]]].
  exists (index x Es). 
  by rewrite nth_index//  xlt0 H/= index_mem. 
case: ifPn => [|]. 
  rewrite maxe_gt => [ [x [xs [_ h]]] _].
  exists (index x Es).
  by rewrite nth_index// ltW// ?h/= index_mem. 
(*   About ltW. *)
rewrite -leNgt => hge0.
(* case: ifPn => [hgt0|]. *)
(*   apply: contraPP. *)
(*   move/forallNP => h. *)
(*   have {}h : forall i : nat, *)
(*       (i < size Es)%N -> *)
(*       (nu.-[[nth (ldl_bool pos false) Es i]]_stle < 0)%E. *)
(*     move=> i iEs. *)
(*     move: (h i) => /negP. *)
(*     by rewrite negb_and leNgt iEs/= orbF Bool.negb_involutive.  *)
(*   apply/negP; rewrite leNgt Bool.negb_involutive//. (* mule_ge0//. *) *)
(*     rewrite /sumE !big_map big_seq_cond.  *)
(*     rewrite mule_lt0/=. *)
(*     rewrite neq_lt. *)
(*     rewrite sume_lt0/=; last 2 first. *)
(*       move => i. rewrite andbT. move => iEs. *)
(*       have hilt0 : (nu.-[[i]]_stle < 0)%E. *)
(*         apply: (le_lt_trans _ hgt0). *)
(*         apply/maxe_ge'. *)
(*         by exists i; rewrite iEs le_refl. *)
(*       rewrite ltW// mule_lt0. *)
(*       rewrite expeR_eq0. rewrite mule_neq_ninfty. *)
(*       rewrite /maxe_dev mule_neq_ninfty. *)
(*       rewrite adde_Neq_ninfty ?hnoo ?hpoo//. *)
(*       rewrite lt_eqF//=. *)
(*       rewrite -oppeey oppeK lt_eqF/=; last exact: (lt_trans hilt0). *)
(*       by rewrite hilt0/= -leNgt expeR_ge0. *)
(*       rewrite hpoo//. *)
(*       rewrite oppeey. *)
(*       move/maxe_neq_infty : hpoo . *)
(*       admit. (*new lemma I think*) *)
(*       admit. *)
(*       rewrite invr_neq0; last first. About fine_lt. *)
(*       rewrite gt_eqF// fine_gt0// sume_gt0/=. *)
(*       rewrite lte_sum_pinfty//. *)
(*       move => i _. rewrite expeR_lty//. *)
(*       rewrite lte_mul_pinfty//.  *)
(*         admit. (*use nu0*) *)
(*         rewrite /maxe_dev lte_mul_pinfty//. *)
(*           (*any way to separate the constant inside the maxe? *)
(*           probably need to backtrack somwehre... or create a bunch of new lemmas*) *)
(*           admit. *)
(*           rewrite fin_numE. (*bigmaxe_fin_num*) *)
(*           admit. *)
(*           admit. *)
(*         move => i _. by rewrite expeR_ge0. *)
(*         (* have: maxe_lt. *) *)
(*         admit. *)
(*     rewrite /= -leNgt lee_fin invr_ge0 fine_ge0//. *)
(*     rewrite /= sume_ge0//. move => t _.  *)
(*     by rewrite  expeR_ge0.  *)
(*  rewrite -nglt//=.  *)
case: ifPn => [hlt0|].
  rewrite leNgt mule_lt0.
  rewrite /sumE !big_map !big_seq !negb_and negb_add.
  rewrite lte_fin invr_lt0 (ltNge _ 0%R) fine_ge0//=; last first.
    by rewrite sume_ge0// => t _; rewrite expeR_ge0.
  have /maxe_lt/= h := hlt0.
  rewrite sume_lt0/=; last 2 first.
  - by move=> i iEs; rewrite nmule_rle0 ?expeR_ge0// h//.
  - move: hlt0 => /maxe_lt.
    have := hnoo; rewrite eq_sym -ltNye => /maxe_gt [i [iEs [_ igtNye] ] ].
    move/(_ i iEs) => h1.
    exists i. rewrite iEs mule_lt0 lt_eqF ?h1//= -leNgt expeR_ge0//.
    rewrite gt_eqF// expeR_gt0//.
    rewrite ltNye mule_neq_ninfty.
    rewrite gt_eqF ?ltNyr//= /maxe_dev mule_neq_ninfty.
    rewrite gt_eqF//= ltNye adde_Neq_ninfty.
    - rewrite -big_seq hnoo -oppeey oppeK lt_eqF//=.
      exact: (lt_trans (h1 _)).
    - by rewrite -big_seq hpoo.
    by rewrite oppeey gt_eqF.
  rewrite lt_eqF/= ?gt_eqF//=.
    rewrite lte_fin invr_gt0 fine_gt0// sume_gt0/=; last 2 first.
    - by move=> i _; rewrite expeR_ge0.
    - admit.
    rewrite lte_sum_pinfty// => i iEs.
    rewrite expeR_lty// lte_mul_pinfty// ?ltW//.
    rewrite /maxe_dev lte_mul_pinfty//.
    - rewrite -big_seq sube_ge0 ?maxe_ge'; first by exists i; rewrite iEs le_refl.
    - by rewrite !fin_numE hnoo hpoo/= orbT.
    - rewrite fin_numE adde_Neq_pinfty.
      + admit.
      + by rewrite -big_seq//.
      rewrite -oppeey oppeK lt_eqF//=.
      apply: (le_lt_trans (le_trans _ hge0) _) => //.
      by rewrite maxe_ge'; exists i; rewrite iEs le_refl.
    exact: ltry.
  rewrite sume_lt0//=.
    by move=> i iEs; rewrite nmule_rle0 ?expeR_ge0// h.
  admit.
rewrite -nglt//=.
move/maxe_ge' => [x [xs [_ h]]] _.
exists (index x Es). Search (_ = +oo).
by rewrite nth_index// h /= index_mem xs.
Admitted.

Lemma stl_nary_inversion_orE0 (Es : seq (expr Bool_P) ) :
    is_stl false (nu.-[[ ldl_or Es ]]_stle) -> (forall i, (i < size Es)%nat -> is_stl false (nu.-[[ nth (ldl_bool pos false) Es i ]]_stle)).
Proof.
rewrite/is_stl/= big_map.

case: ifPn.
  move => /eqP h _ i i0/=.
  apply: (@le_lt_trans _ _ (\big[maxe/-oo%E]_(j <- Es) nu.-[[j]]_stle)).
  
  (* simple needs lemma max = -oo -> all elemtns -oo*)
  admit.
  rewrite h//.
case: ifPn.
  move => h1 h2.  admit. (*contra, +oo <0*)
  case: ifPn.
  rewrite maxe_gt => [ [x [xs [_ h]]] hmaxinf].
    move => hmaxninf'.
    rewrite/sumE !big_map.
    rewrite mule_lt0//.
    rewrite /= {1}lt_eqF//=.
      rewrite {1}gt_eqF//=.
        admit. 
          rewrite lte_fin invr_gt0 fine_gt0//. 
          rewrite sume_gt0.
            rewrite andTb.
            admit.
            move => i _. by rewrite expeR_ge0.
            exists x. rewrite xs//=. split.
              done. split. done. rewrite expeR_gt0//.
            admit. rewrite sume_lt0. done.
              move => i _. 
              admit.
        exists x. rewrite xs; split => //; split => //.
          rewrite mule_lt0_gt0//; last first.
          rewrite expeR_gt0// ltNye !mule_eq_ninfty/= !negb_or !negb_and !negb_or !negb_and.
          rewrite -!leNgt !lee_fin/= (ltW nu0)/= !andbT !orbT/=.
          rewrite invr_ge0 fine_ge0. rewrite !orbT/=. 
          rewrite adde_Neq_ninfty. rewrite hmaxninf'.
          move: hmaxninf'. move/maxe_neq_infty' => h1. 
          (* rewrite h1. *)
          admit. (*easy, use hilt0*)
          rewrite hmaxinf//.
          admit.
          admit.
          rewrite mule_lt0.
          admit. 
  rewrite -nglt. move => h1 h2 h3.
  case: ifPn.
     move => h4.
      rewrite /sumE !big_map.
    move => hlt0 i i0.
    move: h4. rewrite maxe_lt. 
      admit.
    rewrite -leNgt//=.
    rewrite lte_fin; lra.  
Admitted.

Lemma stl_soundness (e : expr Bool_P) b :
  is_stl b (nu.-[[ e ]]_stle) -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind'.
- move: b b0 => [] [] //=.
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
  move: b => [].
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
  + by case: b; rewrite /is_stl/= ?lee_fin ?lte_fin ?ltNge subr_ge0 !stl_ereal_translations_Real_coincide// => /negbTE.
  + case: b; rewrite /is_stl/= ?lee_fin ?lte_fin !stl_ereal_translations_Real_coincide.
    by rewrite oppr_ge0 normr_le0 subr_eq0.
    by rewrite oppr_lt0 normr_gt0 subr_eq0 => /negbTE.
Qed.


End stl_lemmas.

(* Ale: disabled for now
Section shadow_lifting_stl_and.
Context {R : realType}.
Variable nu : R.
Variable M : nat.
Hypothesis M0 : M != 0%N.
(*add hypothesis nu>0 if needed*)

(* The ones below do not type check yet, need to check if we can extend to ereal *)

Definition min_dev {R : numDomainType} (x : \bar R) (xs : seq \bar R) : \bar R :=
  (x - minE xs) * (fine (minE xs))^-1%:E.

Definition min_devR {R : realType} (x : R) (xs : seq R) : R :=
  (x - minR xs) * (minR xs)^-1.

Local Open Scope ereal_scope.

(*Natalia: will only consider >0 and <0 without edge cases, as to separate cases*)
(* Definition stl_and (xs : seq \bar R) : \bar R :=
  if minE xs == +oo then +oo
  else if minE xs == -oo then -oo (*Check if needed*)
  else if minE xs < 0 then
    sumE (map (fun a => minE xs * expeR (min_dev a xs) * expeR (nu%:E * min_dev a xs)) xs) *
    (fine (sumE (map (fun a => expeR (nu%:E * min_dev a xs)) xs)))^-1%:E
  else if minE xs > 0 then
    sumE (map (fun a => a * expeR (-nu%:E * min_dev a xs)) xs) *
    (fine (sumE (map (fun a => expeR (nu%:E * min_dev a xs)) xs)))^-1%:E
    else 0. *)

(*to do: change map to big operator probably*)

Local Close Scope ereal_scope.

Definition stl_and_gt0 n (v : 'rV[R]_n)  :=
  sumR (map (fun a => a * expR (-nu * min_devR a ( MatrixFormula.seq_of_rV v))) ( MatrixFormula.seq_of_rV v)) *
  (sumR (map (fun a => expR (nu * min_devR a ( MatrixFormula.seq_of_rV v))) ( MatrixFormula.seq_of_rV v)))^-1.

Definition stl_and_lt0 n (v : 'rV[R]_n) :=
  sumR (map (fun a => a * expR (-nu * min_devR a ( MatrixFormula.seq_of_rV v))) ( MatrixFormula.seq_of_rV v)) *
    (sumR (map (fun a => expR (nu * min_devR a ( MatrixFormula.seq_of_rV v))) ( MatrixFormula.seq_of_rV v)))^-1.


 Search (_ `^ _).
Lemma shadowlifting_stl_and_gt0 (p : R) : p > 0 ->
  forall i, ('d (@stl_and_gt0 M.+1) '/d i) (const_mx p) = (M%:R) ^ -1.
Proof.
move=> p0 i.
rewrite /partial.
(* have /cvg_lim : h^-1 * (stl_and_gt0 (const_mx p + h *: err_vec i) -
                        stl_and_gt0 (n:=M.+1) (const_mx p))
       @[h --> (0:R)^'] --> ((M%:R)^ -1):R. *)


Admitted.


End shadow_lifting_stl_and.
*)
