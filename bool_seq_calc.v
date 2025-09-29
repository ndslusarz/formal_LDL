From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder finmap multiset.
Require Import mathcomp_extra analysis_extra dl fuzzy.

(**md**************************************************************************)
(* # Classical sequent calculus                                               *)
(*   seq_calc_bool_ms - sequent calc for standard boolean logic               *)
(*                      using multisets                                       *)
(*   sound_sc_bool_mseq - soundness proof                                     *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Reserved Notation "{[ e ]}" (format "{[  e  ]}").

HB.instance Definition _ (R : realType) x y z v :=
  @gen_choiceMixin (@expr R (boolT x y z v)).

Reserved Notation "Q |= P" (no associativity, at level 61).
Reserved Notation "Q |- P" (no associativity, at level 61).

Section seq_calc_bool.
Local Open Scope ring_scope.
Local Open Scope dl_scope.
Local Open Scope mset_scope.
Context {R : realType} {K : choiceType}.
Implicit Types (A : {mset K}) (s : seq K).
Local Notation "<< e >>" := (@bool_translation R _ e).

Inductive seq_calc_bool_ms : {mset (@expr R (boolT_def impl_def m_undef l_def))}
  -> {mset (@expr R (boolT_def impl_def m_undef l_def))} -> Prop :=
| init : forall (Q P : {mset (@expr R (boolT_def impl_def m_undef l_def))}) (a : @expr R (boolT_def impl_def m_undef l_def)),
     a +` Q |= a +` P
| bot : forall (Q P : {mset (@expr R (boolT_def impl_def m_undef l_def))}),
    (dl_bool neg_def _ _ _ false) +` Q |= P
| top : forall (Q P : {mset (@expr R (boolT_def impl_def m_undef l_def))}),
    Q |= (dl_bool neg_def _ _ _ true) +` P
| and_R : forall (Q P : {mset (@expr R (boolT_def impl_def m_undef l_def))}) (a : @expr R (boolT_def impl_def m_undef l_def))
                 (b : (@expr R (boolT_def impl_def m_undef l_def))),
    Q |= a +` P  ->  Q |= ( b) +` P ->
      Q |=  (a `/\ b) +` P
| andL1 :  forall (Q P : {mset (@expr R (boolT_def impl_def m_undef l_def))}) (a b : @expr R (boolT_def impl_def m_undef l_def)),
    a +` Q  |= P ->
      (a `/\ b) +` Q |= P
| andL2 :  forall (Q P : {mset (@expr R (boolT_def impl_def m_undef l_def))}) (a b : @expr R (boolT_def impl_def m_undef l_def)),
    b +` Q  |= P ->
      (a `/\ b) +` Q |= P
| orR1 : forall (Q P : {mset (@expr R (boolT_def impl_def m_undef l_def))})
                (a : @expr R (boolT_def impl_def m_undef l_def))
                 (b : (@expr R (boolT_def impl_def m_undef l_def))),
    Q |=  a +` P ->
      Q |=  (a `\/ b) +` P
| orR2 : forall (Q P : {mset (@expr R (boolT_def impl_def m_undef l_def))})
                (a : @expr R (boolT_def impl_def m_undef l_def))
                 (b : (@expr R (boolT_def impl_def m_undef l_def))),
    Q |=  b +` P ->
      Q |=  (a `\/ b) +` P
| orL :  forall (Q P : {mset (@expr R (boolT_def impl_def m_undef l_def))})
                (a : @expr R (boolT_def impl_def m_undef l_def))
                 (b : (@expr R (boolT_def impl_def m_undef l_def))),
    a+`Q  |= P ->  b +` Q |= P ->
      (a `\/ b)+`Q |= P
| negL : forall Q P a,
    Q |= a +` P ->
      (`~ a)+`Q|= P
where "Q |= P" := (seq_calc_bool_ms Q P).


Lemma sound_sc_bool_mseq (Q P : {mset expr (boolT_def impl_def m_undef l_def)}) :
  Q |= P ->
  (forall q : expr (boolT_def impl_def m_undef l_def),
    q \in Q -> <<q>> = <<dl_bool neg_def _ _ _ true>>) ->
  exists p : expr (boolT_def impl_def m_undef l_def),
    (p \in P) /\ <<p>> = <<dl_bool neg_def _ _ _ true>>.
Proof.
 rewrite //=. intros. dependent induction H.
- exists a. have H := H0 a.
  rewrite in_mset1D eqxx orTb ?andTb.
  move: H; rewrite in_mset1D eqxx orTb ?andTb//=.
  by auto.
- exfalso.  move: H0.
  rewrite//=. apply contrapT. rewrite  not_implyE.
  rewrite not_andE notE. left.
  rewrite -existsNP.
  exists (dl_bool neg_def _ _ _ false).
  rewrite in_mset1D eqxx orTb//=.
  by auto.
- exists (dl_bool neg_def _ _ _ true).
  by rewrite in_mset1D eqxx.
- destruct (IHseq_calc_bool_ms1 H1) as [x [IH11 IH12]].
  destruct (IHseq_calc_bool_ms2 H1) as [y [IH21 IH22]].
  rewrite in_mset1D in IH11. move/predU1P: IH11 => [H2|H2].
    + subst.
      rewrite in_mset1D in IH21. move/predU1P: IH21 => [|] H2.
      * subst.
        exists (a `/\ b).
        simpl; split; eauto.
        - by rewrite in_mset1D eqxx orTb.
        - rewrite !big_ord_recl big_ord0 !tnthS !tnth0.
          by rewrite IH12 IH22.
      * by exists y; rewrite IH22 in_mset1D H2 orbT.
    + by exists x; rewrite IH12 in_mset1D H2 orbT.
- have := H0 (a `/\ b).
  rewrite in_mset1D eqxx orTb /=.
  rewrite !big_ord_recl big_ord0 !tnthS !tnth0 => /(_ isT) H1.
  apply IHseq_calc_bool_ms.
  intros. rewrite in_mset1D in H2. move/predU1P: H2 => [|] H2.
      * subst.
        by case/andP: H1.
      * apply H0. by rewrite in_mset1D H2 orbT.
- have := H0 (a `/\ b).
  rewrite in_mset1D eq_refl orTb /=.
  rewrite !big_ord_recl big_ord0 !tnthS !tnth0 => /(_ isT) H1.
  apply IHseq_calc_bool_ms.
  intros. rewrite in_mset1D in H2. move/predU1P: H2 => [|] H2.
      * subst.
        by case/andP : H1 => _ /andP[].
      * apply H0. by rewrite in_mset1D H2 orbT.
- destruct (IHseq_calc_bool_ms H0) as [x [IH1 IH2]].
  rewrite in_mset1D in IH1. move/predU1P: IH1 => [|] H1.
    + subst.
      exists (a `\/ b).
      rewrite in_mset1D eqxx orTb//= !big_ord_recl big_ord0 !tnthS !tnth0 IH2.
      by rewrite orTb.
    + exists x.
      by rewrite IH2 in_mset1D H1 orbT.
- destruct (IHseq_calc_bool_ms H0) as [x [IH1 IH2]].
  rewrite in_mset1D in IH1. move/predU1P : IH1 => [|] H1.
    + subst.
      exists (a `\/ b).
      rewrite in_mset1D eqxx orTb/= !big_ord_recl big_ord0 !tnthS !tnth0 IH2.
      by rewrite orbT.
    + exists x.
      by rewrite IH2 in_mset1D H1 orbT.
- have := H1 (a `\/ b).
  rewrite in_mset1D eqxx orTb/= => /(_ isT).
  rewrite !big_ord_recl big_ord0 !tnthS !tnth0 orbF => /orP[ha|hb].
  + apply IHseq_calc_bool_ms1.
    intros. rewrite in_mset1D in H2. move/predU1P: H2 => [|] H2.
      * subst. by apply ha.
      * apply H1. by rewrite in_mset1D H2 orbT.
  + apply IHseq_calc_bool_ms2.
    intros. rewrite in_mset1D in H2. move/predU1P: H2 => [|] H2.
    * subst. by apply hb.
    * apply H1. by rewrite in_mset1D H2 orbT.
- have := H0 (`~ a).
  rewrite in_mset1D eq_refl orTb => /(_ isT) H1.
  destruct IHseq_calc_bool_ms as [x y].
  + intros. apply H0.
    by rewrite in_mset1D H2 orbT.
  + exists x. destruct y as [h1 h2].
    rewrite h2.
    rewrite in_mset1D in h1. move/predU1P: h1 => [h1 | h3].
    * subst. rewrite /= in H1.
      by rewrite h2 in H1.
    * by rewrite h3.
Qed.

End seq_calc_bool.
