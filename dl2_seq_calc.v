From HB Require Import structures.
From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder finmap multiset.
Require Import mathcomp_extra analysis_extra dl dl2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

(**md**************************************************************************)
(* # Hypersequent calculi for DL2                                             *)
(*                                                                            *)
(*                                                                            *)
(* ## DL2                                                                     *)
(* - seq_calc_dl2 == hypersequent calculus DL2                                *)
(* - sound_dl2 == soundness of seq_calc_dl2                                   *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "{[ e ]}" (format "{[  e  ]}").

HB.instance Definition _ (R : realType) x y z v :=
  @gen_choiceMixin (@expr R (boolT x y z v)).

Reserved Notation "Q |= P" (no associativity, at level 61).
Reserved Notation "Q |- P" (no associativity, at level 61).

Section dl2_hyperseq_calc.
Local Open Scope ring_scope.
Local Open Scope dl_scope.
Local Open Scope mset_scope.
Context {R : realType} {K : choiceType}.
Implicit Types (s : seq K).
Variable p : R.
Local Notation "[[ e ]]_dl2" := (@dl2_translation R  _ e).

Let formula := @expr R boolT_dl2.
Let hypersequent := seq (seq formula * seq formula).

Implicit Type Q P S : hypersequent.
Implicit Type A B C D X Y : seq formula.
Implicit Type a b c : formula.

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).

Inductive seq_calc_dl2 :  hypersequent -> Prop :=
| id_dl2 : forall Q a,
    seq_calc_dl2 (([:: a] |- [:: a]) :: Q)
| empty : forall Q,
    seq_calc_dl2 (([::] |- [::]) :: Q)
(*structural*)
| eex_dl2 : forall Q P S1 S2,
    seq_calc_dl2 (S1 ++ P ++ Q ++ S2) ->
    seq_calc_dl2 (S1 ++ Q ++ P ++ S2)
| ew_dl2 : forall Q P,
    seq_calc_dl2 Q ->
    seq_calc_dl2 (Q ++ P)
| ec_dl2 : forall Q P,
    seq_calc_dl2 (Q ++ P ++ P) ->
    seq_calc_dl2 (Q ++ P)
| w_dl2 : forall Q A B C,
    seq_calc_dl2 ((A |- B) :: Q) ->
    seq_calc_dl2 ((A ++ C |- B) :: Q)
| comm_hyper_dl2 : forall Q A1 A2 B1 B2 C D,
    seq_calc_dl2 (((A1 ++ B1) |- C) :: Q) ->
    seq_calc_dl2 (((A2 ++ B2) |- D) :: Q) ->
    seq_calc_dl2 ( ((A1 ++ A2) |- C) :: ((B1 ++ B2) |- D) :: Q)
(*exchange*)
| exL_dl2 : forall Q A B C X Y,
    seq_calc_dl2 (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_dl2 (((X ++ B ++ A ++ Y) |- C) :: Q)
| exR_dl2 : forall Q A B C X Y,
    seq_calc_dl2 ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_dl2 ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
| top_dl2 : forall Q A,
    seq_calc_dl2 ((A |- [:: dl_bool _ _ _ _ true]) :: Q)
| mandL_dl2 : forall Q A B a b,
    seq_calc_dl2 ((a :: b :: A |- B) :: Q) ->
    seq_calc_dl2 (((a `** b) :: A |- B) :: Q)
| mandR_dl2 : forall Q A1 A2 B1 B2 a b,
    seq_calc_dl2 ((A1 |- a  :: B1) :: Q) ->
    seq_calc_dl2 ((A2 |-  b :: B2) :: Q) ->
    seq_calc_dl2 ((A1 ++ A2 |- (a `** b) :: B1 ++ B2) :: Q)
| implR_dl2 : forall Q A B a b,
    seq_calc_dl2 ((A |- B) :: Q ) ->
    seq_calc_dl2 ((a :: A |- b :: B) :: Q) ->
    seq_calc_dl2 ((A |- (a `=> b) :: B) :: Q)
| implL_dl2 : forall Q A B a b,
    seq_calc_dl2 ((A |- B) :: Q ) ->
    seq_calc_dl2 ((b :: A |- a :: B) :: Q) ->
    seq_calc_dl2 (( (a `=> b) :: A |- B) :: Q)
| andL_dl2 : forall Q A B a b,
    seq_calc_dl2 (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_dl2 ((((a `/\ b) :: B) |- A) :: Q)
| andR_dl2 : forall Q A B a b,
    seq_calc_dl2 ( (A |- a :: B) :: Q ) ->
    seq_calc_dl2 ( (A |- b :: B) :: Q) ->
    seq_calc_dl2 ((A |- (a `/\ b) :: B) :: Q )
| orL_dl2 : forall Q A B a b,
    seq_calc_dl2 (((b :: B) |- A) :: Q) ->
    seq_calc_dl2 (((a :: B) |- A) :: Q) ->
    seq_calc_dl2 (((a `\/ b) :: B |- A) :: Q)
| orR_dl2 : forall Q A B a b,
    seq_calc_dl2 ((A |- a :: B ) :: ( A |- b :: B) :: Q ) ->
    seq_calc_dl2 ((A |- (a `\/ b):: B ) :: Q)
.

Definition eval_dl2 A := \sum_(i <- map dl2_translation A) i.
(*Definition eval_dl2 A := [[(dl_mand A)]]_dl2 .*)

Lemma eval_dl2_cat A B : eval_dl2 (A ++ B) = eval_dl2 A + eval_dl2 B.
Proof. by rewrite /eval_dl2/= !big_map !big_cat. Qed.

Lemma eval_dl2_cons A a : eval_dl2 (a :: A) = [[ a ]]_dl2 + eval_dl2 A.
Proof. by rewrite /eval_dl2/= !big_cons. Qed.

Lemma eval_dl2_and_le0 A : eval_dl2 A <= 0.
Proof.
rewrite /eval_dl2; elim: A => [|a l ih].
- by rewrite big_nil lexx.
- have H := dl2_translation_le0 a.
  rewrite big_map in ih.
  by rewrite big_map big_cons; lra.
 Qed.

Lemma sound_dl2 Q : seq_calc_dl2 Q ->
  exists2 q : (seq formula) * (seq formula), q \in Q
    & eval_dl2 (fst q)  <=  eval_dl2 (snd q).
Proof.
move=> H; dependent induction H.
- by exists ([:: a] |- [:: a]) => //; rewrite mem_head.
- by exists ([::] |- [::]).
- case: IHseq_calc_dl2 => [M].
  rewrite !mem_cat => -IH1 IH2.
  exists M => //.
  rewrite !mem_cat.
  move/orP: IH1 => [->// |/orP].
  case => [-> |]; first by rewrite !orbT.
  by move/orP => [|] ->; rewrite ?(orTb,orbT).
- case: IHseq_calc_dl2 => [q IH1 IH2].
  by exists q => //; rewrite mem_cat IH1 orTb.
- case IHseq_calc_dl2 => [q + IH2].
  rewrite !mem_cat => /orP [h |/orP [h | h]];
  by exists q; rewrite ?mem_cat ?h ?orTb ?orbT.
- move: IHseq_calc_dl2 => [q + IH2].
  rewrite in_cons => /predU1P[h|h].
  + exists (A ++ C |- B) => //; subst.
      rewrite //= in IH2.
      by rewrite in_cons eq_refl orTb//.
    rewrite //= eval_dl2_cat. rewrite //= in IH2.
    have hc := eval_dl2_and_le0 C.
    by lra.
  + by exists q => //; rewrite in_cons h orbT.
- case IHseq_calc_dl2_1 => [q1].
  case IHseq_calc_dl2_2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH12 /predU1P[h1 | h1] IH22.
  + subst.
    rewrite //= !eval_dl2_cat in IH12 IH22.
    have temp : eval_dl2 A2 <= eval_dl2 B1 \/ eval_dl2 A2 > eval_dl2 B1. lra.
    destruct temp as [ab | ab].
    * exists (A1 ++ A2 |- C); first by rewrite !in_cons eq_refl !orTb //=.
      rewrite eval_dl2_cat. lra.
    * exists (B1 ++ B2 |- D); first by rewrite !in_cons eq_refl !orTb orbT//=.
      rewrite eval_dl2_cat. lra.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case: IHseq_calc_dl2 => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + exists (X ++ B ++ A ++ Y |- C); subst; first by rewrite mem_head.
    rewrite//= !eval_dl2_cat in IH2.
    by rewrite//= !eval_dl2_cat; lra.
  + by exists q => //; rewrite in_cons h orbT.
- case: IHseq_calc_dl2 => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + subst. exists (C |- X ++ B ++ A ++ Y); first by rewrite mem_head.
    rewrite//= !eval_dl2_cat in IH2.
    by rewrite//= !eval_dl2_cat; lra.
  + by exists q => //; rewrite in_cons h orbT.
- exists (A |- [:: dl_bool _ _ _ _ true ]); first by rewrite mem_head.
  by rewrite//= /eval_dl2/= !big_cons big_nil !addr0 eval_dl2_and_le0/=.
- case: IHseq_calc_dl2 => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + subst. exists ((a `** b) :: A |- B); first by rewrite mem_head.
    rewrite//= !eval_dl2_cons in IH2.
    rewrite//= eval_dl2_cons/= big_ord_recl !big_ord1 tnthS !tnth0.
    rewrite addrA in IH2.
    by [].
  + by exists q => //; rewrite in_cons h orbT.
- case IHseq_calc_dl2_1 => [q1].
  case IHseq_calc_dl2_2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH22 /predU1P[h1 | h1] IH12.
  + subst. exists (A1 ++ A2 |- (a `** b) :: B1 ++ B2); first by rewrite mem_head.
    have ev_0 : eval_dl2 [::] = 0.
      rewrite /eval_dl2/= big_nil//=.
    rewrite//= !eval_dl2_cons ?addrA//= in IH12 IH22.
    by rewrite//= eval_dl2_cons/= big_ord_recl !big_ord1 tnthS !tnth0 !eval_dl2_cat; lra.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case IHseq_calc_dl2_1 => [q1].
  case IHseq_calc_dl2_2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH22 /predU1P[h1 | h1] IH12.
  + subst. exists (A |- (a `=> b) :: B); first by rewrite mem_head.
    rewrite//= in IH12.
    rewrite//= eval_dl2_cons eval_dl2_cons in IH22.
    rewrite//= eval_dl2_cons//= /maxr; case: ifP; move => /eqP hc;
    by rewrite ?oppr0 ?add0r//=; lra.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case IHseq_calc_dl2_1 => [q1].
  case IHseq_calc_dl2_2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH22 /predU1P[h1 | h1] IH12.
  + subst. exists ((a `=> b) :: A |- B); first by rewrite mem_head.
    rewrite//= in IH12.
    rewrite//= eval_dl2_cons eval_dl2_cons in IH22.
    rewrite//= eval_dl2_cons//= /maxr; case: ifP; move => /eqP hc.
    * by rewrite oppr0 add0r//=.
    * by lra.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case: IHseq_calc_dl2 => [q + IH2].
  rewrite !in_cons => /predU1P[h |/predU1P [h | h]].
  + subst. exists ((a `/\ b) :: B |- A); first by rewrite mem_head.
    rewrite//= !eval_dl2_cons //= in IH2.
    rewrite//= eval_dl2_cons/= !big_ord_recl !tnthS !tnth0//=.
    by rewrite /minr; repeat case: ifP; move => h1 h2; lra.
  + subst. exists ((a `/\ b) :: B |- A); first by rewrite mem_head.
    rewrite//= !eval_dl2_cons //= in IH2.
    rewrite//= eval_dl2_cons/= !big_ord_recl !tnthS !tnth0//=.
    by rewrite /minr; repeat case: ifP; move => h1 h2; lra.
  + by exists q => //; rewrite in_cons h orbT.
- case IHseq_calc_dl2_1 => [q1].
  case IHseq_calc_dl2_2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH22 /predU1P[h1 | h1] IH12.
  + subst. exists (A |- (a `/\ b) :: B); first by rewrite mem_head.
    rewrite//= !eval_dl2_cons in IH12 IH22.
    rewrite//= eval_dl2_cons//= !big_ord_recl big_ord0 !tnthS !tnth0 /minr//=;
    repeat case: ifP; move => hc;
    rewrite ?oppr0 ?add0r//=; lra.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case IHseq_calc_dl2_1 => [q1].
  case IHseq_calc_dl2_2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH22 /predU1P[h1 | h1] IH12.
  + subst. exists ((a `\/ b) :: B |- A); first by rewrite mem_head.
    rewrite//= !eval_dl2_cons in IH12 IH22.
    rewrite//= eval_dl2_cons//= !big_ord_recl big_ord0 !tnthS !tnth0 /maxr.
    repeat case: ifP; move => /eqP hc;
    by rewrite ?oppr0 ?add0r//=; lra.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case: IHseq_calc_dl2 => [q + IH2].
  rewrite !in_cons => /predU1P[h |/predU1P [h | h]].
  + subst. exists (A |- (a `\/ b) :: B); first by rewrite mem_head.
    rewrite//= !eval_dl2_cons //= in IH2.
    rewrite//= eval_dl2_cons/= !big_ord_recl big_ord0 !tnthS !tnth0//=.
    by rewrite /maxr; repeat case: ifP; move => h1 h2; lra.
  + subst. exists (A |- (a `\/ b) :: B); first by rewrite mem_head.
    rewrite//= !eval_dl2_cons //= in IH2.
    rewrite//= eval_dl2_cons/= !big_ord_recl big_ord0 !tnthS !tnth0//=.
    by rewrite /maxr; repeat case: ifP; move => h1 h2; lra.
  + by exists q => //; rewrite in_cons h orbT.
Qed.

Lemma dl2_cat1C Q I : seq_calc_dl2 (I :: Q) = seq_calc_dl2 ([:: I] ++ Q).
Proof. by []. Qed.

Lemma eex_nil Q P : seq_calc_dl2 (P ++ Q) <-> seq_calc_dl2 (Q ++ P).
Proof.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
rewrite (hxy _  Q P). split => ih.
- apply eex_dl2; by rewrite cats0//=.
- apply eex_dl2 in ih. by rewrite cats0//= in ih.
Qed.

Lemma exL_nil Q A B C :
  seq_calc_dl2 (((A ++ B) |- C) :: Q) <->
  seq_calc_dl2 (((B ++ A) |- C) :: Q).
Proof.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
split; rewrite (hxy _  A B) (hxy _  B A);
exact/exL_dl2.
Qed.

Lemma exR_nil Q A B C :
  seq_calc_dl2 ((C |- (A ++ B)) :: Q) <->
  seq_calc_dl2 ((C |- (B ++ A)) :: Q).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
split; rewrite (hxy _  A B) (hxy _  B A);
exact/exR_dl2.
Qed.

Lemma dl2_prelinearity a b :
  seq_calc_dl2 ([:: ([::] |- [:: ((a `=> b) `\/ (b `=> a))])]).
Proof.
apply orR_dl2.
apply implR_dl2.
- rewrite dl2_cat1C.
  apply ew_dl2.
  exact: empty.
- rewrite dl2_cat1C eex_nil.
  apply implR_dl2.
  + rewrite dl2_cat1C.
    apply ew_dl2.
    exact: empty.
  + rewrite dl2_cat1C. rewrite -(cat0s [:: b]) -{2}((cat0s [:: a])).
    have commH :  [:: [:: b] |- [:: a]] ++ [:: [:: a] |- [:: b]] =
                   [:: [::] ++ [:: b] |- [:: a], [:: a] ++ [::] |- [:: b] & [::]] by rewrite//=.
    rewrite commH.
    apply comm_hyper_dl2; rewrite ?cat0s ?cats0; by apply id_dl2.
Qed.

Lemma comm_xy a c :
  [:: [:: c] |- [:: a]] ++ [:: [:: a] |- [:: c]] =
                   [:: [::] ++ [:: c] |- [:: a], [:: a] ++ [::] |- [:: c] & [::]].
Proof. by []. Qed.

Lemma comm_hyper_xy a b :
seq_calc_dl2 [:: [:: b] |- [:: a]; [:: a] |- [:: b]].
Proof.
rewrite dl2_cat1C. rewrite -(cat0s [:: b]) -{2}((cat0s [:: a])).
rewrite comm_xy.
apply comm_hyper_dl2; rewrite ?cat0s ?cats0; by apply id_dl2.
Qed.

Lemma dl2_seq_distributivity a b c :
  seq_calc_dl2 ([:: ([::] |- [:: ((a `/\ (b `\/ c)) `=> ((a `/\ b) `\/ (a `/\ c)))])]).
Proof.
apply implR_dl2; first by apply empty.
apply orR_dl2.
apply andL_dl2.
apply andR_dl2.
- repeat rewrite dl2_cat1C; apply ew_dl2. exact: id_dl2.
- rewrite !dl2_cat1C.
  apply eex_nil. rewrite !dl2_cat1C.
  apply eex_nil.
  apply andL_dl2.
  apply andR_dl2; first by repeat rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
  rewrite !dl2_cat1C.
  apply eex_nil.
  apply orL_dl2; apply andR_dl2.
  + rewrite cat_cons_xyz_xy. apply eex_nil.
    apply orL_dl2; apply andR_dl2.
    * rewrite cat_cons_xyz_xy.
      apply ew_dl2.
      exact: comm_hyper_xy.
    * rewrite cat_cons_xyz_xyz. apply ew_dl2.
      rewrite dl2_cat1C. apply eex_nil. apply ew_dl2.
      exact: comm_hyper_xy.
    * rewrite dl2_cat1C. apply eex_nil. rewrite //= cat_cons_xyz_xy.
      apply ew_dl2.
      exact: comm_hyper_xy.
    * by repeat rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
  + by repeat rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
  + rewrite cat_cons_xyz_xy.
    apply ew_dl2.
    exact: comm_hyper_xy.
  + rewrite dl2_cat1C; apply eex_nil.
    rewrite dl2_cat1C; apply eex_nil.
    apply orL_dl2; apply andR_dl2.
    * rewrite cat_cons_xyz_xy. apply ew_dl2.
      exact: comm_hyper_xy.
    * rewrite cat_cons_xyz_xyz. apply ew_dl2.
      rewrite dl2_cat1C; apply eex_nil.
      rewrite dl2_cat1C; apply eex_nil. apply ew_dl2.
      exact: comm_hyper_xy.
    * rewrite cat_cons_xyz_xyz. apply eex_nil.
      rewrite //=cat_cons_xyz_xy. apply ew_dl2.
      exact: comm_hyper_xy.
    * by repeat rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
Qed.

Lemma dl2_seq_andC a b :
  seq_calc_dl2 [:: ([:: a `/\ b] |- [:: b`/\ a])].
Proof.
apply andR_dl2; apply andL_dl2.
- by rewrite dl2_cat1C; apply eex_nil; apply ew_dl2; exact: id_dl2.
- by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
Qed.

Lemma dl2_seq_orC a b :
  seq_calc_dl2 [:: ([:: a `\/ b] |- [:: b`\/ a])].
Proof.
apply orL_dl2; apply orR_dl2.
- by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
- by rewrite dl2_cat1C; apply eex_nil; apply ew_dl2; exact: id_dl2.
Qed.

Lemma dl2_seq_andA1 (a b c : formula) :
  seq_calc_dl2 [:: ([:: a `/\ (b `/\ c)] |- [:: (a `/\ b) `/\ c])].
Proof.
apply andR_dl2; apply andL_dl2.
- apply andR_dl2; first by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
  rewrite dl2_cat1C; apply eex_nil.
  apply andR_dl2; apply andL_dl2; last by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
  rewrite dl2_cat1C; apply eex_nil; rewrite dl2_cat1C; apply eex_nil; apply ew_dl2.
  exact: comm_hyper_xy.
- rewrite dl2_cat1C; apply eex_nil.
  apply andL_dl2.
  by rewrite dl2_cat1C; apply eex_nil; apply ew_dl2; exact: id_dl2.
Qed.

Lemma dl2_seq_andA2 a b c :
  seq_calc_dl2 [:: ([:: (a `/\ b) `/\ c] |- [:: a `/\ (b `/\ c)])].
Proof.
apply andR_dl2; apply andL_dl2.
- apply andL_dl2; by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
- apply andR_dl2; apply andL_dl2; first by rewrite dl2_cat1C; apply eex_nil; apply ew_dl2; exact: id_dl2.
  rewrite dl2_cat1C; apply eex_nil. rewrite dl2_cat1C; apply eex_nil.
  apply andR_dl2; last by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
  rewrite dl2_cat1C; apply eex_nil; rewrite dl2_cat1C; apply eex_nil; apply ew_dl2.
  exact: comm_hyper_xy.
Qed.

Lemma dl2_seq_orA1 a b c :
  seq_calc_dl2 [:: ([:: a `\/ (b `\/ c)] |- [:: (a `\/ b) `\/ c])].
Proof.
apply orL_dl2; apply orR_dl2.
- apply orL_dl2; apply orR_dl2; last by rewrite dl2_cat1C; apply eex_nil; apply ew_dl2; exact: id_dl2.
  rewrite dl2_cat1C; apply eex_nil; rewrite dl2_cat1C; apply eex_nil.
  apply orL_dl2; first by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
  rewrite dl2_cat1C; apply eex_nil; rewrite dl2_cat1C; apply eex_nil; apply ew_dl2.
  exact: comm_hyper_xy.
- apply orR_dl2.
  by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
Qed.

Lemma dl2_seq_orA2 a b c :
  seq_calc_dl2 [:: ([:: (a `\/ b) `\/ c] |- [:: a `\/ (b `\/ c)])].
Proof.
apply orL_dl2; apply orR_dl2.
- rewrite dl2_cat1C; apply eex_nil. apply orR_dl2.
  by rewrite dl2_cat1C; apply eex_nil; apply ew_dl2; exact: id_dl2.
- apply orL_dl2; last by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
  rewrite dl2_cat1C; apply eex_nil; apply orL_dl2; apply orR_dl2;
    first by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
  rewrite dl2_cat1C; apply eex_nil; rewrite dl2_cat1C; apply eex_nil; apply ew_dl2.
  exact: comm_hyper_xy.
Qed.

Lemma dl2_seq_and1 a b :
  seq_calc_dl2 [:: ([:: a `/\ (a `\/ b)] |- [:: a])].
Proof.
apply andL_dl2; by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
Qed.

Lemma dl2_seq_and2 a b :
  seq_calc_dl2 [:: ([:: a] |- [:: a `/\ (a `\/ b)])].
Proof.
apply andR_dl2; first exact: id_dl2.
apply orR_dl2; first by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
Qed.

Lemma dl2_seq_or1 a b :
  seq_calc_dl2 [:: ([:: a `\/ (a `/\ b)] |- [:: a])].
Proof.
apply orL_dl2; last by exact: id_dl2.
apply andL_dl2; by rewrite dl2_cat1C; apply ew_dl2; exact: id_dl2.
Qed.

Lemma dl2_seq_or2 a b : seq_calc_dl2 [:: ([:: a] |- [:: a `\/ (a `/\ b)])].
Proof.
by apply orR_dl2; exact: id_dl2.
Qed.

Lemma dl2_seq_unit_el1 a :
  seq_calc_dl2 [:: ([:: a `** dl_bool _ _ _ _ true] |- [:: a ])].
Proof.
apply mandL_dl2.
have -> : [:: a; dl_bool neg_undef impl_def m_def l_def true] =
         [:: a] ++ [:: dl_bool neg_undef impl_def m_def l_def true] by [].
apply w_dl2. rewrite dl2_cat1C.
apply id_dl2.
Qed.

Lemma dl2_seq_unit_el2 a :
  seq_calc_dl2 [:: ([:: a ] |- [:: a `** dl_bool _ _ _ _ true])].
Proof.
rewrite -(cats0 [:: a]) dl2_cat1C.
rewrite -(cats0 [:: dl_mand (tnth [:: a; dl_bool neg_undef impl_def m_def l_def true])]).
rewrite -(cats0 [:: dl_mand (tnth [:: a; dl_bool neg_undef impl_def m_def l_def true])]).
apply mandR_dl2.
- by apply id_dl2.
- by apply top_dl2.
Qed.

Lemma dl2_seq_mandA1 a b c :
  seq_calc_dl2 [:: ([:: a `** (b `** c)] |- [:: (a `** b) `** c])].
Proof.
apply mandL_dl2.
have cat_xy : [:: a; dl_mand (tnth [:: b; c])] = [:: a] ++[:: dl_mand (tnth [:: b; c])]. by rewrite//=.
rewrite cat_xy. rewrite exL_nil.
apply mandL_dl2.
have ha : [:: b; c; a] = [:: b;  c] ++[:: a]. by rewrite//=.
rewrite ha. rewrite exL_nil dl2_cat1C.
rewrite-( cats0 [:: dl_mand (tnth [:: dl_mand (tnth [:: a; b]); c])]).
rewrite-( cats0 [:: dl_mand (tnth [:: dl_mand (tnth [:: a; b]); c])]).
have catbc : [:: a] ++ [:: b; c] = [:: a; b] ++[:: c] by rewrite //=.
rewrite catbc.
apply mandR_dl2; last by apply id_dl2.
have catab : [:: a; b] = [:: a] ++[:: b] by rewrite//=.
rewrite catab.
rewrite -(cats0 [:: dl_mand (tnth [:: a; b])]).
rewrite -(cats0 [:: dl_mand (tnth [:: a; b])]).
apply mandR_dl2; by apply id_dl2.
Qed.

Lemma dl2_seq_mandA2 a b c :
  seq_calc_dl2 [:: ([:: (a `** b) `** c] |- [:: a `** (b `** c)])].
Proof.
apply mandL_dl2; apply mandL_dl2.
have ha : [:: a; b; c] = [:: a] ++ [:: b; c] by rewrite//=.
rewrite ha dl2_cat1C.
rewrite-( cats0 [:: dl_mand (tnth [:: a; dl_mand (tnth [:: b; c])])]).
rewrite-( cats0 [:: dl_mand (tnth [:: a; dl_mand (tnth [:: b; c])])]).
apply mandR_dl2; first by apply id_dl2.
have catbc : [:: b; c] = [:: b] ++[:: c] by rewrite//=.
rewrite {1}catbc.
rewrite -(cats0 [:: dl_mand (tnth [:: b; c])]).
rewrite -(cats0 [:: dl_mand (tnth [:: b; c])]).
apply mandR_dl2; by apply id_dl2.
Qed.

End dl2_hyperseq_calc.
