From HB Require Import structures.
From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder finmap multiset.
Require Import mathcomp_extra analysis_extra ldl dl2.

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
Local Open Scope ldl_scope.
Local Open Scope mset_scope.
Context {R : realType}.
Context {K : choiceType}.
Implicit Types (s : seq K).
Variable p : R.
Local Notation "[[ e ]]_dl2" := (@dl2_translation R  _ e).

Let formula := @expr R boolT_dl2.
Let hypersequent := seq (seq formula * seq formula).

Implicit Type Q P S : hypersequent.
Implicit Type A B C D X Y : seq formula.

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).

Inductive seq_calc_dl2 :  hypersequent -> Prop :=
| id_dl2 : forall Q (a : formula),
    seq_calc_dl2 ( ([::a] |- [:: a]) :: Q)
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
| top_dl2 : forall Q A B,
    seq_calc_dl2 ((A |- [::(ldl_bool _ _ _ _ true)]) :: Q)
    
| mandL_dl2 : forall Q A B (a b : formula),
    seq_calc_dl2 ((a::b :: A |- B) :: Q) ->
    seq_calc_dl2 (((a `** b) :: A |- B) :: Q)
| mandR_dl2 : forall Q A1 A2 B1 B2 (a b : formula),
    seq_calc_dl2 ((A1 |- a  :: B1 ) :: Q) ->
    seq_calc_dl2 ((A2 |-  b :: B2 ) :: Q) ->
    seq_calc_dl2 (( A1 ++ A2 |- (a `** b) :: B1 ++ B2) :: Q)
| implR_dl2 : forall Q A B (a b : formula),
    seq_calc_dl2 ((A|- B) :: Q ) ->
    seq_calc_dl2 ((a :: A |- b :: B) :: Q) ->
    seq_calc_dl2 ((A |- (a `=> b) :: B) :: Q)
| implL_dl2 : forall Q A B (a b : formula),
    seq_calc_dl2 ((A|- B) :: Q ) ->
    seq_calc_dl2 ((b :: A |- a :: B) :: Q) ->
    seq_calc_dl2 (( (a `=> b) :: A |- B) :: Q)
| andL_dl2 : forall Q A B (a b : formula),
    seq_calc_dl2 (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_dl2 ((((a `/\ b) :: B) |- A) :: Q) 
| andR_dl2 : forall Q A B (a b : formula),
    seq_calc_dl2 ( (A |- a :: B) :: Q ) ->
    seq_calc_dl2 ( (A |- b :: B) :: Q) ->
    seq_calc_dl2 ((A |- (a `/\ b) :: B) :: Q )
| orL_dl2 : forall  Q A B (a b : formula),
    seq_calc_dl2 ( ((b :: B) |- A) :: Q) ->
    seq_calc_dl2 ( ((a :: B) |- A) :: Q) ->
    seq_calc_dl2 (((a `\/ b) :: B |- A) :: Q)
| orR_dl2 : forall Q A B (a b : formula),
    seq_calc_dl2 (( A |- a :: B ) :: ( A |- b :: B) :: Q ) ->
    seq_calc_dl2 (( A |- (a `\/ b):: B ) :: Q) 
.

Definition eval_dl2 A := \sum_(i <- map dl2_translation A) i.
(*Definition eval_dl2 A := [[(ldl_mand A)]]_dl2 .*)

Lemma eval_dl2_cat A B :
 eval_dl2 (A ++ B) = eval_dl2 A + eval_dl2 B.
Proof. by rewrite /eval_dl2/= !big_map !big_cat. Qed.

Lemma eval_dl2_cons  A (q: formula):
 eval_dl2 (q :: A) = [[q]]_dl2 + eval_dl2 A.
Proof. by rewrite /eval_dl2/= !big_cons. Qed.

Lemma eval_dl2_and_le0 A:
  eval_dl2 A <= 0.
Proof. 
rewrite /eval_dl2; elim: A => [|a l ih].
- by rewrite big_nil lexx.
- have H := dl2_translation_le0 a.
  rewrite big_map in ih.
  by rewrite big_map big_cons; lra.
 Qed.

Lemma sound_dl2 Q :
seq_calc_dl2 Q -> 
  exists2 q : ( seq formula) * (seq formula), q \in Q 
    & eval_dl2 (fst q)  <=  eval_dl2 (snd q).
Proof.
intros; rewrite//=. dependent induction H.
- by exists ([:: a] |- [:: a]) => //; rewrite mem_head.
- by exists ([::] |- [::]).
- case: IHseq_calc_dl2 => [M].
  rewrite !mem_cat => -[IH1 IH2].
  exists M => //.
  rewrite !mem_cat.
  move/orP: IH1 => [->// |/orP].
  case => [-> |]; first by rewrite !orbT.
  by move/orP => [|] ->; rewrite ?(orTb,orbT).
- case: IHseq_calc_dl2 => [q IH1 IH2].
  by exists q => //; rewrite mem_cat IH1 orTb.
- case IHseq_calc_dl2 => [q + IH2].
  rewrite !mem_cat => /orP [h |/orP [h | h]];
  exists q; rewrite ?mem_cat ?h ?orTb ?orbT//=. 
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
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
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
- exists (A |- [:: ldl_bool _ _ _ _ true ]); first by rewrite mem_head.
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
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
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
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
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
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
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
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
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
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
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

Lemma eex_nil Q P :
    seq_calc_dl2 (P ++ Q) ->
    seq_calc_dl2 (Q ++ P).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
rewrite (hxy _  P Q) in H.
rewrite (hxy _  Q P).
exact/eex_dl2/H.
Qed.

Lemma exL_nil Q A B C :
    seq_calc_dl2 (((A ++ B) |- C) :: Q) ->
    seq_calc_dl2 (((B ++ A) |- C) :: Q).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
rewrite (hxy _  A B) in H.
rewrite (hxy _  B A).
exact/exL_dl2/H.
Qed.

Lemma exR_nil Q A B C :
    seq_calc_dl2 ((C |- (A ++ B)) :: Q) ->
    seq_calc_dl2 ((C |- (B ++ A)) :: Q).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
rewrite (hxy _  A B) in H.
rewrite (hxy _  B A).
exact/exR_dl2/H.
Qed.

End dl2_hyperseq_calc.
