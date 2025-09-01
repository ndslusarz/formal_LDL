From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder finmap multiset.
Require Import mathcomp_extra analysis_extra ldl fuzzy.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory Order.TTheory.
Import numFieldTopology.Exports.

(**md**************************************************************************)
(* # Hypersequent calculi for fuzzy DLs: Lukasiewicz, product, Godel          *)
(*  grouped by DL                                                             *)
(*                                                                            *)
(*                                                                            *)
(* ## Lukasiewicz                                                             *)
(* - seq_calc_luka_impl == hypersequent calculus for the minimal              *)
(*   language fragment                                                        *)
(* - seq_calc_luka == hypersequent calculus for the full syntax               *)
(* - sound_luka_impl == soundness of seq_calc_luka_impl                       *)
(* - sound_luka == soundness of seq_calc_luka                                 *)
(* - luka_neg_impl_admissable == proof that negation can be defined in terms  *)
(*   of implication and bottom                                                *)
(* - luka_true_false_admissable == proof that true can be defined in terms    *)
(*   of negation and bottom                                                   *)
(* - luka_mand_impl_admissable == proof that ** can be defined in terms       *)
(*   of implication and negation                                              *)
(* - luka_mor_impl_admissable == proof that ** can be defined in terms        *)
(*    of implication and negation                                             *)
(* - luka_implL_extended == alternate derivable left implication rule         *)
(* - equivalence_luka == equivalence of seq_calc_luka and seq_calc_luka_impl  *)
(*                                                                            *)
(* ## product                                                                 *)
(* - seq_calc_product == hypersequent calculus for the minimal                *)
(*   language fragment                                                        *)
(* - seq_calc_product' == hypersequent calculus for the full syntax           *)
(* - sound_product == soundness of seq_calc_product                           *)
(* - sound_product' == soundness of seq_calc_product'                         *)
(* - product_neg_impl_admissable == proof that negation can be defined in     *)
(*   terms of implication and bottom                                          *)
(* - product_true_false_admissable == proof that true can be defined in terms *)
(*   of negation and bottom                                                   *)
(* - equivalence_product == equivalence of seq_calc_product'                  *)
(*   and seq_calc_product                                                     *)
(*                                                                            *)
(* ## Godel                                                                   *)
(* - seq_calc_godel == hypersequent calculus for the minimal                  *)
(*   language fragment                                                        *)
(* - seq_calc_godel' == hypersequent calculus for the full syntax             *)
(* - sound_godel == soundness of seq_calc_godel                               *)
(* - sound_godel == soundness of seq_calc_godel'                              *)
(* - godel_neg_impl_admissable == proof that negation can be defined in terms *)
(*   of implication and bottom                                                *)
(* - equivalence_godel == equivalence of seq_calc_godel'                      *)
(*   and seq_calc_godel                                                       *)
(******************************************************************************)

Reserved Notation "{[ e ]}" (format "{[  e  ]}").

HB.instance Definition _ (R : realType) x y z v :=
  @gen_choiceMixin (@expr R (boolT x y z v)).

Reserved Notation "Q |= P" (no associativity, at level 61).
Reserved Notation "Q |- P" (no associativity, at level 61).
Open Scope ldl_scope.

Definition neg_impl_dl (R : realType) :=
  forall f1 f2 (e : @expr R (boolT_def impl_def f1 f2)),
    (`~ e) = (e `=> ldl_bool neg_def impl_def f1 f2 false).

Definition true_false_dl (R : realType) :=
  forall f1 f2 f3,
    (@ldl_bool R neg_def f1 f2 f3  true) = (`~ ldl_bool neg_def f1 f2 f3 false).

Definition mand_impl_dl (R : realType) :=
  forall f (a b : @expr R (boolT_def impl_def m_def f)), (a `** b) = (`~ (a `=> `~b)).

Definition mor_impl_dl (R : realType) :=
  forall f (a b : @expr R (boolT_def impl_def m_def f)), (a `++ b) = ((`~ a) `=> b).

Section hypersequent_lukasiewicz.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType} {K : choiceType}.
Implicit Types (s : seq K).
Variable p : R.
Hypothesis p1 : 1 <= p.
Local Notation "[[ e ]]_ l" := (@translation R l p _ e).

Hypothesis neg_impl_luka  : neg_impl_dl R.

Hypothesis true_false_luka :  true_false_dl R.

Hypothesis mand_impl_luka : mand_impl_dl R.

Hypothesis mor_impl_luka : mor_impl_dl R.

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).
(*entailment as pair (A, B) where A |- B*)

(*soundness for minimal implicational fragment*)

Let formula := @expr R boolT_fuzzy.
Let hypersequent := seq (seq formula * seq formula).

Implicit Type Q P S : hypersequent.
Implicit Type A B C D X Y : seq formula.

Inductive seq_calc_luka_impl : hypersequent -> Prop :=
| id_l : forall Q A,
    seq_calc_luka_impl ( (A |- A) :: Q)
| empty : forall Q,
    seq_calc_luka_impl (([::] |- [::]) :: Q)
(*structural*)
| eex_l : forall Q P S1 S2,
    seq_calc_luka_impl (S1 ++ P ++ Q ++ S2) ->
    seq_calc_luka_impl (S1 ++ Q ++ P ++ S2)
| ew_l : forall Q P,
    seq_calc_luka_impl Q ->
    seq_calc_luka_impl (Q ++ P)
| ec_l : forall Q P,
    seq_calc_luka_impl (Q ++ P ++ P) ->
    seq_calc_luka_impl (Q ++ P)
| w_l : forall Q A B C,
    seq_calc_luka_impl ((A |- B) :: Q) ->
    seq_calc_luka_impl ((A ++ C |- B) :: Q)
| split_l : forall Q A B C D,
    seq_calc_luka_impl (((A ++ B) |- (C ++ D)) :: Q) ->
    seq_calc_luka_impl ((A |- C) ::  (B |- D) :: Q)
| mix_l : forall Q A B C D,
    seq_calc_luka_impl ((A |- C) :: Q) ->
    seq_calc_luka_impl ((B |- D) :: Q) ->
    seq_calc_luka_impl ((A ++ B |- C ++ D) :: Q)
(*exchange*)
| exL_l : forall Q A B C X Y,
    seq_calc_luka_impl ((X ++ A ++ B ++ Y |- C) :: Q) ->
    seq_calc_luka_impl ((X ++ B ++ A ++ Y |- C) :: Q)
| exR_l : forall Q A B C X Y,
    seq_calc_luka_impl ((C |- X ++ A ++ B ++ Y) :: Q) ->
    seq_calc_luka_impl ((C |- X ++ B ++ A ++ Y) :: Q)
(*logical*)
(*restricted to a single-conclusion case for Lukasiewicz*)
| bot_l : forall Q A (b : formula),
    seq_calc_luka_impl (((ldl_bool neg_def _ _ _ false :: A) |- [:: b]) :: Q)
|implL_l : forall Q A B (a b : formula),
    seq_calc_luka_impl (((b :: B) |- a:: A) :: Q ) ->
    seq_calc_luka_impl ((((a `=> b) :: B) |- A) :: Q)
| implR_l : forall Q A B (a b : formula),
    seq_calc_luka_impl ((A |- B) :: Q ) ->
    seq_calc_luka_impl  ((a :: A |- b :: B) :: Q)  ->
    seq_calc_luka_impl ((A |- (a `=> b) :: B) :: Q )
(*standard lattice rules*)
| andL_l : forall Q A B (a b : formula),
    seq_calc_luka_impl (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_luka_impl ((((a `/\ b) :: B) |- A) :: Q)
| andR_l : forall Q A B (a b : formula),
    seq_calc_luka_impl ((A |- a :: B) :: Q) ->
    seq_calc_luka_impl ((A |- b :: B) :: Q) ->
    seq_calc_luka_impl ((A |-  (a `/\ b) :: B) :: Q )
| orL_l : forall  Q A B (a b : formula),
    seq_calc_luka_impl (((b :: A) |- B) :: Q) ->
    seq_calc_luka_impl (((a :: A) |- B) :: Q) ->
    seq_calc_luka_impl (((a `\/ b) :: A |- B) :: Q)
| orR_l : forall Q A B (a b : formula),
    seq_calc_luka_impl (( A |- a :: B ) :: ( A |- b :: B) :: Q ) ->
    seq_calc_luka_impl (( A |- (a `\/ b) :: B) :: Q) .

Inductive seq_calc_luka : hypersequent -> Prop :=
| id_l' : forall Q A,
    seq_calc_luka ((A |- A) :: Q)
| empty' : forall Q,
    seq_calc_luka (([::] |- [::]) :: Q)
(*structural*)
| eex_l' : forall Q P S1 S2,
    seq_calc_luka (S1 ++ P ++ Q ++ S2) ->
    seq_calc_luka (S1 ++ Q ++ P ++ S2)
| ew_l' : forall Q P,
    seq_calc_luka Q ->
    seq_calc_luka (Q ++ P)
| ec_l' : forall Q P,
    seq_calc_luka (Q ++ P ++ P) ->
    seq_calc_luka (Q ++ P)
| w_l' : forall Q A B C,
    seq_calc_luka ((A |- B) :: Q) ->
    seq_calc_luka ((A ++ C |- B) :: Q)
| split_l' : forall Q A B C D,
    seq_calc_luka ((A ++ B |- (C ++ D)) :: Q) ->
    seq_calc_luka ((A |- C) ::  (B |- D) :: Q)
| mix_l' : forall Q A B C D,
    seq_calc_luka ((A |- C) :: Q) ->
    seq_calc_luka ((B |- D) :: Q) ->
    seq_calc_luka ((A ++ B |- (C ++ D)) :: Q)
| exL_l' : forall Q A B C X Y,
    seq_calc_luka ((X ++ A ++ B ++ Y |- C) :: Q) ->
    seq_calc_luka ((X ++ B ++ A ++ Y |- C) :: Q)
| exR_l' : forall Q A B C X Y,
    seq_calc_luka ((C |- X ++ A ++ B ++ Y) :: Q) ->
    seq_calc_luka ((C |- X ++ B ++ A ++ Y) :: Q)
(*logical*)
(*both are restricted to a single-conclusion case for Lukasiewicz*)
| bot_l' : forall Q A (b : formula),
    seq_calc_luka (((ldl_bool neg_def _ _ _ false :: A) |- [:: b]) :: Q)
| top_l' : forall Q A,
    seq_calc_luka ((A |- [:: (ldl_bool neg_def _ _ _  true)]) :: Q)
| mandL_l' : forall Q A B (a b : formula),
    seq_calc_luka (((a :: b :: B) |- A) :: Q ) ->
    seq_calc_luka ((ldl_bool neg_def _ _ _ false :: B |- A) :: Q ) ->
    seq_calc_luka ((((a `** b) :: B) |- A) :: Q)
| mandR_l' : forall Q A B (a b : formula),
    seq_calc_luka ((A |- B) :: Q ) -> (*not needed for soundness,
                                        but this is needed for this rule
                                        to be derivable*)
    seq_calc_luka  ((A |- (a ::  b :: B)) :: (A |- (ldl_bool neg_def _ _ _ false :: B)) :: Q)  ->
    seq_calc_luka ((A |- (a `** b) :: B) :: Q )
| negL_l' : forall Q A B (a : formula),
    seq_calc_luka (((ldl_bool neg_def _ _ _ false :: A) |-  a :: B) :: Q) ->
    seq_calc_luka ((((`~ a) :: A) |- B) :: Q)
| negR_l' : forall Q A B (a : formula),
    seq_calc_luka ( ( A |- B):: Q) ->
    seq_calc_luka (((a :: A) |-  ldl_bool neg_def _ _ _ false :: B)::Q) ->
    seq_calc_luka ((A |-  (`~a) :: B) :: Q)
| morL_l' : forall Q A B (a b : formula),
    seq_calc_luka (( A |- B) :: Q) ->
    seq_calc_luka (((a :: b :: A) |- ldl_bool neg_def _ _ _ false :: B) :: Q) ->
    seq_calc_luka ((((a `++ b) :: A) |- B) :: Q)
| morR_l' : forall Q A B (a b : formula),
    seq_calc_luka ((A |- B):: Q) ->
    seq_calc_luka (((ldl_bool neg_def _ _ _ false :: A) |-  a :: b :: B) :: Q) ->
    seq_calc_luka ((A |- (a `++ b) :: B) :: Q)
| andL_l' : forall Q A B (a b : formula),
    seq_calc_luka (((a :: B) |- A) :: ((b :: B) |- A) :: Q) ->
    seq_calc_luka ((((a `/\ b) :: B) |- A) :: Q)
| andR_l' : forall Q A B (a b : formula),
    seq_calc_luka ((A |- a :: B) :: Q ) ->
    seq_calc_luka ((A |- b :: B) :: Q) ->
    seq_calc_luka ((A |- (a `/\ b) :: B) :: Q)
| orL_l' : forall Q A B (a b : formula),
    seq_calc_luka (((b :: A) |- B) :: Q) ->
    seq_calc_luka (((a :: A) |- B) :: Q) ->
    seq_calc_luka (((a `\/ b) :: A |- B) :: Q)
| orR_l' : forall Q A B (a b : formula),
    seq_calc_luka (( A |- a :: B ) :: ( A |- b :: B) :: Q ) ->
    seq_calc_luka (( A |- (a `\/ b) :: B ) :: Q).

Definition eval_luka A := 1%R + \sum_(i <- A) ([[i]]_Lukasiewicz - 1%R).

Lemma eval_luka_add_el A (a : formula) :
  eval_luka (a :: A) = eval_luka A + [[a]]_Lukasiewicz  - 1.
Proof. by rewrite /eval_luka//= big_cons//=; lra. Qed.

Lemma eval_luka_add A B : eval_luka (A ++ B) = eval_luka A + eval_luka B  - 1.
Proof.
rewrite /eval_luka/= big_cat/= -!addrA; congr (_ + (_ + _)).
by rewrite addrCA subrr addr0.
Qed.

Lemma eval_luka1 A : eval_luka A <= 1.
Proof.
rewrite /eval_luka gerDl sumr_le0//= => i _.
rewrite subr_le0.
by have /andP[] := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ i.
Qed.

Lemma sound_luka_impl Q : seq_calc_luka_impl Q ->
  exists2 q : seq formula * seq formula,
  q \in Q & eval_luka q.1 <= eval_luka q.2.
Proof.
intros; rewrite//=. dependent induction H.
- by exists (A |- A) => //; rewrite mem_head.
- by exists ([::] |- [::]).
- case: IHseq_calc_luka_impl => [M].
  rewrite !mem_cat => IH1 IH2.
  exists M => //.
  rewrite !mem_cat.
  move/orP: IH1 => [->// |/orP].
  case => [-> |]; first by rewrite !orbT.
  by move/orP => [|] ->; rewrite ?(orTb,orbT).
- case: IHseq_calc_luka_impl => [q IH1 IH2].
  by exists q => //; rewrite mem_cat IH1 orTb.
- case IHseq_calc_luka_impl => [M IH1 IH2].
  exists M => //; rewrite !mem_cat in IH1.
  rewrite mem_cat. move/orP : IH1.
  move => [h |/orP h].
    rewrite h ?orbT; split; rewrite//=.
  by move: h => [h | h]; rewrite h ?orbT; split; rewrite//=.
- move: IHseq_calc_luka_impl => [q + IH2].
  rewrite in_cons => /predU1P[h|h].
  + exists (A ++ C |- B) => //; subst.
      rewrite //= in IH2.
      by rewrite in_cons eq_refl orTb//.
    rewrite //= eval_luka_add.
    have hc := eval_luka1 C.
    by lra.
  + by exists q => //; rewrite in_cons h orbT.
- move: IHseq_calc_luka_impl => [q1 + IH2].
  rewrite in_cons => /orP[h1|h2]; first last.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
  + move/eqP in h1.
    subst. rewrite !eval_luka_add in IH2.
    have helper :
      (eval_luka A + eval_luka B)%E - 1 <= (eval_luka C + eval_luka D)%E - 1 ->
      (eval_luka A + eval_luka B)%E - eval_luka D - 1 <= eval_luka C  - 1 .
      by intros; lra.
    apply helper in IH2.
    clear helper.
    have /orP[h1|h1] := le_total (1 + eval_luka B) (1 + eval_luka D).
    * exists (B |- D).
      - by rewrite !in_cons eq_refl !orbT.
      - by rewrite  //=; lra.
    * exists (A |- C) => /=.
      - by rewrite !in_cons eq_refl !orTb.
      - rewrite lerD2l -subr_ge0 in h1.
        have helper2 (A' B' C' D' : R) : 0 <= B' - D' ->
          A' + B' - D' - 1 <= C'-1 ->
          A' <=  C' by intros; lra.
        have hh := helper2 (eval_luka A) (eval_luka B) (eval_luka C) (eval_luka D).
        by rewrite (hh h1 IH2).
- case IHseq_calc_luka_impl1 => [q1].
  case IHseq_calc_luka_impl2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + exists (A ++ B |- C ++ D) => //.
    by rewrite mem_head.
    subst.
    rewrite /= in IH12.
    rewrite /= in IH22.
    rewrite /=.
    have IH := lerD IH12 IH22.
    rewrite !eval_luka_add. lra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case: IHseq_calc_luka_impl => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + subst. exists ((X ++ B ++ A ++ Y |- C)) => //; first by rewrite mem_head.
    rewrite//= !eval_luka_add in IH2.
    rewrite//= !eval_luka_add. lra.
  + by exists q => //; rewrite in_cons h orbT.
- move: IHseq_calc_luka_impl => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + subst. exists (C |- X ++ B ++ A ++ Y).
    by rewrite mem_head.
    rewrite//= !eval_luka_add in IH2.
    by rewrite//= !eval_luka_add; lra.
  + by exists q; rewrite ?in_cons ?h ?orbT//=.
- exists (ldl_bool neg_def  _ _ _ false :: A |- [:: b]); first by rewrite mem_head.
  rewrite //= !eval_luka_add_el addr0.
  have h := eval_luka1 A.
  have hb := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ b.
  have := hb => /andP[b0 b1].
  have helper : 0 <= (eval_luka [::] + [[b]]_Lukasiewicz)%E - 1 ->
                eval_luka A - 1 <= (eval_luka [::] + [[b]]_Lukasiewicz)%E - 1 by intros; lra.
  by apply helper; rewrite /eval_luka//= big_nil addr0; lra.
- move: IHseq_calc_luka_impl => [q + IH2].
  rewrite in_cons => /predU1P[h1 | h2].
  + exists ((a `=> b) :: B |- A); first by rewrite mem_head.
    subst.
    rewrite //= !eval_luka_add_el in IH2.
    rewrite //= !eval_luka_add_el//=/minr; case: ifP => h.
    * by rewrite addrA; lra.
    * have H1 : (eval_luka B + [[b]]_Lukasiewicz)%E - 1 <= (eval_luka A + [[a]]_Lukasiewicz)%E - 1 ->
                (eval_luka B + [[b]]_Lukasiewicz)%E - [[a]]_Lukasiewicz <= eval_luka A by intros; lra.
      apply H1 in IH2; clear H1.
      have H2 : (((1 - [[a]]_Lukasiewicz)%R + [[b]]_Lukasiewicz)%E < 1) = false ->
                ((( - [[a]]_Lukasiewicz)%R + [[b]]_Lukasiewicz)%E >= 0) by intros; lra.
      by apply H2 in h; lra.
  + by exists q => //; rewrite in_cons h2 orbT.
- case IHseq_calc_luka_impl1 => [q1].
  case IHseq_calc_luka_impl2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + exists (A |- (a `=> b) :: B); first by rewrite mem_head.
    subst.
    rewrite //= in IH12.
    rewrite //= !eval_luka_add_el in IH22.
    rewrite //= eval_luka_add_el//=/minr; case: ifP => h.
    * have temp : (eval_luka A + [[a]]_Lukasiewicz)%E - 1 <= (eval_luka B + [[b]]_Lukasiewicz)%E - 1 ->
                  eval_luka A <= (eval_luka B + ((1 - [[a]]_Lukasiewicz)%R + [[b]]_Lukasiewicz))%E - 1
        by intros; lra.
      by apply temp in IH22; rewrite //=.
    * lra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- move: IHseq_calc_luka_impl => [q1 + IH2].
  rewrite !in_cons => /predU1P[h1 | /predU1P [h2 | h3]].
  + exists ((a `/\ b) :: B |- A); first by rewrite mem_head.
    subst.
    rewrite //= !eval_luka_add_el in IH2.
    rewrite //= !eval_luka_add_el//=/minR !big_ord_recl !big_ord0/= /minr.
    repeat case: ifP; move=> h; lra.
  + exists ((a `/\ b) :: B |- A); first by rewrite mem_head.
    subst.
    rewrite //= !eval_luka_add_el in IH2.
    rewrite //= !eval_luka_add_el//=/minR.
    rewrite !big_ord_recl !big_ord0/= /minr.
    repeat case: ifP; move=> h; lra.
  + by exists q1 => //; rewrite in_cons h3 orbT.
- case IHseq_calc_luka_impl1 => [q1].
  case IHseq_calc_luka_impl2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + exists (A |- (a `/\ b) :: B); first by rewrite mem_head.
    subst.
    rewrite //= eval_luka_add_el//=/minR !big_ord_recl !big_ord0 /minr.
    rewrite //= !eval_luka_add_el in IH12 IH22.
    have hB := eval_luka1 B.
    have hA := eval_luka1 A.
    have ha := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ a.
    have hb := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ b.
    repeat case: ifP; move => h1 h2; lra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case IHseq_calc_luka_impl1 => [q1].
  case IHseq_calc_luka_impl2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + exists ((a `\/ b) :: A |- B); first by rewrite mem_head.
    subst; rewrite //= eval_luka_add_el//=/maxR !big_ord_recl big_ord0 /maxr.
    rewrite //= !eval_luka_add_el in IH12 IH22.
    have hb := @translate_boolT_01 R p p1 Lukasiewicz _ _ _ (b).
    repeat case: ifP; move => h1 h2; lra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- move: IHseq_calc_luka_impl => [q1 + IH2].
  have hB := eval_luka1 B.
  have hA := eval_luka1 A.
  have ha := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ a.
  have hb := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ b.
  rewrite !in_cons => /predU1P[h1 | /predU1P [h2 | h3]].
  + exists (A |- (a `\/ b) :: B); first by rewrite mem_head.
    subst; rewrite //= !eval_luka_add_el//=/maxR !big_ord_recl big_ord0 /maxr.
    rewrite //= !eval_luka_add_el in IH2.
    repeat case: ifP; move=> h1 h2; lra.
  + exists (A |- (a `\/ b) :: B); first by rewrite mem_head.
    subst; rewrite //= !eval_luka_add_el//=/maxR !big_ord_recl big_ord0 /maxr.
    rewrite //= !eval_luka_add_el in IH2.
    repeat case: ifP; move=> h1 h2; lra.
  + by exists q1 => //; rewrite in_cons h3 orbT.
Qed.

Lemma sound_luka Q: seq_calc_luka Q ->
  exists2 q : seq formula * seq formula,
  q \in Q & eval_luka q.1 <= eval_luka q.2.
Proof.
intros; rewrite//=. dependent induction H.
- by exists (A |- A) => //; rewrite mem_head.
- by exists ([::] |- [::]).
- case: IHseq_calc_luka => [M].
  rewrite !mem_cat => IH1 IH2.
  exists M => //.
  rewrite !mem_cat.
  move/orP: IH1 => [->// |/orP].
  case => [-> |]; first by rewrite !orbT.
  by move/orP => [|] ->; rewrite ?(orTb,orbT).
- case: IHseq_calc_luka => [q IH1 IH2].
  by exists q => //; rewrite mem_cat IH1 orTb.
- case IHseq_calc_luka => [M IH1 IH2].
  exists M => //; rewrite !mem_cat in IH1.
  rewrite mem_cat. move/orP : IH1.
  move => [h |/orP h].
    rewrite h ?orbT; split; rewrite//=.
  by move: h => [h | h]; rewrite h ?orbT; split; rewrite//=.
- case: IHseq_calc_luka => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + exists (A ++ C |- B); first by rewrite in_cons eq_refl orTb.
    subst. rewrite //= in IH2.
    rewrite //= eval_luka_add.
    have hc := eval_luka1 C.
    by lra.
  + by exists q => //; rewrite in_cons h orbT.
- case: IHseq_calc_luka => [q + IH2].
  rewrite in_cons => /orP[/eqP h1 | h2].
  + subst. rewrite !eval_luka_add in IH2.
    have helper :
      (eval_luka A + eval_luka B)%E - 1 <= (eval_luka C + eval_luka D)%E - 1 ->
      (eval_luka A + eval_luka B)%E - eval_luka D - 1 <= ( eval_luka C)%E  - 1
      by intros; lra.
    apply helper in IH2.
    clear helper.
    have /orP[h1|h1] := le_total (1 + eval_luka B) (1 + eval_luka D).
    * exists (B |- D).
      - by rewrite !in_cons eq_refl !orbT.
      - by rewrite //=; lra.
    * exists (A |- C) => /=.
      - by rewrite !in_cons eq_refl !orTb.
      - have helper (D' B' : R) : 1 + D' <= 1 + B' -> (B' - D' >= 0)
          by intros; lra.
        apply helper in h1.
        have helper2 (A' B' C' D' : R) : 0 <= B' - D' ->
          A' + B' - D' - 1 <= C'-1 ->
          A' <=  C'
          by intros; lra.
        have hh := helper2 (eval_luka A) (eval_luka B) (eval_luka C) (eval_luka D).
        by rewrite (hh h1 IH2).
  + by exists q => //; rewrite !in_cons h2 !orbT.
- case IHseq_calc_luka1 => [q1].
  case IHseq_calc_luka2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + exists (A ++ B |- C ++ D); first by rewrite mem_head.
    subst.
    rewrite /= in IH12 IH22.
    have IH := lerD IH12 IH22.
    by rewrite /= !eval_luka_add; lra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case: IHseq_calc_luka => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + subst. exists ((X ++ B ++ A ++ Y |- C)); first by rewrite mem_head.
    rewrite//= !eval_luka_add in IH2.
    by rewrite//= !eval_luka_add; lra.
  + by exists q => //; rewrite in_cons h !orbT.
- case: IHseq_calc_luka => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + subst. exists (C |- X ++ B ++ A ++ Y); first by rewrite mem_head.
    rewrite//= !eval_luka_add in IH2.
    by rewrite//= !eval_luka_add; lra.
  + by exists q => //; rewrite in_cons h !orbT.
- exists (ldl_bool neg_def _ _ _ false :: A |- [:: b]); first by rewrite mem_head.
  rewrite /= !eval_luka_add_el addr0.
  have h := eval_luka1 A.
  have /andP[b0 b1] := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ b.
  have : 0 <= (eval_luka [::] + [[b]]_Lukasiewicz)%E - 1 ->
         eval_luka A - 1 <= (eval_luka [::] + [[b]]_Lukasiewicz)%E - 1
    by intros; lra.
  by apply; rewrite /eval_luka//= big_nil addr0; lra.
- exists (A |- [:: ldl_bool neg_def _ _ _ true]); first by rewrite mem_head.
  rewrite //= !eval_luka_add_el//= .
  have h := eval_luka1 A.
  by rewrite addrK /eval_luka big_nil addr0 h.
(*andL_l*)
- case IHseq_calc_luka1 => [q1].
  case IHseq_calc_luka2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + subst.
    exists ((a `** b) :: B |- A); first by rewrite mem_head.
    rewrite eval_luka_add_el//= addr0 in IH22.
    rewrite //=  !eval_luka_add_el in IH12.
    rewrite eval_luka_add_el.
    have /andP[ab0 ab1] := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ (a `/\ b).
    rewrite /= big_ord_recl !big_ord1 /maxr.
    case: ifP; move => h_max.
    * by rewrite addr0; apply IH22.
    * rewrite addrA.
      have -> : (eval_luka B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E - 1 =
                (((eval_luka B + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1 by lra.
      by rewrite IH12.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case: IHseq_calc_luka2 => [q + IH2].
  rewrite in_cons in_cons =>/orP [/eqP h |/orP [/eqP h | h]].
  +  exists (A |- (a `** b) :: B); first by rewrite mem_head.
    * subst.
      rewrite //= !eval_luka_add_el in IH2.
      rewrite eval_luka_add_el.
      have /andP[ab0 ab1] := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ (a `** b).
      rewrite /= big_ord_recl big_ord1 /maxr.
      case: ifP; move => h_max.
      + rewrite addr0.
        have hh : ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E =
                 (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1)%R.
          by set (e := ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E) in *; lra.
        rewrite hh in h_max. clear hh.
        have hh : eval_luka A <= (((eval_luka B + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1 ->
                  ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 < 0 ->
                  eval_luka A <= eval_luka B -1 by lra.
        by rewrite (hh IH2 h_max).
      + have -> :
             (eval_luka B + ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R))%E - 1 =
              (((eval_luka B + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1 by lra.
         by rewrite IH2.
    * exists (A |- (a `** b) :: B) ; first by rewrite mem_head.
      subst.
      rewrite eval_luka_add_el.
      rewrite /=eval_luka_add_el/= addr0 in IH2.
      have /andP[] := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ (a `** b).
      by lra.
  + by exists q=> //; rewrite in_cons h orbT.
- move: IHseq_calc_luka => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + subst.
    exists ((`~ a) :: A |- B).
    rewrite mem_head; split; rewrite//=.
    rewrite //= !eval_luka_add_el //= addr0 in IH2.
    rewrite eval_luka_add_el//=.
    by lra.
  + by exists q=> //; rewrite in_cons h orbT.
- case: IHseq_calc_luka2 => [q + IH2].
  rewrite in_cons => /predU1P[h | h].
  + subst.
    exists (A |- (`~ a) :: B).
    rewrite mem_head; split; rewrite//=.
    rewrite //= !eval_luka_add_el //= addr0 in IH2.
    rewrite eval_luka_add_el//=.
    by lra.
  + by exists q=> //; rewrite in_cons h orbT.
- move: IHseq_calc_luka2 => [q + IH2].
  rewrite in_cons => /predU1P[h|h].
  + subst.
    rewrite//= !eval_luka_add_el//= addr0 in IH2.
    exists ((a `++ b) :: A |- B); first by rewrite mem_head.
    rewrite eval_luka_add_el//= big_ord_recl big_ord1 /minr.
    case: ifPn => h_min.
    *  have ->// : (eval_luka A + ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz))%E - 1 -1 <=
                 eval_luka B -1 ->
                 (eval_luka A + ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz))%E - 1 <=
                 eval_luka B .
         by intros; lra.
       by lra.
    * rewrite -leNgt in h_min.
      have helper : (((eval_luka A + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1 <= 
                        eval_luka B - 1 ->
                      (((eval_luka A %R )%E)%R)%E <= eval_luka B .
        by intros; lra.
      by apply helper in IH2; lra. 
  + by exists q=> //; rewrite in_cons h orbT.
- case IHseq_calc_luka1 => [q1].
  case IHseq_calc_luka2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
   + subst. 
     exists (A |- (a `++ b) :: B); first by rewrite mem_head. 
     rewrite //= !eval_luka_add_el//= in IH22.
     rewrite //= addr0 in IH22.
     rewrite //= eval_luka_add_el//= big_ord_recl big_ord1 /minr.
     case: ifPn => h_min.
     * have helper : eval_luka A - 1 <= 
                        (((eval_luka B + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1 ->
                      eval_luka A <=
                        (((eval_luka B + ([[a]]_Lukasiewicz)%E)%R + [[b]]_Lukasiewicz))%E - 1.
         by intros; lra.
       apply helper in IH22.
       have really : (eval_luka B + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 =
                     (eval_luka B + ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz))%E - 1 by lra.
       rewrite -really.
       by rewrite IH22.
     * clear IH22.
       lra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- move: IHseq_calc_luka => [q1 + IH2].
  rewrite !in_cons => /predU1P[h1 | /predU1P [h2 | h3]].
  + exists ((a `/\ b) :: B |- A); first by rewrite mem_head.
    subst.
    rewrite //= !eval_luka_add_el in IH2.
    rewrite //= !eval_luka_add_el//=/minR !big_ord_recl big_ord0 /minr.
    by repeat case: ifP; move=> h; lra.
  + exists ((a `/\ b) :: B |- A); first by rewrite mem_head.
    subst.
    rewrite //= !eval_luka_add_el in IH2.
    rewrite //= !eval_luka_add_el//=/minR !big_ord_recl big_ord0 /minr.
    by repeat case: ifP; move=> h; lra.
  + by exists q1 => //; rewrite in_cons h3 orbT.
- case IHseq_calc_luka1 => [q1].
  case IHseq_calc_luka2 => [q2].
  have hB := eval_luka1 B.
  have hA := eval_luka1 A.
  have ha := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ a.
  have hb := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ b.
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + exists (A |- (a `/\ b) :: B); first by rewrite mem_head.
    subst.
    rewrite //= eval_luka_add_el//=/minR !big_ord_recl !big_ord0 /minr.
    rewrite //= !eval_luka_add_el in IH12 IH22.
    by repeat case: ifP; move => h1 h2; lra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case IHseq_calc_luka1 => [q1].
  case IHseq_calc_luka2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + exists ((a `\/ b) :: A |- B); first by rewrite mem_head.
    subst.
    rewrite //= eval_luka_add_el//=/maxR !big_ord_recl big_ord0 /maxr.
    rewrite //= !eval_luka_add_el in IH12 IH22.
    have hb := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ b.
    by repeat case: ifP; move => h1 h2; lra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- move: IHseq_calc_luka => [q1 + IH2].
  have hB := eval_luka1 B.
  have hA := eval_luka1 A.
  have ha := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ a.
  have hb := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ b.
  rewrite !in_cons => /predU1P[h1 | /predU1P [h2 | h3]].
  + exists (A |- (a `\/ b) :: B); first by rewrite mem_head.
    subst.
    rewrite //= !eval_luka_add_el in IH2.
    rewrite //= !eval_luka_add_el//=/maxR !big_ord_recl big_ord0 /maxr.
    by repeat case: ifP; move=> h1 h2; lra.
  + exists (A |- (a `\/ b) :: B); first by rewrite mem_head.
    subst.
    rewrite //= !eval_luka_add_el in IH2.
    rewrite //= !eval_luka_add_el//=/maxR !big_ord_recl big_ord0 /maxr.
    by repeat case: ifP; move=> h1 h2; try lra.
  + by exists q1 => //; rewrite !in_cons h3 !orbT.
Qed.

Lemma luka_neg_impl_admissable (e : formula) :
 [[`~ e]]_Lukasiewicz = [[e `=> ldl_bool _ _ _ _ false]]_Lukasiewicz.
Proof.
rewrite//= addr0 /minr; case: ifPn; intros; first by [].
have h := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ e.
rewrite -leNgt in n.
apply/eqP; rewrite eq_le n andbT.
by lra.
Qed.

Lemma luka_true_false_admissable :
  [[@ldl_bool R neg_def impl_def m_def l_def true]]_Lukasiewicz =
    [[`~ ldl_bool neg_def impl_def m_def l_def false]]_Lukasiewicz.
Proof. by rewrite//= subr0. Qed.

Lemma luka_mand_impl_admissable (a b: formula):
  [[a `** b]]_Lukasiewicz = [[`~ (a `=> `~b)]]_Lukasiewicz.
Proof.
rewrite//=/maxr/minr.
case: ifP; case: ifP; rewrite//= => h1 h2; try lra.
- rewrite !big_ord_recl big_ord0 addr0 in h2.
  have ha := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ a.
  have hb := @translate_boolT_01 R _ p1 Lukasiewicz _ _ _ b.
  have helper1 : ((1 - [[a]]_Lukasiewicz)%R + (1 - [[b]]_Lukasiewicz)%R)%E < 1 ->
                 [[a]]_Lukasiewicz + [[b]]_Lukasiewicz > 1.
    by intros; lra.
  apply helper1 in h1.
  have helper2 : ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E < 0 ->
            [[a]]_Lukasiewicz + [[b]]_Lukasiewicz < 1.
    by intros; lra.
  apply helper2 in h2.
  by lra.
- rewrite !big_ord_recl big_ord0 addr0 in h2.
  rewrite !big_ord_recl big_ord0 addr0.
  have -> : 1 - ((1 - [[a]]_Lukasiewicz)%R + (1 - [[b]]_Lukasiewicz)%R)%E =
                  1 - ((2 - [[a]]_Lukasiewicz - [[b]]_Lukasiewicz)%R)%E by lra.
  have -> : 1 - (2 - [[a]]_Lukasiewicz - [[b]]_Lukasiewicz) =
                   -1 + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz by lra.
  have -> : ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E =
                   ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 by lra.
  by lra.
- rewrite !big_ord_recl big_ord0 addr0 in h2.
  rewrite !big_ord_recl big_ord0 addr0//=.
  have helper3 : ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E =
                   ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 by lra.
  rewrite helper3//=. rewrite helper3 in h2.
  have helper : (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 < 0) = false ->
                ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E  >= 1 by intros; lra.
  apply helper in h2.
  have helper2 : (((1 - [[a]]_Lukasiewicz)%R + (1 - [[b]]_Lukasiewicz)%R)%E < 1) = false ->
                 [[a]]_Lukasiewicz + [[b]]_Lukasiewicz <= 1 by intros; lra.
  apply helper2 in h1.
  by lra.
Qed.

Lemma luka_mor_impl_admissable (a b : formula):
  [[a `++ b]]_Lukasiewicz = [[(`~ a) `=> b]]_Lukasiewicz.
Proof.
rewrite//=/maxr/minr.
have helper : ((1 - (1 - [[a]]_Lukasiewicz))%R + [[b]]_Lukasiewicz)%E =
                   [[a]]_Lukasiewicz + [[b]]_Lukasiewicz by lra.
case: ifPn; case: ifPn; rewrite//= !big_ord_recl big_ord0 ?addr0 => h1 h2.
- by rewrite  helper.
- by rewrite helper h2 in h1.
- rewrite helper.
  apply/eqP; rewrite eq_le !leNgt h2/=.
  by lra.
Qed.

(*specific exchange rules for simpler cases*)
Lemma luka_cat1C Q a :
  seq_calc_luka_impl (a :: Q) =
  seq_calc_luka_impl ([::a] ++ Q).
Proof.
rewrite//=.
Qed.

Lemma luka_catC Q P :
    seq_calc_luka_impl (P ++ Q) ->
    seq_calc_luka_impl (Q ++ P).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
rewrite (hxy _  P Q) in H.
rewrite (hxy _  Q P).
exact/eex_l/H.
Qed.

Lemma luka_exL_nil Q A B C :
    seq_calc_luka_impl (((A ++ B) |- C) :: Q) ->
    seq_calc_luka_impl (((B ++ A) |- C) :: Q).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
rewrite (hxy _  A B) in H.
rewrite (hxy _  B A).
exact/exL_l/H.
Qed.

Lemma luka_exR_nil Q A B C :
    seq_calc_luka_impl ((C |- (A ++ B)) :: Q) ->
    seq_calc_luka_impl ((C |- (B ++ A)) :: Q).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
rewrite (hxy _  A B) in H.
rewrite (hxy _  B A).
exact/exR_l/H.
Qed.

(*an alternate derivable implication rule, derivable*)
Lemma luka_implL_extended Q A B (a b : formula):
    seq_calc_luka_impl ((B |- A) :: (b :: B |- a :: A) :: Q ) ->
    seq_calc_luka_impl (((a `=> b) :: B |- A) :: Q).
Proof.
move => H. rewrite luka_cat1C.
apply luka_catC.
apply ec_l.
rewrite -(cat1s (a `=> b) B).
apply luka_catC.
apply luka_exL_nil.
apply w_l.
rewrite -(cat1s _ Q) -cat1s.
apply luka_catC. 
rewrite -catA.
apply (@luka_catC _ (Q ++ [:: B |- A])).
apply luka_catC.
apply implL_l.
rewrite -cat1s.
move: H.
rewrite -cat1s -(cat1s _ Q) .
move/(@luka_catC ([:: b :: B |- a :: A] ++ Q) _ ).
by rewrite -catA.
Qed.


Lemma equivalence_luka Q:
  seq_calc_luka Q -> seq_calc_luka_impl Q.
Proof.
intros.
dependent induction H.
- exact: id_l.
- exact: empty.
- by apply: eex_l; exact IHseq_calc_luka.
- by apply: ew_l; exact: IHseq_calc_luka.
- by apply: ec_l; exact: IHseq_calc_luka.
- by apply: w_l; exact: IHseq_calc_luka.
- by apply: split_l; exact: IHseq_calc_luka.
- apply: mix_l.
  + exact: IHseq_calc_luka1.
  + exact: IHseq_calc_luka2.
- by apply: exL_l; exact: IHseq_calc_luka.
- by apply: exR_l; exact: IHseq_calc_luka.
- exact: bot_l.
- rewrite true_false_luka neg_impl_luka.
  apply implR_l.
  + rewrite -(cat0s A).
    exact/w_l/empty.
  + exact: bot_l.
- rewrite mand_impl_luka neg_impl_luka.
  apply implL_l. apply implR_l.
  + by exact IHseq_calc_luka2.
  + rewrite neg_impl_luka. apply implR_l.
    * have -> : [:: a, ldl_bool _ _ _ _ false & B] =
                [:: a] ++ (ldl_bool _ _ _ _ false :: B) by [].
      apply/luka_exL_nil/w_l.
      by exact: IHseq_calc_luka2.
    * have -> : [:: b, a, ldl_bool _ _ _ _ false & B] =
                [:: b; a] ++ (ldl_bool _ _ _ _ false :: B) by [].
      apply luka_exL_nil.
      have -> : (ldl_bool _ _ _ _ false :: B) ++ [:: b; a] =
                [::ldl_bool _ _ _ _ false] ++ B ++ [:: b; a] by [].
      rewrite -(cat1s _ A).
      apply: mix_l.
      - by exact: id_l.
      - have <- : [:: b] ++ [:: a] ++ [::] = [:: b; a] by [].
        apply exL_l. rewrite cats0.
        apply (@luka_exL_nil _ ([:: a] ++ [:: b]) B).
        have helper1 : [:: a, b & B] = ([:: a] ++ [:: b]) ++ B by [].
        rewrite helper1 in IHseq_calc_luka1.
        by exact: IHseq_calc_luka1.
- rewrite mand_impl_luka neg_impl_luka.
  apply: implR_l.
  + by exact: IHseq_calc_luka1.
  + apply luka_implL_extended. rewrite neg_impl_luka.
    have -> : [:: A |- ldl_bool _ _ _ _ false :: B,
                     (b `=> ldl_bool _ _ _ _ false) :: A |- [:: a, ldl_bool _ _ _ _ false & B] & Q] =
                    [:: A |- ldl_bool _ _ _ _ false :: B] ++ ((
                       (b `=> ldl_bool _ _ _ _ false) :: A |- [:: a, ldl_bool _ _ _ _ false & B]) :: Q).
      by [].
    apply luka_catC => /=.
    apply luka_implL_extended.
    have -> : [:: A |- [:: a, ldl_bool _ _ _ _ false & B],
                      ldl_bool _ _ _ _ false :: A |- [:: b, a, ldl_bool _ _ _ _ false & B]
      & Q ++ [:: A |- ldl_bool _ _ _ _ false :: B]] =
                     [:: A |- [:: a, ldl_bool _ _ _ _ false & B]] ++
                       (( ldl_bool _ _ _ _ false :: A |- [:: b, a, ldl_bool _ _ _ _ false & B]) ::
      Q ++ [:: A |- ldl_bool _ _ _ _ false :: B]).
      by [].
    apply luka_catC.
    apply ew_l .
    have -> : ldl_bool _ _ _ _ false :: A |- [:: b, a, ldl_bool _ _ _ _ false & B] =
                     ([::ldl_bool _ _ _ _ false] ++ A |- [:: b] ++ [:: a] ++ [:: ldl_bool _ _ _ _ false] ++ B).
      by [].
    apply exR_l. apply(@luka_exR_nil _ ([:: ldl_bool _ _ _ _ false] ++ [:: a] ++ B) ([:: b])).
    have -> : ([:: ldl_bool  _ _ _ _ false] ++ [:: a] ++ B) ++ [:: b] =
              ([:: ldl_bool  _ _ _ _ false]) ++ ([:: a] ++ B ++ [:: b]) by [].
    apply: mix_l.
    * by exact: id_l.
    * rewrite catA. apply luka_exR_nil.
      have -> : [:: b] ++ [:: a] ++ B = [::] ++ [:: b] ++ [:: a] ++ B by [].
      apply exR_l. rewrite//=.
      have -> : (A |- [:: a, b & B]) :: Q ++ [:: A |- ldl_bool  _ _ _ _ false :: B] =
                ([::A |- [:: a, b & B]] ++ Q ++ [:: A |- ldl_bool  _ _ _ _ false :: B] ++ [::]) by [].
      by apply: eex_l; rewrite cats0.
- by rewrite neg_impl_luka; exact/implL_l/IHseq_calc_luka.
- rewrite neg_impl_luka. apply implR_l.
  + by exact: IHseq_calc_luka1.
  + by exact: IHseq_calc_luka2.
- rewrite mor_impl_luka. apply luka_implL_extended.
  rewrite neg_impl_luka.
  have -> : [:: A |- B, b :: A |- (a `=> ldl_bool  _ _ _ _ false) :: B & Q] =
            [:: A |- B] ++ ((b :: A |- (a `=> ldl_bool  _ _ _ _ false) :: B) :: Q) by [].
  apply: luka_catC => /=.
  apply: implR_l.
  + rewrite -(cat1s b A).
    apply/luka_exL_nil/w_l.
    rewrite -(cat1s (A |- B)) catA.
    apply ew_l.
    rewrite -(cat1s (A |- B)).
    by exact: IHseq_calc_luka1.
  + have -> : ([:: a, b & A] |- ldl_bool  _ _ _ _ false :: B) :: Q ++ [:: A |- B] =
              (([:: a, b & A] |- ldl_bool  _ _ _ _ false :: B) :: Q) ++ [:: A |- B] by [].
    apply ew_l.
    by exact: IHseq_calc_luka2.
- rewrite mor_impl_luka. apply implR_l.
  + by exact: IHseq_calc_luka1.
  + rewrite neg_impl_luka. apply implL_l.
    by exact: IHseq_calc_luka2.
- apply andL_l. by exact IHseq_calc_luka.
- apply andR_l.
  + by exact IHseq_calc_luka1.
  + by exact IHseq_calc_luka2.
- apply orL_l.
  + by exact IHseq_calc_luka1.
  + by exact IHseq_calc_luka2.
- apply orR_l. by exact IHseq_calc_luka.
Qed.


End hypersequent_lukasiewicz.

Section hypersequent_product.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Context {K : choiceType}.
Implicit Types (s : seq K).
Variable p : R.
Hypothesis p1 : 1 <= p.
Local Notation "[[ e ]]_ l" := (@translation R l p _ e).

Hypothesis neg_impl_product : neg_impl_dl R.

Hypothesis true_false_product :  true_false_dl R.

Let formula := @expr R (boolT_def impl_def m_def l_def).
Let hypersequent := seq (seq formula * seq formula).

Implicit Type Q P S : hypersequent.
Implicit Type A B C D X Y : seq formula.

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).

(*small-language fragment*)
Inductive seq_calc_product : hypersequent -> Prop :=
| id_p : forall Q A,
    seq_calc_product ((A |- A) :: Q)
| empty_p : forall Q,
    seq_calc_product (([::] |- [::]) :: Q)
(*structural*)
| eex_p : forall Q P S1 S2,
    seq_calc_product (S1 ++ P ++ Q ++ S2) ->
    seq_calc_product (S1 ++ Q ++ P ++ S2)
| ew_p : forall Q P,
    seq_calc_product Q ->
    seq_calc_product (Q ++ P)
| ec_p : forall Q P,
    seq_calc_product (Q ++ P ++ P) ->
    seq_calc_product (Q ++ P)
(*add split and mix rules*)
| split_p : forall Q A B C D,
    seq_calc_product ((A ++ B |- C ++ D) :: Q) ->
    seq_calc_product ((A |- C) :: (B |- D) :: Q)
| mix_p : forall Q A B C D,
    seq_calc_product ((A |- C) :: Q) ->
    seq_calc_product ((B |- D) :: Q) ->
    seq_calc_product ((A ++ B |- C ++ D) :: Q)
| exL_p : forall Q A B C X Y,
    seq_calc_product ((X ++ A ++ B ++ Y |- C) :: Q) ->
    seq_calc_product ((X ++ B ++ A ++ Y |- C) :: Q)
| exR_p : forall Q A B C X Y,
    seq_calc_product ((C |- X ++ A ++ B ++ Y) :: Q) ->
    seq_calc_product ((C |- X ++ B ++ A ++ Y) :: Q)
| w_p : forall Q A B C,
    seq_calc_product ((A |- B) :: Q) ->
    seq_calc_product ((A ++ C |- B) :: Q)
(*logical*)
| bot_p : forall Q A B (b : formula),
    seq_calc_product (((ldl_bool _ _ _ _ false :: A) |- B) :: Q)
| mandL_p : forall Q A B (a b : formula),
    seq_calc_product ((a :: b :: B |- A) :: Q ) ->
    seq_calc_product ((((a `** b) :: B) |- A) :: Q )
| mandR_p : forall Q A B (a b : formula),
    seq_calc_product ( (A |- a :: b ::B) :: Q ) ->
    seq_calc_product ((A |- (a `** b):: B ) :: Q )
| negL_p : forall Q A B (a : formula),
    seq_calc_product ((B |- [::a]) :: Q) ->
    seq_calc_product ((((`~ a) :: B) |- A) :: Q)
| implR_p : forall Q A B (a b : formula),
    seq_calc_product ((A |- B) :: Q) ->
    seq_calc_product ((a :: A |- b :: B) :: Q ) ->
    seq_calc_product (( A |- (a `=> b) :: B) :: Q )
| implL_p : forall Q A B (a b : formula),
      seq_calc_product (((`~ a) :: A |- B) :: Q) ->
      seq_calc_product ((b :: A |- a :: B) :: Q ) ->
      seq_calc_product (((a `=> b) :: A |-  B) :: Q )
| andL_p : forall Q A B (a b : formula),
    seq_calc_product (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_product ((((a `/\ b) :: B) |- A) :: Q)
| andR_p : forall Q A B (a b : formula),
    seq_calc_product ((A |- a :: B) :: Q ) ->
    seq_calc_product ((A |- b :: B) :: Q) ->
    seq_calc_product ((A |- (a `/\ b):: B) :: Q )
| orL_p : forall  Q A B (a b : formula),
    seq_calc_product (((b :: B) |- A) :: Q) ->
    seq_calc_product (((a :: B) |- A) :: Q) ->
    seq_calc_product (((a `\/ b) :: B |- A) :: Q)
| orR_p : forall Q A B (a b : formula),
    seq_calc_product (( A |- a :: B ) :: ( A |- b :: B) :: Q ) ->
    seq_calc_product (( A |- (a `\/ b):: B ) :: Q).

(*LDL language*)
Inductive seq_calc_product' : hypersequent -> Prop :=
| id_p' : forall Q A,
    seq_calc_product' ((A |- A) :: Q)
| empty_p' : forall Q,
     seq_calc_product' (([::] |- [::]) :: Q)
(*structural*)
| eex_p' : forall Q P S1 S2,
    seq_calc_product' (S1 ++ P ++ Q ++ S2) ->
    seq_calc_product' (S1 ++ Q ++ P ++ S2)
| ew_p' : forall Q P,
    seq_calc_product' Q ->
    seq_calc_product' (Q ++ P)
| ec_p' : forall Q P,
    seq_calc_product' (Q ++ P ++ P) ->
    seq_calc_product' (Q ++ P)
(*add split and mix rules*)
| split_p' : forall Q A B C D,
    seq_calc_product' ((A ++ B |- C ++ D) :: Q) ->
    seq_calc_product' ((A |- C) :: (B |- D) :: Q)
| mix_p' : forall  Q A B C D,
    seq_calc_product' ((A |- C) :: Q) ->
    seq_calc_product' ((B |- D) :: Q) ->
    seq_calc_product' ((A ++ B |- (C ++ D)) :: Q)
| exL_p' : forall  Q A B C X Y ,
    seq_calc_product' ((X ++ A ++ B ++ Y |- C) :: Q) ->
    seq_calc_product' ((X ++ B ++ A ++ Y |- C) :: Q)
| exR_p' : forall Q A B C X Y,
    seq_calc_product' ((C |- X ++ A ++ B ++ Y) :: Q) ->
    seq_calc_product' ((C |- X ++ B ++ A ++ Y) :: Q)
| w_p' : forall Q A B C,
    seq_calc_product' ((A |- B) :: Q) ->
    seq_calc_product' ((A ++ C |- B) :: Q)
(*logical*)
| bot_p' : forall Q A B (b : formula),
    seq_calc_product' (((ldl_bool _ _ _ _ false :: A) |- B) :: Q)
| top_p' : forall Q A,
   seq_calc_product' ((A |- [:: (ldl_bool _ _ _ _ true)]) :: Q)
| mandL_p' : forall Q A B (a b : formula),
    seq_calc_product' (((a :: b :: B) |- A) :: Q ) ->
    seq_calc_product' ((((a `** b) :: B) |- A) :: Q )
| mandR_p' : forall Q A B (a b : formula),
    seq_calc_product' ( (A |- a :: b ::B) :: Q ) ->
    seq_calc_product' ((A |- (a `** b):: B ) :: Q )
| negR_p' : forall Q A B (a : formula),
    seq_calc_product' ((A |- B) :: Q) ->
    seq_calc_product' ((a :: A |- ldl_bool _ _ _ _ false :: B) :: Q) ->
    seq_calc_product' ((A |- (`~ a) :: B) :: Q)
| negL_p' : forall Q A B (a : formula),
    seq_calc_product' ((B |- [::a]) :: Q) ->
    seq_calc_product' ((((`~a) :: B) |- A) :: Q)
| andL_p' : forall Q A B (a b : formula),
    seq_calc_product' (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_product' ((((a `/\ b) :: B) |- A) :: Q)
| andR_p' : forall Q A B (a b : formula),
    seq_calc_product' ((A |- a :: B) :: Q ) ->
    seq_calc_product' ((A |- b :: B) :: Q) ->
    seq_calc_product' ((A |- (a `/\ b):: B) :: Q )
| orL_p' : forall  Q A B (a b : formula),
    seq_calc_product' (((b :: B) |- A) :: Q) ->
    seq_calc_product' (((a :: B) |- A) :: Q) ->
    seq_calc_product' (((a `\/ b) :: B |- A) :: Q)
| orR_p' : forall Q A B (a b : formula),
    seq_calc_product' ((A |- a :: B ) :: ( A |- b :: B) :: Q ) ->
    seq_calc_product' ((A |- (a `\/ b):: B ) :: Q).

Definition eval_product A := \prod_(i <- A) [[i]]_product.

Lemma eval_product_add A B  :
  eval_product (A ++ B) = eval_product A * eval_product B.
Proof. by rewrite /eval_product//= big_cat unlock. Qed.

Lemma eval_product_add_el A q :
  eval_product (q :: A) = ([[q]]_product) * eval_product A.
Proof. by rewrite /eval_product//= big_cons. Qed.

Lemma eval_product_01 A : 0 <= eval_product A <= 1.
Proof.
rewrite /eval_product; elim: A => [|a l /andP[? ?]].
- by rewrite big_nil lexx andbT.
- have /andP[? ?] := @translate_boolT_01 R _ p1 product _ _ _ a.
  by rewrite big_cons mulr_ge0//= mulr_ile1.
Qed.

Lemma eval_product_ge0 A : 0 <= eval_product A.
Proof. by have /andP[] := eval_product_01 A. Qed.

Lemma eval_product_le1 A : eval_product A <= 1.
Proof. by have /andP[] := eval_product_01 A. Qed.

Lemma sound_product Q : seq_calc_product Q ->
  exists2 q : seq formula * seq formula,
  q \in Q & eval_product q.1 <= eval_product q.2.
Proof.
intros; rewrite//=. dependent induction H.
- by exists (A |- A) => //; rewrite mem_head.
- by exists ([::] |- [::]).
- case: IHseq_calc_product => [M].
  rewrite !mem_cat => IH1 IH2.
  exists M => //.
  rewrite !mem_cat.
  move/orP: IH1 => [->// |/orP].
  case => [-> |]; first by rewrite !orbT.
  by move/orP => [|] ->; rewrite ?(orTb,orbT).
- case: IHseq_calc_product => [q IH1 IH2].
  by exists q => //; rewrite mem_cat IH1 orTb.
- case IHseq_calc_product => [M + IH2].
  rewrite !mem_cat => /orP[h |/orP[h|h]];
  by exists M; rewrite ?mem_cat ?h ?orTb ?orbT.
- case: IHseq_calc_product => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst q1.
    rewrite /= !eval_product_add in IH2.
    have /orP[h|h] := le_total (eval_product A) (eval_product C).
    * by exists (A |- C); [rewrite mem_head|rewrite h].
    * have := eval_product_ge0 A; rewrite le_eqVlt => /predU1P[ha'|ha'].
      + exists (A |- C) => /=; first by rewrite mem_head.
        by rewrite -ha' eval_product_ge0.
      + exists (B |- D); first by rewrite /= !in_cons eqxx orTb orbT.
        have : eval_product A * eval_product B <= eval_product A * eval_product D.
          by rewrite (le_trans IH2)// ler_wpM2r// eval_product_ge0.
        by rewrite ler_pM2l.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case IHseq_calc_product1 => [q1].
  case IHseq_calc_product2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + exists (A ++ B |- C ++ D); subst; first by rewrite in_cons eqxx orTb.
    rewrite //= in IH12 IH22.
    by rewrite /= !eval_product_add ler_pM// eval_product_ge0.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case: IHseq_calc_product => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst. exists ((X ++ B ++ A ++ Y |- C)); first by rewrite mem_head.
    rewrite//= !eval_product_add in IH2.
    rewrite//= !eval_product_add.
    by rewrite (mulrCA (eval_product B)).
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case: IHseq_calc_product => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst. exists (C |- X ++ B ++ A ++ Y); first by rewrite mem_head.
    rewrite//= !eval_product_add in IH2.
    rewrite//= !eval_product_add.
    by rewrite (mulrCA (eval_product B)).
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case: IHseq_calc_product => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + exists (A ++ C |- B); subst; rewrite //= in IH2.
    * by rewrite in_cons eq_refl orTb.
    * rewrite //= eval_product_add.
      rewrite (le_trans _ IH2)//.
      by rewrite ler_piMr ?eval_product_ge0 ?eval_product_le1.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- exists (ldl_bool _ _ _ _ false :: A |- B).
  + by rewrite in_cons eq_refl orTb.
  + rewrite//= /eval_product big_cons//= mul0r.
    have h := eval_product_01 B. rewrite /eval_product in h.
    have helper : forall (x : R), 0 <= x <= 1 -> 0 <= x /\ x <= 1 by intros; lra.
    apply helper in h. case h => [h1 _].
    by rewrite h1.
- case: IHseq_calc_product => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst.
    exists ((a `** b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite /= /eval_product !big_cons//= mulrA in IH2.
    rewrite /= /eval_product !big_cons//= !big_ord_recl big_ord0 mulr1.
    by exact IH2.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case: IHseq_calc_product => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst.
    exists (A |- (a `** b) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite//= /eval_product !big_cons//= mulrA in IH2.
    rewrite//= /eval_product !big_cons/= !big_ord_recl !big_ord0/= !tnthS !tnth0 mulr1.
    by exact IH2.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case: IHseq_calc_product => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst.
    exists ((`~ a) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons big_nil mulr1 //= in IH2.
    rewrite//= /eval_product  !big_cons//=.
    case: ifP; intros; rewrite//=.
    * by rewrite mul0r eval_product_ge0.
    * rewrite mul1r.
      have := @translate_boolT_01 R _ p1 product _ _ _ a.
      rewrite le_eqVlt n orbF => /andP[/eqP/esym a0{n} a1].
      by rewrite (le_trans IH2)// a0 eval_product_ge0.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case IHseq_calc_product1 => [q1].
  case IHseq_calc_product2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + subst q1 q2.
    exists (A |- (a `=> b) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite /= /eval_product //= in IH22.
    rewrite /= !eval_product_add_el in IH12.
    rewrite//= !eval_product_add_el//=.
    case: ifPn => [ba|ba].
    * have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
      have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
      case/andP : ha => /[swap] ha1; rewrite le_eqVlt => -/predU1P[ha'|ha'].
      - move: ba.
        by rewrite -ha' ltNge; case/andP : hb => ->//.
      - by rewrite mulrC mulrA ler_pdivlMr// !(mulrC (eval_product _)).
    * by rewrite mul1r.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case IHseq_calc_product1 => [q1].
  case IHseq_calc_product2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + subst q1 q2.
    exists ((a `=> b) :: A |- B); first by rewrite in_cons eq_refl orTb.
    rewrite /= !eval_product_add_el //= in IH12 IH22.
    rewrite /= !eval_product_add_el//=.
    have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
    move: IH12; case: ifPn; case: ifPn => ba a0 AB.
    * by rewrite mulrC mulrA ler_pdivrMr// !(mulrC (eval_product _)).
    * rewrite mul1r//= {AB}.
      rewrite -leNgt in ba.
      by rewrite -(ler_pM2l a0) (le_trans _ IH22)// ler_wpM2r// eval_product_ge0.
    * move/andP : hb => [+ _] => /le_lt_trans /(_ ba).
      by rewrite (negbTE a0).
    * rewrite mul1r//.
      by rewrite mul1r//= in AB.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- move: IHseq_calc_product => [q1 + IH2].
  rewrite !in_cons => /predU1P[h1 | /predU1P [h2 | h3]].
  + subst.
    exists ((a `/\ b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons//= /minR !big_ord_recl big_ord0 /minr.
    rewrite//= /eval_product !big_cons  in IH2.
    repeat case: ifP; move=> h1 h2; try nra.
    * have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
      have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
      have hB := eval_product_01 B. rewrite /eval_product in hB.
      rewrite (le_trans _ IH2)// ler_wpM2r//.
        by case/andP : hB.
      by rewrite leNgt h2.
    * rewrite mul1r.
      have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
      have {}h2 : [[a]]_product = 1.
        apply/eqP; rewrite eq_le.
        case/andP : ha => _ ->/=.
        by rewrite leNgt h2.
      by move: IH2; rewrite h2 mul1r.
  + subst q1.
    exists ((a `/\ b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons//= /minR !big_ord_recl big_ord0 /minr.
    rewrite//= /eval_product !big_cons in IH2.
    repeat case: ifP; move=> h1 h2; try nra.
    * have hB := eval_product_01 B.
      rewrite /eval_product in hB.
      rewrite (le_trans _ IH2)// ler_wpM2r//.
        by case/andP : hB.
      by rewrite ltW.
    * have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
      have hB := eval_product_01 B.
      rewrite /eval_product in hB.
      rewrite (le_trans _ IH2)// ler_wpM2r//.
        by case/andP : hB.
      have {}h1 : [[b]]_product = 1.
        apply/eqP; rewrite eq_le.
        case/andP : hb => _ ->/=.
        by rewrite leNgt h1.
      by rewrite h1 ltW.
    * have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
      have hB := eval_product_01 B.
      rewrite /eval_product in hB.
      have {}h1 : [[b]]_product = 1.
        apply/eqP; rewrite eq_le.
        case/andP : hb => _ ->/=.
        by rewrite leNgt h1.
      by rewrite mul1r (le_trans _ IH2)// h1 mul1r.
  + by exists q1 => //; rewrite !in_cons h3 !orbT.
- case IHseq_calc_product1 => [q1].
  case IHseq_calc_product2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + subst.
    exists (A |- (a `/\ b) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite //= !eval_product_add_el //= in IH12 IH22.
    rewrite//= !eval_product_add_el//= /minR !big_ord_recl big_ord0 /minr.
    have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
    have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
    have hB := eval_product_01 B.
    by repeat case: ifP; move=> h1 h2; nra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case IHseq_calc_product1 => [q1].
  case IHseq_calc_product2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + subst.
    exists ((a `\/ b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite /= !eval_product_add_el //= in IH12 IH22.
    rewrite /= !eval_product_add_el//= /maxR !big_ord_recl big_ord0 /maxr.
    have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
    have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
    have hB := eval_product_01 B.
    have hA := eval_product_01 A.
    by repeat case: ifP; move=> h1 h2; nra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- move: IHseq_calc_product => [q1 + IH2].
  rewrite !in_cons => /predU1P[h1 | /predU1P [h2 | h3]].
  + subst.
    exists (A |- (a `\/ b) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons//= /maxR !big_ord_recl big_ord0 /maxr.
    rewrite//= /eval_product !big_cons in IH2.
    have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
    have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
    have hB := eval_product_01 B.
    have hA := eval_product_01 A.
    rewrite /eval_product in hB hA.
    by repeat case: ifP; move=> h1 h2; nra.
  + subst.
    exists (A |- (a `\/ b) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons//= /maxR !big_ord_recl big_ord0 /maxr.
    rewrite//= /eval_product !big_cons in IH2.
    have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
    have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
    have hB := eval_product_01 B.
    have hA := eval_product_01 A.
    rewrite /eval_product in hB hA.
    by repeat case: ifP; move=> h1 h2; nra.
  + by exists q1 => //; rewrite !in_cons h3 !orbT.
Qed.

Lemma sound_product' Q : seq_calc_product' Q ->
  exists2 q : seq formula * seq formula,
    q \in Q & (eval_product (fst q) <= eval_product (snd q)).
Proof.
intros; rewrite//=. dependent induction H.
- by exists (A |- A) => //; rewrite mem_head.
- by exists ([::] |- [::]).
- case: IHseq_calc_product' => [M].
  rewrite !mem_cat => IH1 IH2.
  exists M => //.
  rewrite !mem_cat.
  move/orP: IH1 => [->// |/orP].
  case => [-> |]; first by rewrite !orbT.
  by move/orP => [|] ->; rewrite ?(orTb,orbT).
- case: IHseq_calc_product' => [q IH1 IH2].
  by exists q => //; rewrite mem_cat IH1 orTb.
- case IHseq_calc_product' => [M + IH2].
  rewrite !mem_cat; move/orP => [h |/orP [h | h]];
  by exists M; rewrite ?mem_cat ?h ?orTb ?orbT//=.
- case: IHseq_calc_product' => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst.
    rewrite //= !eval_product_add in IH2.
    have ha := eval_product_01 A.
    have hb := eval_product_01 B.
    have hc := eval_product_01 C.
    have hd := eval_product_01 D.
    have /orP[h|h] := le_total (eval_product A) (eval_product C).
    * exists (A |- C); first by rewrite //= mem_head.
      by rewrite h.
    * have helper : eval_product A * eval_product B <=
                    eval_product A * eval_product D by nra.
      have helper1 (a b d : R) : a * b <= a * d ->
                                           0 < a ->
                                           b <= d by intros; nra.
      have [ha'|ha']:  0 < eval_product A \/ 0 = eval_product A by lra.
      + exists (B |- D); first  by rewrite //= !in_cons eq_refl orTb orbT.
        apply (helper1 _ _ _ helper) in ha'.
        by rewrite//=.
      + exists (A |- C); first by rewrite //= mem_head.
        by lra.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case IHseq_calc_product'1 => [q1].
  case IHseq_calc_product'2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + exists (A ++ B |- C ++ D); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= !eval_product_add.
    rewrite //= in IH12 IH22.
    have le_mul : forall ( a b c :R ),  0 <= a -> 0 <= b -> a <= c ->
                                        b <=1 -> a * b <= c * b by intros; nra.
    have /andP[ha0 ha1] := eval_product_01 A.
    have /andP[hb0 hb1] := eval_product_01 B.
    have /andP[hc0 hc1] := eval_product_01 C.
    have /andP[hd0 hd1] := eval_product_01 D.
    apply (le_mul _ _ (eval_product C) ha0 hb0) in IH22; last by exact hb1.
    have le_le : forall (a b c d : R),  0 <= a -> 0 <= b -> 0 <= c -> 0 <= d ->
                                        a* b <= c * b -> b <= d -> a * b <= c * d by intros; nra.
    apply (le_le (eval_product A) (eval_product B) (eval_product C)
             (eval_product D) ha0 hb0 hc0 hd0) in IH22;  last by exact IH12.
    by exact IH22.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case: IHseq_calc_product' => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst. exists ((X ++ B ++ A ++ Y |- C)); first by rewrite mem_head.
    rewrite//= !eval_product_add in IH2.
    rewrite//= !eval_product_add.
    by lra.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case: IHseq_calc_product' => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst. exists (C |- X ++ B ++ A ++ Y); first by rewrite mem_head.
    rewrite//= !eval_product_add in IH2.
    rewrite//= !eval_product_add.
    by rewrite (mulrCA (eval_product B)).
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case: IHseq_calc_product' => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + exists (A ++ C |- B); subst; rewrite //= in IH2.
    * by rewrite in_cons eq_refl orTb.
    * rewrite //= eval_product_add.
      by rewrite (le_trans _ IH2)// ler_piMr ?eval_product_ge0 ?eval_product_le1.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- exists (ldl_bool _ _ _ _ false :: A |- B).
  + by rewrite in_cons eq_refl orTb.
  + rewrite//= /eval_product big_cons//= mul0r.
    have h := eval_product_01 B. rewrite /eval_product in h.
    have helper : forall (x : R), 0 <= x <= 1 -> 0 <= x /\ x <= 1 by intros; lra.
    apply helper in h. case h => [h1 _].
    by rewrite h1.
- exists (A |- [:: ldl_bool _ _ _ _ true]).
  + by rewrite in_cons eq_refl orTb.
  + rewrite//= /eval_product big_cons//= mul1r big_nil.
    by have /andP[] := eval_product_01 A.
- case: IHseq_calc_product' => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst.
    exists ((a `** b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite /= /eval_product !big_cons//= mulrA in IH2.
    rewrite /= /eval_product !big_cons//= !big_ord_recl big_ord0 mulr1.
    by exact IH2.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case: IHseq_calc_product' => [q1 + IH2].
  rewrite in_cons => /predU1P[h1|h2].
  + subst.
    exists (A |- (a `** b) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite//= /eval_product !big_cons//= mulrA in IH2.
    rewrite//= /eval_product !big_cons//= !big_ord_recl big_ord0 mulr1.
    by exact IH2.
  + by exists q1 => //; rewrite !in_cons h2 !orbT.
- case IHseq_calc_product'1 => [q1].
  case IHseq_calc_product'2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + subst.
    exists (A |- (`~ a) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite //= !eval_product_add_el//= mul0r in IH22.
    rewrite //= in IH12.
    rewrite//= eval_product_add_el//=.
    by case: ifPn; intros; rewrite ?(mul0r,mul1r)//; nra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- move: IHseq_calc_product' => [q1 + IH2].
  rewrite in_cons => /predU1P[IH1 | IH1].
  + subst.
    exists ((`~ a) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons big_nil mulr1 //= in IH2.
    rewrite//= /eval_product !big_cons//=.
    case: ifPn; intros; rewrite//=.
    * rewrite mul0r.
      by have /andP[] := eval_product_01 A.
    * rewrite mul1r.
      have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
      have hb : forall (x : R),  ~~ (0 < x) ->
                 0 <= x <= 1 ->
                 0 = x by intros; lra.
      apply (hb _  n) in ha.
      rewrite -ha in IH2.
      have hA := eval_product_01 A. rewrite /eval_product in hA.
      have helper : \prod_(i <- B) [[i]]_product <= 0 ->
                    0 <= \prod_(i <- A) [[i]]_product <= 1 ->
                    \prod_(i <- B) [[i]]_product <= \prod_(i <- A) [[i]]_product by intros; lra.
      by apply (helper IH2) in hA; exact hA.
  + by exists q1 => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_product' => [q1 + IH2].
  rewrite !in_cons => /predU1P[h1 | /predU1P [h2 | h3]].
  + subst.
    exists ((a `/\ b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons//= /minR !big_ord_recl big_ord0 /minr.
    rewrite//= /eval_product !big_cons in IH2.
    repeat case: ifP; move=> h1 h2; try nra.
    * have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
      have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
      have hB := eval_product_01 B. rewrite /eval_product in hB.
      have lelt : ([[a]]_product < [[b]]_product) = false <->
                    [[b]]_product <= [[a]]_product by split; intros; lra.
      apply lelt in h2.
      have hA' : [[b]]_product * \prod_(j <- B) [[j]]_product <= \prod_(i <- A) [[i]]_product
        by intros; nra.
      by exact hA'.
    * rewrite mul1r.
      have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
      have ha1 : forall (x : R),  (x < 1) = false ->
                 0 <= x <= 1 ->
                 x = 1 by intros; lra.
      apply (ha1 _ h2) in ha; rewrite//=.
      rewrite ha mul1r in IH2.
      by exact IH2.
  + subst.
    exists ((a `/\ b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons//= /minR !big_ord_recl big_ord0 /minr.
    rewrite//= /eval_product !big_cons in IH2.
    repeat case: ifP; move=> h1 h2; try nra.
    * have hB := eval_product_01 B. rewrite /eval_product in hB.
      have h' : [[a]]_product * \prod_(j <- B) [[j]]_product <= \prod_(i <- A) [[i]]_product
        by intros; nra.
      by exact h'.
    * have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
      have hB := eval_product_01 B. rewrite /eval_product in hB.
      have hb1 : forall (x : R),  (x < 1) = false ->
                 0 <= x <= 1 ->
                 x = 1 by  intros; lra.
      apply (hb1 _ h1) in hb; rewrite//=.
      rewrite hb mul1r in IH2.
      by nra.
    * rewrite mul1r.
      have hb := @translate_boolT_01 R p p1 product _ _ _ (b).
      have hB := eval_product_01 B. rewrite /eval_product in hB.
      by nra.
  + by exists q1 => //; rewrite !in_cons h3 !orbT.
- case IHseq_calc_product'1 => [q1].
  case IHseq_calc_product'2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + subst.
    exists (A |- (a `/\ b) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite //= !eval_product_add_el //= in IH12 IH22.
    rewrite//= !eval_product_add_el//= /minR !big_ord_recl big_ord0 /minr.
    have ha := @translate_boolT_01 R _ p1 product _ _ _ a.
    have hb := @translate_boolT_01 R _ p1 product _ _ _ b.
    have hB := eval_product_01 B.
    have hA := eval_product_01 A.
    by repeat case: ifP; move=> h1 h2; nra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT.
- case IHseq_calc_product'1 => [q1].
  case IHseq_calc_product'2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + subst.
    exists ((a `\/ b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite //= !eval_product_add_el //= in IH12 IH22.
    rewrite//= !eval_product_add_el//= /maxR !big_ord_recl big_ord0 /maxr.
    have ha := @translate_boolT_01 R p p1 product _ _ _ (a).
    have hb := @translate_boolT_01 R p p1 product _ _ _ (b).
    have hB := eval_product_01 B.
    have hA := eval_product_01 A.
    by repeat case: ifP; move=> h1 h2; nra.
  + by exists q1 => //; rewrite in_cons h1 orbT.
  + by exists q2 => //; rewrite in_cons h2 orbT.
  + by exists q1 => //; rewrite in_cons h1 orbT. 
- move: IHseq_calc_product' => [q1 + IH2].
  rewrite !in_cons => /predU1P[h1 | /predU1P [h2 | h3]].
  + subst.
    exists (A |- (a `\/ b) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons//= /maxR !big_ord_recl big_ord0 /maxr. 
    rewrite//= /eval_product !big_cons in IH2. 
    have ha := @translate_boolT_01 R p p1 product _ _ _ (a).
    have hb := @translate_boolT_01 R p p1 product _ _ _ (b).
    have hB := eval_product_01 B. 
    have hA := eval_product_01 A.
    rewrite /eval_product in hB hA.
    by repeat case: ifP; move=> h1 h2; nra.
  + subst.
    exists (A |- (a `\/ b) :: B); first by rewrite in_cons eq_refl orTb.
    rewrite //= /eval_product !big_cons//= /maxR !big_ord_recl big_ord0 /maxr. 
    rewrite//= /eval_product !big_cons in IH2. 
    have ha := @translate_boolT_01 R p p1 product _ _ _ (a).
    have hb := @translate_boolT_01 R p p1 product _ _ _ (b).
    have hB := eval_product_01 B. 
    have hA := eval_product_01 A.
    rewrite /eval_product in hB hA.
    by repeat case: ifP; move=> h1 h2; nra.
  + by exists q1 => //; rewrite !in_cons h3 !orbT. 
Qed.

Lemma product_true_false_admissable :
  [[@ldl_bool R neg_def impl_def m_def l_def true]]_product =
    [[`~ ldl_bool neg_def impl_def m_def l_def false]]_product.
Proof. by rewrite//=; case: ifP; intros; lra. Qed.

Lemma product_neg_impl_admissable (e : formula):
 [[`~ e]]_product = [[e `=> ldl_bool _ _ _ _  false]]_product.
Proof.
rewrite//=. repeat case: ifP; intros; by rewrite ?mul0r//=.
Qed.

Lemma equivalence_product Q:
  seq_calc_product' Q -> seq_calc_product Q.
Proof.
intros.
dependent induction H. 
- apply id_p.
- apply empty_p.
- apply eex_p. by exact IHseq_calc_product'.
- apply ew_p. by exact IHseq_calc_product'.
- apply ec_p. by exact IHseq_calc_product'.
- apply split_p. by exact IHseq_calc_product'.
- apply mix_p. 
  + by exact IHseq_calc_product'1.
  + by exact IHseq_calc_product'2. 
- apply exL_p. by exact IHseq_calc_product'.
- apply exR_p. by exact IHseq_calc_product'.
- apply w_p. by exact IHseq_calc_product'.
- by apply bot_p.
- rewrite true_false_product neg_impl_product. apply implR_p. 
  + have h : [::] ++ A = A by [].
    rewrite -h. 
    apply w_p. apply empty_p.
  + have h : ldl_bool _ _ _ _ false :: A = [::ldl_bool _ _ _ _ false] ++ A.
      by [].
    rewrite h . apply w_p. apply id_p.
- apply mandL_p. by exact IHseq_calc_product'.
- apply mandR_p. by exact IHseq_calc_product'.
- rewrite neg_impl_product. apply implR_p; rewrite//=. 
- apply negL_p. by exact IHseq_calc_product'.
- apply andL_p. by exact IHseq_calc_product'.
- apply andR_p. 
  + by exact IHseq_calc_product'1. 
  + by exact IHseq_calc_product'2.
- apply orL_p. 
  + by exact IHseq_calc_product'1. 
  + by exact IHseq_calc_product'2.
- apply orR_p. by exact IHseq_calc_product'.
Qed.

End hypersequent_product.

Section hypersequent_godel.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Context {K : choiceType}.
Implicit Types (s : seq K).
Variable p : R.
Hypothesis p1 : 1 <= p.
Local Notation "[[ e ]]_ l" := (@translation R l p _ e).

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).
(*entailment as pair (A, B) where A |- B*)

Let formula := @expr R (boolT_def impl_def m_def l_def).
Let hypersequent := seq (seq formula * seq formula).

Implicit Type Q P S : hypersequent.
Implicit Type A B C D X Y : seq formula.

Hypothesis neg_impl_godel : neg_impl_dl R.

(*hypersequent calculus as per literature*)
Inductive seq_calc_godel :  hypersequent
      -> Prop :=
| id_g : forall Q (a : formula),
    seq_calc_godel ( ([::a] |- [::a]) :: Q)
(*structural*)
| eex_g : forall Q P S1 S2,
    seq_calc_godel (S1 ++ P ++ Q ++ S2) ->
    seq_calc_godel (S1 ++ Q ++ P ++ S2)
| ew_g : forall Q P,
    seq_calc_godel Q ->
    seq_calc_godel (Q ++ P)
| ec_g : forall Q P,
    seq_calc_godel (Q ++ P ++ P) ->
    seq_calc_godel (Q ++ P)
| comm_hyper_g : forall Q A1 A2 B1 B2 C D,
    seq_calc_godel ((A1 ++ B1 |- C) :: Q) ->
    seq_calc_godel ((A2 ++ B2 |- D) :: Q) ->
    seq_calc_godel ((A1 ++ A2 |- C) :: ((B1 ++ B2) |- D) :: Q)
| comm_g : forall Q A B C,
    seq_calc_godel (((A ++ B ++ B) |- C) :: Q) ->
    seq_calc_godel (((A ++ B) |- C) :: Q)
| weak_g : forall Q A B C,
    seq_calc_godel ((A |- C) :: Q ) ->
    seq_calc_godel (((A ++ B) |- C) :: Q )
| exL_g : forall Q A B C X Y,
    seq_calc_godel ((X ++ A ++ B ++ Y |- C) :: Q) ->
    seq_calc_godel ((X ++ B ++ A ++ Y |- C) :: Q)
| exR_g : forall Q A B C X Y,
    seq_calc_godel ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_godel ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
| bot_g : forall Q A B,
    seq_calc_godel (((ldl_bool _ _ _ _ false :: A) |- B) :: Q)
| top_g : forall Q A,
    seq_calc_godel ((A |- [::ldl_bool _ _ _ _ true]) :: Q )
| andL_g : forall Q A B (a b : formula),
    seq_calc_godel (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_godel ((((a `/\ b) :: B) |- A) :: Q) 
| andR_g : forall Q A (a b : formula),
    seq_calc_godel ( (A |- [:: a]) :: Q ) ->
    seq_calc_godel ( (A |- [:: b]) :: Q) ->
    seq_calc_godel ((A |- [:: (a `/\ b)]) :: Q )
| orL_g : forall  Q A B (a b : formula),
    seq_calc_godel ( ((b :: B) |- A) :: Q) ->
    seq_calc_godel ( ((a :: B) |- A) :: Q) ->
    seq_calc_godel (((a `\/ b) :: B |- A) :: Q)
| orR_g : forall Q A (a b : formula),
    seq_calc_godel (( A |- [::a] ) :: ( A |- [::b]) :: Q ) ->
    seq_calc_godel (( A |- [::(a `\/ b)] ) :: Q) 
| implR_g : forall Q A B (a b : formula),
    seq_calc_godel ((a :: A |- [::b]) :: Q) ->
    seq_calc_godel ((A |- [:: (a `=> b)]) :: Q)
| implL_g : forall Q A1 A2 B (a b: formula),
    seq_calc_godel ((A1 |- [:: a]) :: Q) ->
    seq_calc_godel ((b :: A2 |- B) :: Q) ->
    seq_calc_godel (( (a `=> b) :: A1 ++ A2 |- B) :: Q).

Inductive seq_calc_godel' : hypersequent -> Prop :=
| id_g' : forall Q (a : formula),
    seq_calc_godel' ( ([::a] |- [::a]) :: Q)
(*structural*)
| eex_g' : forall Q P S1 S2,
    seq_calc_godel' (S1 ++ P ++ Q ++ S2) ->
    seq_calc_godel' (S1 ++ Q ++ P ++ S2)
| ew_g' : forall Q P,
    seq_calc_godel' Q ->
    seq_calc_godel' (Q ++ P)
| ec_g' : forall Q P,
    seq_calc_godel' (Q ++ P ++ P) ->
    seq_calc_godel' (Q ++ P)
| comm_hyper_g' : forall Q A1 A2 B1 B2 C D,
    seq_calc_godel' (((A1 ++ B1) |- C) :: Q) ->
    seq_calc_godel' (((A2 ++ B2) |- D) :: Q) ->
    seq_calc_godel' ( ((A1 ++ A2) |- C) :: ((B1 ++ B2) |- D) :: Q)
| comm_g' : forall Q A B C,
    seq_calc_godel' (((A ++ B ++ B) |- C) :: Q) ->
    seq_calc_godel' (((A ++ B) |- C) :: Q)
| weak_g' : forall Q A B C,
    seq_calc_godel' ((A |- C) :: Q ) ->
    seq_calc_godel' (((A ++ B) |- C) :: Q )
| exL_g' : forall Q A B C X Y,
    seq_calc_godel' (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_godel' (((X ++ B ++ A ++ Y) |- C) :: Q)
| exR_g' : forall Q A B C X Y,
    seq_calc_godel' ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_godel' ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
| bot_g' : forall Q A B,
    seq_calc_godel' (((ldl_bool _ _ _ _ false :: A) |- B) :: Q)
| top_g' : forall Q A,
    seq_calc_godel' ((A |- [::ldl_bool _ _ _ _ true]) :: Q )
| andL_g' : forall Q A B (a b : formula),
    seq_calc_godel' (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_godel' ((((a `/\ b) :: B) |- A) :: Q)
| andR_g' : forall Q A (a b : formula),
    seq_calc_godel' ( (A |- [:: a]) :: Q ) ->
    seq_calc_godel' ( (A |- [:: b]) :: Q) ->
    seq_calc_godel' ((A |- [:: (a `/\ b)]) :: Q )
| orL_g' : forall  Q A B (a b : formula),
    seq_calc_godel' ( ((b :: B) |- A) :: Q) ->
    seq_calc_godel' ( ((a :: B) |- A) :: Q) ->
    seq_calc_godel' (((a `\/ b) :: B |- A) :: Q)
| orR_g' : forall Q A (a b : formula),
    seq_calc_godel' ((A |- [::a] ) :: ( A |- [::b]) :: Q ) ->
    seq_calc_godel' ((A |- [::(a `\/ b)] ) :: Q)
| negR_g : forall Q A (a : formula),
    seq_calc_godel' ((a :: A |- [:: ldl_bool _ _ _ _ false]) :: Q) ->
    seq_calc_godel' ((A |- [:: (`~ a)]) :: Q)
| negL_g : forall Q A1 A2 B (a : formula),
    seq_calc_godel' ((A1 |- [:: a]) :: Q) ->
    seq_calc_godel' (((ldl_bool _ _ _ _ false) :: A2 |- B) :: Q) ->
    seq_calc_godel' (((`~ a) :: A1 ++ A2 |- B) :: Q).

Lemma big_maxr_godel_le1 n (A : 'I_n -> formula) :
   \big[maxr/0]_(j < n) [[A j]]_Godel <= 1.
Proof.
have := @translate_boolT_01 R p p1 Godel _ _ _  (ldl_or A).
rewrite /= /maxR.
by case/andP.
Qed.

Lemma big_minr_godel_le1 n (A : 'I_n -> formula) :
  \big[minr/1]_(j < n) [[A j]]_Godel <= 1.
Proof.
have := @translate_boolT_01 R _ p1 Godel _ _ _  (ldl_and A).
rewrite /= /minR.
by case/andP.
Qed.

Lemma big_maxr_godel_ge0 n (A : 'I_n -> formula) :
   0 <= \big[maxr/0]_(j < n) [[A j]]_Godel .
Proof.
have := @translate_boolT_01 R _ p1 Godel _ _ _  (ldl_or A).
rewrite //= /maxR.
by case/andP.
Qed.

Lemma big_minr_godel_ge0 n (A : 'I_n -> formula) :
   0 <= \big[minr/1]_(j < n) [[A j]]_Godel .
Proof.
have := @translate_boolT_01 R _ p1 Godel _ _ _  (ldl_and A).
by rewrite //= /minR => /andP[].
Qed.

Lemma big_min_cat_godel (A B : seq formula) :
  \big[minr/1]_(j <- A ++ B) [[j]]_Godel =
  minr (\big[minr/1]_(j <- A) [[j]]_Godel) (\big[minr/1]_(j <- B) [[j]]_Godel).
Proof. by apply/big_cat_idem; rewrite /=/minr; case: ifP. Qed.

Lemma big_max_cat_godel A B:
  \big[maxr/0]_(j <- A ++ B) [[j]]_Godel =
  maxr (\big[maxr/0]_(j <- A) [[j]]_Godel) (\big[maxr/0]_(j <- B) [[j]]_Godel).
Proof. by apply/big_cat_idem; rewrite /=/maxr; case: ifP. Qed.

Lemma big_minr_if A B :
  if \big[minr/1]_(j <- A) [[j]]_Godel <= \big[minr/1]_(j <- B) [[j]]_Godel then
    \big[minr/1]_(j <- A ++ B) [[j]]_Godel = \big[minr/1]_(j <- A) [[j]]_Godel
  else
    \big[minr/1]_(j <- A ++ B) [[j]]_Godel = \big[minr/1]_(j <- B) [[j]]_Godel.
Proof.
have H := big_min_cat_godel A B.
rewrite {2}/minr in H. rewrite//=.
move: H. case: ifP;
case: ifPn; intros; rewrite//=; lra.
Qed.

Lemma minr_lt_godel A B C :
  \big[minr/1]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- A) [[j]]_Godel /\
    \big[minr/1]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- B) [[j]]_Godel <->
 (\big[minr/1]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- A ++ B) [[j]]_Godel).
Proof.
split.
- move => [h1 h2].
  have := big_minr_if A B. 
  by case: ifP; move => _ ->.
- move => h.
  have := big_minr_if A B.
  by case: ifP; move => H' H; rewrite H in h; rewrite h; split; first by []; lra.
Qed.

Lemma minr_le_godel A B C :
 (\big[minr/1]_(j <- (A ++ B)) [[j]]_Godel <= \big[minr/1]_(j <- C) [[j]]_Godel) ->
  (\big[minr/1]_(j <- A) [[j]]_Godel <= \big[minr/1]_(j <- B) [[j]]_Godel /\
    \big[minr/1]_(j <- A) [[j]]_Godel <= \big[minr/1]_(j <- C) [[j]]_Godel) \/
    (\big[minr/1]_(j <- B) [[j]]_Godel <= \big[minr/1]_(j <- C) [[j]]_Godel /\
\big[minr/1]_(j <- B) [[j]]_Godel <= \big[minr/1]_(j <- A) [[j]]_Godel).
Proof.
intros. have := big_minr_if A B.
case: ifP; move => h' h.
- by rewrite h in H; left; rewrite H//=.
- by right; rewrite h in H; rewrite H; split; first by []; lra.
Qed.

Lemma minr_maxr_lt_godel A B C:
  \big[maxr/0]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- A) [[j]]_Godel /\
    \big[maxr/0]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- B) [[j]]_Godel <->
 (\big[maxr/0]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- A ++ B) [[j]]_Godel).
Proof.
split.
- move => [h1 h2].
  have := big_minr_if A B.
  by case: ifP; move => _ ->. 
- move => h.
  have := big_minr_if A B.
  by case: ifP; move => H' H; rewrite H in h; rewrite h; split; first by []; lra.
Qed.

Lemma minr_maxr_le_godel A B C :
 (\big[minr/1]_(j <- (A ++ B)) [[j]]_Godel <= \big[maxr/0]_(j <- C) [[j]]_Godel) ->
  (\big[minr/1]_(j <- A) [[j]]_Godel <= \big[minr/1]_(j <- B) [[j]]_Godel /\
    \big[minr/1]_(j <- A) [[j]]_Godel <= \big[maxr/0]_(j <- C) [[j]]_Godel) \/
    (\big[minr/1]_(j <- B) [[j]]_Godel <= \big[maxr/0]_(j <- C) [[j]]_Godel /\
\big[minr/1]_(j <- B) [[j]]_Godel <= \big[minr/1]_(j <- A) [[j]]_Godel).
Proof.
intros. have := big_minr_if A B.
case: ifP; move => h' h.
- by rewrite h in H; left; rewrite H//=.
- by right; rewrite h in H; rewrite H; split; first by []; lra.
Qed.

Lemma sound_godel Q:
  seq_calc_godel Q ->
  exists2 q : (seq formula * seq formula), q \in Q &
(\big[minr/1]_(f <- q.1) translation Godel p f  <=  \big[maxr/0]_(f <- q.2) translation Godel p f).
Proof.
intros; rewrite//=. dependent induction H.
- exists ([:: a] |- [:: a]); first by rewrite //= mem_head.
  by rewrite /minR/maxR !big_cons !big_nil /minr/maxr; repeat case: ifP; lra.
- case: IHseq_calc_godel => [M].
  rewrite !mem_cat => IH1 IH2.
  exists M => //.
  rewrite !mem_cat.
  move/orP: IH1 => [->// |/orP].
  case => [-> |]; first by rewrite !orbT.
  by move/orP => [|] ->; rewrite ?(orTb,orbT).
- case: IHseq_calc_godel => [q IH1 IH2].
  by exists q => //; rewrite mem_cat IH1 orTb.
- case IHseq_calc_godel => [M + IH2].
  rewrite !mem_cat => /orP [h |/orP [h | h]]; exists M => //;
            by rewrite mem_cat h ?orbT; split; rewrite//=.
- case IHseq_calc_godel1 => [q1].
  case IHseq_calc_godel2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + subst => /=.
    have helper : forall (a b : R), a < b <-> ~(b <= a) by intros; lra.
         have contr_comp : forall (a b : R), a < b -> b <= a -> false by intros; lra.
     have hq : exists q : seq formula * seq formula,
         q = (A1 ++ A2 |- C) \/ q = B1 ++ B2 |- D
         by exists (A1 ++ A2 |- C); auto.
    have h: ~(exists2 q : seq formula * seq formula,
              q \in [:: A1 ++ A2 |- C, B1 ++ B2 |- D & Q] &
              \big[minr/1]_(i <- [seq [[i]]_Godel | i <- q.1]) i <=
                \big[maxr/0]_(i <- [seq [[i]]_Godel | i <- q.2]) i) -> false.
       move/minr_maxr_le_godel : IH12 => -[ [h1 h1'] | [h1 h1']];
       move/minr_maxr_le_godel : IH22 => -[ [h2 h2'] | [h2 h2']];
       intro;
       rewrite -forallPNP in H1;
       have := H1 (A1 ++ A2 |- C); rewrite mem_head //= !big_map; try move/(_ isT) => H11; try move => H11;
       have := H1 (B1 ++ B2 |- D); rewrite in_cons  //= !big_map; try move/(_ isT) => H22;
                                                                                      try move => H22; auto;
       rewrite -helper in H11; rewrite -?helper in H22;
       rewrite -minr_maxr_lt_godel in H11; rewrite -minr_maxr_lt_godel in H22;
       destruct H11 as [H11 H11']; destruct H22 as [H22 H22']; try lra;
    rewrite ?in_cons ?eq_refl ?orTb ?orbT//=.
    by move: h; rewrite falseE => /contrapT [q qmem]; rewrite !big_map => ?; exists q.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- move: IHseq_calc_godel => [q + IH2].
  rewrite in_cons => /predU1P[ | IH1].
  + exists (A ++ B |- C); subst; first by rewrite in_cons eq_refl orTb. 
    move: IH2 => /=.
    suff : \big[minr/1]_(j <- A ++ B ++ B) [[j]]_Godel =
           \big[minr/1]_(j <- A ++ B) [[j]]_Godel by move=> ->.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {7}/minr {11}/minr; repeat case: ifP; 
    intros; rewrite//=; lra.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_godel => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (A ++ B |- C); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //=.
    have := big_minr_if A B.
    case: ifPn; intros.
    * by rewrite -H0 in IH2; exact IH2.
    * by rewrite H0 (le_trans _ IH2)// ltW// ltNge.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_godel => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (X ++ B ++ A ++ Y |- C); subst; first by rewrite in_cons eq_refl orTb.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {3}/minr {8}/minr {13}/minr {14}/minr {19}/minr.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {3}/minr {8}/minr {13}/minr {14}/minr {19}/minr in IH2.
    move: IH2.
    repeat case: ifPn; intros; rewrite//=; try lra.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_godel => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (C |- X ++ B ++ A ++ Y); subst; first by rewrite in_cons eq_refl orTb.
    rewrite !big_max_cat_godel {1}/maxr {2}/maxr {3}/maxr {7}/maxr {12}/maxr {13}/maxr {18}/maxr.
    rewrite !big_max_cat_godel {1}/maxr {2}/maxr {3}/maxr {7}/maxr {12}/maxr {13}/maxr {18}/maxr in IH2.
    move: IH2.
    repeat case: ifP; intros; rewrite//=; try lra.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- exists (ldl_bool _ _ _ _ false :: A |- B); first by rewrite in_cons eq_refl orTb.
  by rewrite //= !big_cons ge_min big_tnth big_maxr_godel_ge0.
- exists (A |- [:: ldl_bool _ _ _ _ true]); first by rewrite in_cons eq_refl orTb.
  rewrite /minR/maxR//= !big_cons big_nil /maxr; case: ifPn => /= i.
  + by exfalso; lra.
  + by rewrite big_tnth big_minr_godel_le1.
- move: IHseq_calc_godel => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + exists ((a `/\ b) :: B |- A); subst; first by rewrite in_cons eq_refl orTb.
    rewrite !big_cons/= /minR/= !big_ord_recl !big_ord0 tnthS !tnth0.
    rewrite !big_cons/= /minR/= in IH2.
    have hb : minr ([[b]]_Godel) 1 = [[b]]_Godel.
      apply/min_idPl.
      by have /andP[] := @translate_boolT_01 R p p1 Godel _ _ _  b.
    rewrite {1}/minr; case: ifP; rewrite hb; move => h.
    * by rewrite /minr; rewrite{1}/minr in h; move: h; case: ifP; intros;
        move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
    * by rewrite{1}/minr in h; move: h; case: ifP; intros;
      move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
  + move/predU1P : IH1 => [|IH1].
    exists ((a `/\ b) :: B |- A); subst; first by rewrite in_cons eq_refl orTb.
    rewrite /= !big_cons/minR/=/minR !big_ord_recl big_ord0 tnthS !tnth0.
    rewrite /= !big_cons in IH2.
    have hb : minr ([[b]]_Godel) 1 = [[b]]_Godel.
      have h := @translate_boolT_01 R p p1 Godel _ _ _  b.
      rewrite /minr; case: ifPn; rewrite//=; intros.
      by lra.
    rewrite {1}/minr; case: ifPn; rewrite hb; move => h.
    * by rewrite /minr; rewrite{1}/minr in h; move: h; case: ifP; intros;
        move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
    * by rewrite{1}/minr in h; move: h; case: ifP; intros;
      move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- case IHseq_calc_godel1 => [q1].
  case IHseq_calc_godel2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + subst.
    rewrite /= big_cons big_nil in IH12.
    rewrite /= big_cons big_nil in IH22.
    have hb_max (x : @expr R (boolT_def impl_def m_def l_def)) :
        (maxr ([[x]]_Godel) 0) = [[x]]_Godel.
      have h := @translate_boolT_01 R p p1 Godel _ _ _  x.
      by rewrite /maxr; case: ifP; rewrite//=; intros; lra.
    have hb_min (x : @expr R (boolT_def impl_def m_def l_def)) :
        (minr ([[x]]_Godel) 1) = [[x]]_Godel.
      have h := @translate_boolT_01 R p p1 Godel _ _ _  x.
      by rewrite /minr; case: ifP; rewrite//=; intros; lra.
    rewrite !hb_max in IH12 IH22.
    exists (A |- [:: a `/\ b]); subst; first by rewrite in_cons eq_refl orTb. 
    rewrite /= !big_cons !big_nil/=/minR !big_ord_recl big_ord0 tnthS !tnth0  hb_min {2}/minr.
    by case: ifP; intros; rewrite hb_max; lra.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case IHseq_calc_godel1 => [q1].
  case IHseq_calc_godel2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + subst.
    rewrite /= !big_cons in IH12 IH22.
    exists ((a `\/ b) :: B |- A); first by rewrite in_cons eq_refl orTb. 
    rewrite /= !big_cons/=/maxR !big_ord_recl big_ord0 tnthS !tnth0.
    have hb_max (x : @expr R (boolT_def impl_def m_def l_def)) :
        maxr ([[x]]_Godel) 0 = [[x]]_Godel.
      have h := @translate_boolT_01 R p p1 Godel _ _ _  x.
      rewrite /maxr; case: ifPn; rewrite//=; intros.
      lra.
    rewrite hb_max {1}/maxr{1}/minr. case: ifPn; case: ifPn; intros.
    * rewrite {1}/minr in IH12; move: IH12; case: ifPn; intros; first by lra.
      by rewrite i0 in n.
    * rewrite {1}/minr in IH22; move: IH22; case: ifP; intros; rewrite//=.
      by rewrite i in n0.
    * rewrite {1}/minr in IH12; move: IH12; case: ifP; intros; rewrite//=.
      by rewrite i0 in n.
    * rewrite {1}/minr in IH22; move: IH22; case: ifP; intros; rewrite//=.
      by rewrite i in n0.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- move: IHseq_calc_godel => [q + IH2].
  have hb_max (x : @expr R (boolT_def impl_def m_def l_def)) :
    maxr ([[x]]_Godel) 0 = [[x]]_Godel.
    have h := @translate_boolT_01 R p p1 Godel _ _ _  x.
    by rewrite /maxr; case: ifP; rewrite//=; intros; lra.
  rewrite !in_cons => /predU1P[| IH1].
  + exists (A |- [:: a `\/ b]); subst; first by rewrite in_cons eq_refl orTb.
    rewrite /= /minR !big_cons big_nil /=/maxR !big_ord_recl big_ord0 tnthS !tnth0.
    rewrite /= /minR/maxR !big_cons big_nil in IH2.
    rewrite hb_max {2}/maxr. rewrite hb_max in IH2.
    by case: ifPn; intros; rewrite hb_max//= (le_trans IH2)// ltW.
  + move/predU1P : IH1 => [| IH1].
    exists (A |- [:: a `\/ b]); subst; first by rewrite in_cons eq_refl orTb.
    rewrite /= !big_cons big_nil /=/maxR !big_ord_recl big_ord0 tnthS !tnth0.
    rewrite /= !big_cons big_nil in IH2.
    rewrite hb_max in IH2. rewrite hb_max {2}/maxr.
    case: ifPn; intros; rewrite hb_max//=.
    rewrite -leNgt in n.
    by rewrite (le_trans IH2).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_godel => [q + IH2].
  rewrite !in_cons => /predU1P[| IH1].
  + exists (A |- [:: a `=> b]); subst; first by rewrite in_cons eq_refl orTb.
    move: IH2.
    rewrite /= !big_cons !big_nil /=.
    case: ifP.
    * have := @translate_boolT_01 R p p1 Godel _ _ _  b.
      by rewrite /maxr{1}/minr; case: ifPn; case: ifPn; try lra.
    * have := big_minr_godel_le1 (tnth (in_tuple A)).
      rewrite big_tnth /minr /maxr.
      by case: ifP; case: ifP; case: ifP; lra.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- case IHseq_calc_godel1 => [q1].
  case IHseq_calc_godel2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + exists ((a `=> b) :: A1 ++ A2 |- B); subst; first by rewrite in_cons eq_refl orTb.
    move: IH12 IH22.
    rewrite /= !big_cons !big_nil /minr /maxr/=.
    have ha := @translate_boolT_01 R p p1 Godel _ _ _  a.
    have := big_minr_if A1 A2.
    by repeat case: ifP; try lra.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
Qed.

Lemma sound_godel' Q:
  seq_calc_godel' Q ->
  exists2 q : seq formula * seq formula, q \in Q &
(\big[minr/1]_(f <- q.1) translation Godel p f  <=  \big[maxr/0]_(f <- q.2) translation Godel p f).
Proof.
intros; rewrite//=. dependent induction H.
- exists ([:: a] |- [:: a]); first by rewrite /= mem_head.
  by rewrite /minR/maxR !big_cons !big_nil /minr/maxr; repeat case: ifP; lra.
- case: IHseq_calc_godel' => [M].
  rewrite !mem_cat => IH1 IH2.
  exists M => //.
  rewrite !mem_cat.
  move/orP: IH1 => [->// |/orP].
  case => [-> |]; first by rewrite !orbT.
  by move/orP => [|] ->; rewrite ?(orTb,orbT).
- case: IHseq_calc_godel' => [q IH1 IH2].
  by exists q => //; rewrite mem_cat IH1 orTb.
- case IHseq_calc_godel' => [M + IH2].
  rewrite !mem_cat => /orP [h |/orP [h | h]]; exists M => //;
            by rewrite mem_cat h ?orbT; split; rewrite//=.
- case IHseq_calc_godel'1 => [q1].
  case IHseq_calc_godel'2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + subst.
    rewrite //=/minR/maxR in IH12 IH22.
    rewrite //=/maxR/minR.
    have helper : forall (a b : R), a < b <-> ~(b <= a) by intros; lra.
          have contr_comp : forall (a b : R), a < b -> b <= a -> false by intros; lra.
    have hq : exists q : seq formula * seq formula,
        q = (A1 ++ A2 |- C) \/ q = B1 ++ B2 |- D
        by exists (A1 ++ A2 |- C); auto.
    have h:  ~(exists2 q : seq formula * seq formula,
    q \in [:: A1 ++ A2 |- C, B1 ++ B2 |- D & Q] & \big[minr/1]_(i <- [seq [[i]]_Godel | i <- q.1]) i <=
               \big[maxr/0]_(i <- [seq [[i]]_Godel | i <- q.2]) i) -> false.
        move/minr_maxr_le_godel : IH12 => -[ [h1 h1'] | [h1 h1']];
        move/minr_maxr_le_godel : IH22 => -[ [h2 h2'] | [h2 h2']];
        intro;
        rewrite -forallPNP in H1;
        have := H1 (A1 ++ A2 |- C); rewrite mem_head //= !big_map; try move/(_ isT) => H11; try move => H11;
        have := H1 (B1 ++ B2 |- D); rewrite in_cons  //= !big_map; try move/(_ isT) => H22;
                                                                                       try move => H22; auto;
        rewrite -helper in H11; rewrite -?helper in H22;
        rewrite -minr_maxr_lt_godel in H11; rewrite -minr_maxr_lt_godel in H22;
        destruct H11 as [H11 H11']; destruct H22 as [H22 H22']; try lra;
     rewrite ?in_cons ?eq_refl ?orTb ?orbT//=.
     by move: h; rewrite falseE => /contrapT [q qmem]; rewrite !big_map => ?; exists q.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- move: IHseq_calc_godel' => [q + IH2].
  rewrite in_cons => /predU1P[ | IH1].
  + exists (A ++ B |- C); subst; first by rewrite in_cons eq_refl orTb.
    move: IH2.
    rewrite //= /minR.
    suff : \big[minr/1]_(j <- A ++ B ++ B) [[j]]_Godel =
           \big[minr/1]_(j <- A ++ B) [[j]]_Godel by move=> ->.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {7}/minr {11}/minr; repeat case: ifP;
    intros; rewrite//=; lra.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_godel' => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (A ++ B |- C); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= /minR.
    rewrite //= /minR in IH2.
    have := big_minr_if A B.
    case: ifPn; intros.
    * by rewrite -H0 in IH2; exact IH2.
    * by rewrite H0 (le_trans _ IH2)// ltW// ltNge.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_godel' => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (X ++ B ++ A ++ Y |- C); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= /minR/maxR.
    rewrite //= /minR/maxR in IH2.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {3}/minr {8}/minr {13}/minr {14}/minr {19}/minr.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {3}/minr {8}/minr {13}/minr {14}/minr {19}/minr in IH2.
    move: IH2.
    repeat (case: ifPn; try lra).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_godel' => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (C |- X ++ B ++ A ++ Y); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= /minR/maxR.
    rewrite //= /minR/maxR in IH2.
    rewrite !big_max_cat_godel {1}/maxr {2}/maxr {3}/maxr {7}/maxr {12}/maxr {13}/maxr {18}/maxr.
    rewrite !big_max_cat_godel {1}/maxr {2}/maxr {3}/maxr {7}/maxr {12}/maxr {13}/maxr {18}/maxr in IH2.
    move: IH2.
    by repeat (case: ifP; try lra).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- exists (ldl_bool _ _ _ _ false :: A |- B); first by rewrite in_cons eq_refl orTb.
  by rewrite /minR/maxR//= !big_cons ge_min/= big_tnth big_maxr_godel_ge0.
- exists (A |- [:: ldl_bool _ _ _ _ true]); first by rewrite in_cons eq_refl orTb.
  rewrite /= !big_cons big_nil /maxr; case: ifPn => /=h.
  + lra.
  + by rewrite big_tnth big_minr_godel_le1.
- move: IHseq_calc_godel' => [q].
  rewrite !in_cons => /predU1P[-> h|].
    exists ((a `/\ b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    move: h.
    rewrite /= !big_cons /= /minR !big_ord_recl big_ord0 tnthS !tnth0.
    have : minr ([[b]]_Godel) 1 = [[b]]_Godel.
      apply/min_idPl.
      by have /andP[] := @translate_boolT_01 R p p1 Godel _ _ _  b.
    by rewrite /minr; repeat (case: ifP; try lra).
  move/predU1P => [-> h|h].
    exists ((a `/\ b) :: B |- A); subst; first by rewrite in_cons eq_refl orTb.
    move: h.
    rewrite /= !big_cons /=/minR !big_ord_recl big_ord0 tnthS !tnth0.
    have : minr ([[b]]_Godel) 1 = [[b]]_Godel.
      have h := @translate_boolT_01 R p p1 Godel _ _ _  b.
      rewrite /minr; case: ifPn; rewrite//=; intros.
      by lra.
    by rewrite /minr; repeat (case: ifPn; try lra).
  by exists q => //; rewrite !in_cons h !orbT.
- case IHseq_calc_godel'1 => [q1].
  case IHseq_calc_godel'2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] +/orP[/eqP h1 | h1].
  + subst.
    rewrite /= !big_cons !big_nil.
    have hb_max (x : @expr R (boolT_def impl_def m_def l_def)) :
        (maxr ([[x]]_Godel) 0) = [[x]]_Godel.
      have h := @translate_boolT_01 R p p1 Godel _ _ _  x.
      by rewrite /maxr; case: ifP; rewrite//=; intros; lra.
    have hb_min (x : @expr R (boolT_def impl_def m_def l_def)) :
        (minr ([[x]]_Godel) 1) = [[x]]_Godel.
      have h := @translate_boolT_01 R p p1 Godel _ _ _  x.
      by rewrite /minr; case: ifP; rewrite//=; intros; lra.
    rewrite !hb_max => h1 h2.
    exists (A |- [:: a `/\ b]); subst; first by rewrite in_cons eq_refl orTb.
    rewrite /= !big_cons big_nil /=/minR !big_ord_recl big_ord0 tnthS !tnth0 hb_min {2}/minr.
    by case: ifP; intros; rewrite hb_max; lra.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case IHseq_calc_godel'1 => [q1].
  case IHseq_calc_godel'2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + subst.
    rewrite /= !big_cons in IH12 IH22.
    exists ((a `\/ b) :: B |- A); first by rewrite in_cons eq_refl orTb.
    rewrite /= !big_cons /=/maxR !big_ord_recl big_ord0 tnthS !tnth0.
    have hb_max (x : @expr R (boolT_def impl_def m_def l_def)) :
        maxr ([[x]]_Godel) 0 = [[x]]_Godel.
      have h := @translate_boolT_01 R p p1 Godel _ _ _  x.
      rewrite /maxr; case: ifPn; rewrite//=; intros.
      lra.
    rewrite hb_max {1}/maxr{1}/minr. case: ifPn; case: ifPn; intros.
    * rewrite {1}/minr in IH12; move: IH12; case: ifPn; intros; first by lra.
      by rewrite i0 in n.
    * rewrite {1}/minr in IH22; move: IH22; case: ifP; intros; rewrite//=.
      by rewrite i in n0.
    * rewrite {1}/minr in IH12; move: IH12; case: ifP; intros; rewrite//=.
      by rewrite i0 in n.
    * rewrite {1}/minr in IH22; move: IH22; case: ifP; intros; rewrite//=.
      by rewrite i in n0.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- move: IHseq_calc_godel' => [q + IH2].
  have hb_max (x : @expr R (boolT_def impl_def m_def l_def)) :
    maxr ([[x]]_Godel) 0 = [[x]]_Godel.
    have h := @translate_boolT_01 R p p1 Godel _ _ _  x.
    by rewrite /maxr; case: ifP; rewrite//=; intros; lra.
  rewrite !in_cons => /predU1P[| IH1].
  + exists (A |- [:: a `\/ b]); subst; first by rewrite in_cons eq_refl orTb.
    rewrite /= !big_cons big_nil /=/maxR !big_ord_recl big_ord0 tnthS !tnth0.
    rewrite /= !big_cons big_nil in IH2.
    rewrite hb_max {2}/maxr. rewrite hb_max in IH2.
    by case: ifPn; intros; rewrite hb_max//= (le_trans IH2)// ltW.
  + move/predU1P : IH1 => [| IH1].
    exists (A |- [:: a `\/ b]); subst; first by rewrite in_cons eq_refl orTb.
    rewrite /= !big_cons big_nil /=/maxR !big_ord_recl big_ord0 tnthS !tnth0.
    rewrite /= !big_cons big_nil in IH2.
    rewrite hb_max in IH2. rewrite hb_max {2}/maxr.
    case: ifPn; intros; rewrite hb_max//=.
    rewrite -leNgt in n.
    by rewrite (le_trans IH2).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- case: IHseq_calc_godel' => [q + IH2].
  rewrite !in_cons => /predU1P[|].
  + exists (A |- [:: `~ a]); subst; first by rewrite in_cons eq_refl orTb.
    rewrite /= !big_cons big_nil /=.
    rewrite /= !big_cons big_nil /= in IH2.
    case: ifPn => h.
    * rewrite /maxr; case: ifPn; intros; rewrite/=;
      rewrite maxxx {1}/minr in IH2; move: IH2; case: ifP; intros; rewrite//=.
      - by lra.
      - have ha := @translate_boolT_01 R _ p1 Godel _ _ _  a.
        have := @translate_boolT_01 R _ p1 Godel _ _ _  (ldl_and (tnth (in_tuple A))).
        by lra.
    * have -> : @maxr R 1 0 = 1 by rewrite /maxr ltNge ler01.
      rewrite maxxx {1}/minr in IH2; move: IH2; case: ifPn.
        by rewrite big_tnth (big_minr_godel_le1 (tnth (in_tuple A))).
      lra.
  + by exists q => //; rewrite !in_cons b orbT.
- case IHseq_calc_godel'1 => [q1].
  case IHseq_calc_godel'2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH22 /orP[/eqP h1 | h1] IH12.
  + exists ((`~ a) :: A1 ++ A2 |- B); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= /minR/maxR !big_cons/=.
    rewrite //= /minR/maxR !big_cons ?big_nil/= in IH12 IH22.
    rewrite {1}/minr. case: ifPn; case: ifPn; intros; rewrite//=.
    * have := @translate_boolT_01 R p p1 Godel _ _ _  (ldl_or (tnth (in_tuple B))).
      by rewrite /=/maxR big_tnth; case/andP.
    * have := big_minr_godel_le1 (tnth (in_tuple (A1 ++ A2))).
      by move: i; rewrite leNgt big_tnth => ->.
    * have hAA :=  @translate_boolT_01 R p p1 Godel _ _ _  (ldl_and (tnth (in_tuple (A1 ++ A2)))).
      rewrite//= /minR in hAA.
      rewrite big_tnth in n.
      have {hAA}-> : \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel = 0.
        apply/eqP; rewrite eq_le big_tnth leNgt n/=.
        by case/andP : hAA.
      have := @translate_boolT_01 R _ p1 Godel _ _ _  (ldl_or (tnth (in_tuple B))).
      rewrite/=/maxR big_tnth.
      by case/andP.
    * rewrite /maxr in IH12. move: IH12.
      have ha := @translate_boolT_01 R _ p1 Godel _ _ _  a.
      case: ifPn; intros; rewrite//=; first lra.
      have {}ha : [[a]]_Godel = 0 by apply/eqP; rewrite eq_le !leNgt n/=.
      rewrite ha big_tnth in IH12.
      have hA1 := @translate_boolT_01 R p p1 Godel _ _ _  (ldl_and (tnth (in_tuple A1))).
      rewrite//= /minR in hA1.
      have helper : \big[minr/1]_(j <- A1) [[j]]_Godel <= 0 ->
                    0 <= \big[minr/1]_(j <- A1) [[j]]_Godel <= 1 ->
                     \big[minr/1]_(j <- A1) [[j]]_Godel = 0 by intro; lra.
      rewrite big_tnth in helper.
      apply (helper IH12) in hA1.
      have := big_minr_if A1 A2.
      have hA2 :=  @translate_boolT_01 R p p1 Godel _ _ _  (ldl_and (tnth (in_tuple A2))).
      rewrite//= /minR in hA2.
      case: ifPn; intros; rewrite//=.
      - rewrite H1 [leLHS]big_tnth hA1.
        have := @translate_boolT_01 R p p1 Godel _ _ _  (ldl_or (tnth (in_tuple B))).
        rewrite /= /maxR big_tnth.
        rewrite big_tnth [leRHS]big_tnth in i.
        by case/andP.
      - clear helper IH12 ha.
        rewrite big_tnth hA1 -ltNge big_tnth in n2.
        have contr : 0 <= \big[minr/1]_(i < size A2) [[tnth (in_tuple A2) i]]_Godel <= 1 ->
                     \big[minr/1]_(i < size A2) [[tnth (in_tuple A2) i]]_Godel < 0 ->
                     False by intros; lra.
        by have := contr hA2 n2.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
Qed.

Lemma godel_neg_impl_admissable (e : formula) :
  [[`~ e]]_Godel = [[e `=> ldl_bool _ _ _ _ false]]_Godel.
Proof. by []. Qed.

Lemma equivalence_godel Q : seq_calc_godel' Q -> seq_calc_godel Q.
Proof.
intros.
dependent induction H.
- exact: id_g.
- by apply: eex_g; exact: IHseq_calc_godel'.
- by apply: ew_g; exact IHseq_calc_godel'.
- by apply: ec_g; exact IHseq_calc_godel'.
- apply comm_hyper_g.
  + exact: IHseq_calc_godel'1.
  + exact: IHseq_calc_godel'2.
- by apply comm_g; exact: IHseq_calc_godel'.
- by apply weak_g; exact: IHseq_calc_godel'.
- by apply exL_g; exact: IHseq_calc_godel'.
- by apply exR_g; exact: IHseq_calc_godel'.
- exact: bot_g.
- exact: top_g.
- apply andL_g. by exact IHseq_calc_godel'.
- apply andR_g.
  + exact: IHseq_calc_godel'1.
  + exact: IHseq_calc_godel'2.
- apply orL_g.
  + exact: IHseq_calc_godel'1.
  + exact: IHseq_calc_godel'2.
- apply/orR_g. by exact IHseq_calc_godel'.
- by rewrite neg_impl_godel; exact: implR_g.
- by rewrite neg_impl_godel; exact: implL_g.
Qed.

End hypersequent_godel.
