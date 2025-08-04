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

Reserved Notation "{[ e ]}" (format "{[  e  ]}").

HB.instance Definition _ (R : realType) x y z v := 
  @gen_choiceMixin (@expr R (Bool_T x y z v)). 

Reserved Notation "Q |= P" (no associativity, at level 61).
Reserved Notation "Q |- P" (no associativity, at level 61).


Section dl2_hyperseq_calc.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope mset_scope. 
Context {R : realType}.
Context {K : choiceType}.
Implicit Types  (A : {mset K}) (s : seq K).
Variable p : R. 
Local Notation "[[ e ]]_dl2" := (@dl2_translation R  _ e).

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).

Inductive seq_calc_dl2 :  seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                                * seq (@expr R (Bool_T_undef impl_def m_def l_undef)))
(*-> {mset (seq {mset (@expr R Bool_T_def)})}*)
      -> Prop :=
| id_dl2 : forall (Q :  seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef))
                              * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                (a : @expr R (Bool_T_undef impl_def m_def l_undef)),
    seq_calc_dl2 ( ([::a] |- [:: a]) :: Q)
(*structural*)
| eex_dl2 : forall (Q P S1 S2: seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                                     * seq (@expr R (Bool_T_undef impl_def m_def l_undef)))),
    seq_calc_dl2 (S1 ++ P ++ Q ++ S2) ->
    seq_calc_dl2 (S1 ++ Q ++ P ++ S2)
| ew_dl2 : forall (Q P : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                               * seq (@expr R (Bool_T_undef impl_def m_def l_undef)))),
    seq_calc_dl2 Q ->
    seq_calc_dl2 (Q ++ P) 
| ec_dl2 : forall (Q P : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                               * seq (@expr R (Bool_T_undef impl_def m_def l_undef)))),
    seq_calc_dl2 (Q ++ P ++ P) ->
    seq_calc_dl2 (Q ++ P)
| w_dl2 : forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                            * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                  (A B C : seq (@expr R (Bool_T_undef impl_def m_def l_undef))),
    seq_calc_dl2 ((A |- B) :: Q) ->
    seq_calc_dl2 ((A ++ C |- B) :: Q)
| comm_hyper_dl2 : forall (Q :  seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                                      * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                  (A1 A2 B1 B2 C D: seq (@expr R (Bool_T_undef impl_def m_def l_undef))),
    seq_calc_dl2 (((A1 ++ B1) |- C) :: Q) ->
    seq_calc_dl2 (((A2 ++ B2) |- D) :: Q) ->               
    seq_calc_dl2 ( ((A1 ++ A2) |- C) :: ((B1 ++ B2) |- D) :: Q)
(*exchange*)
| exL_dl2 : forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef))
                              * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                  (A B C X Y : seq (@expr R (Bool_T_undef impl_def m_def l_undef))),
    seq_calc_dl2 (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_dl2 (((X ++ B ++ A ++ Y) |- C) :: Q) 
| exR_dl2 : forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                              * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                  (A B C X Y : seq (@expr R (Bool_T_undef impl_def m_def l_undef))),
    seq_calc_dl2 ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_dl2 ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
| top_dl2 : forall Q 
                  (A B : seq (@expr R (Bool_T_undef impl_def m_def l_undef))),
    seq_calc_dl2 ((A |- [::(ldl_bool _ _ _ _ true)]) :: Q)
    
| mandL_dl2 : forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                               * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                   (A B : seq (@expr R (Bool_T_undef impl_def m_def l_undef)))
                   (a b : @expr R (Bool_T_undef impl_def m_def l_undef)),
    seq_calc_dl2 ((a :: A |- B) :: Q) ->
    seq_calc_dl2 ((b :: A |- B) :: Q) ->
    seq_calc_dl2 (((a `** b) :: A |- B) :: Q)
| mandR_dl2 : forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                               * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                   (A B : seq (@expr R (Bool_T_undef impl_def m_def l_undef)))
                   (a b : @expr R (Bool_T_undef impl_def m_def l_undef)),
    seq_calc_dl2 ((A |- a :: b :: B ) :: Q) ->
    (*seq_calc_dl2 ((A |- b :: B ) :: Q) ->*)
    seq_calc_dl2 (( A |- (a `** b) :: B) :: Q)
| morL_dl2 : forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                               * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                   (A B : seq (@expr R (Bool_T_undef impl_def m_def l_undef)))
                   (a b : @expr R (Bool_T_undef impl_def m_def l_undef)),
    seq_calc_dl2 ((a :: A |- B) :: Q) ->
    seq_calc_dl2 ((b :: A |- B) :: Q) ->
    seq_calc_dl2 (((a `++ b) :: A |- B) :: Q)
| morR_dl2 : forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                               * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                   (A B : seq (@expr R (Bool_T_undef impl_def m_def l_undef)))
                   (a b : @expr R (Bool_T_undef impl_def m_def l_undef)),
    seq_calc_dl2 ((A |- a :: b :: B ) :: Q) ->
    (*seq_calc_dl2 ((A |- b :: B ) :: Q) ->*)
    seq_calc_dl2 (( A |- (a `++ b) :: B) :: Q)
| implR_dl2 : forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                               * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                   (A B : seq (@expr R (Bool_T_undef impl_def m_def l_undef)))
                   (a b : @expr R (Bool_T_undef impl_def m_def l_undef)),
    seq_calc_dl2 ((A|- B) :: Q ) ->
    seq_calc_dl2 ((a :: A |- b :: B) :: Q) ->
    seq_calc_dl2 ((A |- (a `=> b) :: B) :: Q)
| implL_dl2 : forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                               * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                   (A B : seq (@expr R (Bool_T_undef impl_def m_def l_undef)))
                   (a b : @expr R (Bool_T_undef impl_def m_def l_undef)),
    seq_calc_dl2 ((A|- B) :: Q ) ->
    seq_calc_dl2 ((b :: A |- a :: B) :: Q) ->
    seq_calc_dl2 (( (a `=> b) :: A |- B) :: Q)
.

Lemma dl2_mor_mand_equiv (Q : seq (@expr R (Bool_T_undef impl_def m_def l_undef))):
 [[(ldl_mand Q)]]_dl2 = [[(ldl_mor Q)]]_dl2.
Proof.
rewrite//=.
Qed.

Definition eval_dl2  (Q : seq (@expr R (Bool_T_undef impl_def m_def l_undef)))
  := [[(ldl_mand Q)]]_dl2 .


Lemma eval_dl2_cat  (Q P : seq (@expr R (Bool_T_undef impl_def m_def l_undef))) :
 eval_dl2 (Q ++ P) = (eval_dl2 Q + eval_dl2 P)%R.
Proof.
rewrite /eval_dl2//=/sumR !big_map !big_cat//=.
Qed.

Lemma eval_dl2_cons  (P : seq (@expr R (Bool_T_undef impl_def m_def l_undef))) (q: (@expr R (Bool_T_undef impl_def m_def l_undef))):
 eval_dl2 (q :: P) = [[q]]_dl2 + eval_dl2 P.
Proof.
rewrite /eval_dl2//=/sumR !big_cons//=.
Qed.

Lemma eval_dl2_and_le0 (Q : seq (@expr R (Bool_T_undef impl_def m_def l_undef))):
  eval_dl2 Q <= 0.
Proof.
have H := dl2_translation_le0 p _  (ldl_mand Q).
rewrite/= in H; rewrite /eval_dl2//=.
Qed.


Lemma sound_dl2 (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
* seq (@expr R (Bool_T_undef impl_def m_def l_undef)))):
seq_calc_dl2 Q -> 
exists (q : ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
* seq (@expr R (Bool_T_undef impl_def m_def l_undef)))), q \in Q 
/\ 
eval_dl2 (fst q)  <=  eval_dl2 (snd q).
Proof.
intros; rewrite//=. dependent induction H.
- exists ([:: a] |- [:: a]). rewrite //= mem_head; split. by [].  
  rewrite /eval_dl2/eval_dl2//= /sumR. 
- destruct IHseq_calc_dl2 as [M [IH1 IH2]]. 
  exists M. 
  rewrite !mem_cat //= in IH1.
  rewrite !mem_cat. split; first last.
  by rewrite IH2//=. move/orP: IH1.
  move => [IH1 | /orP IH1].
  rewrite IH1//=.
  destruct IH1 as [IH1 | IH1].
  rewrite IH1 !orbT//=.
  move/orP: IH1.
  move => [IH1 | IH1]; rewrite IH1 ?orTb ?orbT//=.
- destruct IHseq_calc_dl2 as [q [IH1 IH2]].
  exists q. rewrite mem_cat IH1 orTb.
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_dl2 as [M [IH1 IH2]].   
  exists M. rewrite !mem_cat in IH1. 
  rewrite mem_cat. move/orP : IH1. 
  move => [h |/orP h].  rewrite h ?orbT; split; rewrite//=. 
  move: h. move => [h | h]; rewrite h ?orbT; split; rewrite//=.
- destruct IHseq_calc_dl2 as [q [IH1 IH2]].
   rewrite in_cons in IH1. 
   move/orP : IH1. 
  move => [/eqP h | h].
  + exists (A ++ C |- B).
    subst. rewrite //= in IH2.
    rewrite in_cons eq_refl orTb. split. by [].
    rewrite //= eval_dl2_cat. 
    have HC := eval_dl2_and_le0 C.
    lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- destruct IHseq_calc_dl2_1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_dl2_2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    rewrite //= eval_dl2_cat in IH12.
    rewrite //= eval_dl2_cat in IH22.
    have temp : eval_dl2 A2 <= eval_dl2 B1 \/ eval_dl2 A2 > eval_dl2 B1. lra.
    destruct temp as [ab | ab].
    * exists (A1 ++ A2 |- C).
      rewrite !in_cons eq_refl !orTb //=. split; first by [].
      rewrite eval_dl2_cat. lra.
    * exists (B1 ++ B2 |- D).
      rewrite !in_cons eq_refl !orTb orbT//=. split; first by [].
      rewrite eval_dl2_cat. lra.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
- destruct IHseq_calc_dl2 as [q [IH1 IH2]].
  rewrite in_cons in IH1. 
  move/orP : IH1. 
  move => [/eqP h | h].
  + exists (X ++ B ++ A ++ Y |- C).
    subst.
    rewrite mem_head; split; first by [].
    rewrite//=  !eval_dl2_cat in IH2.
    rewrite//= !eval_dl2_cat. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- destruct IHseq_calc_dl2 as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h | h].
  + subst. exists (C |- X ++ B ++ A ++ Y).
    rewrite mem_head; split; first by [].
    rewrite//= !eval_dl2_cat in IH2.
    rewrite//= !eval_dl2_cat. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- exists (A |- [:: ldl_bool _ _ _ _ true ]).
  rewrite mem_head; split; first by [].
  by rewrite//= /eval_dl2//=/sumR !big_cons big_nil !addr0 eval_dl2_and_le0/=.
- destruct IHseq_calc_dl2_1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_dl2_2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. exists (a `** b :: A |- B).
    rewrite//= eval_dl2_cons in IH12.
    rewrite//= eval_dl2_cons in IH22.
    rewrite mem_head; split; first by [].
    rewrite//= eval_dl2_cons//=/sumR !big_cons big_nil addr0. 
    have ha := dl2_translation_le0 p _  a.
    have hb := dl2_translation_le0 p _  b. 
    have h : ([[a]]_dl2 + eval_dl2 A)%E <= eval_dl2 B ->
             ([[a]]_dl2 + [[b]]_dl2 + eval_dl2 A)%E <= eval_dl2 B. lra.
    rewrite (h IH12)//=.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
- destruct IHseq_calc_dl2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH21. 
   move/orP: IH21.
  move => [/eqP h2 | h2].
  + subst. exists (A |- a `** b :: B). 
    rewrite mem_head; split; first by [].
    have ev_0 : eval_dl2 [::] = 0. rewrite /eval_dl2//= /sumR big_nil//=.
    rewrite//= !eval_dl2_cons addrA//= in IH22.
    rewrite//= eval_dl2_cons//=/sumR !big_cons big_nil addr0//=.
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
- destruct IHseq_calc_dl2_1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_dl2_2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. exists (a `++ b :: A |- B).
    rewrite//= eval_dl2_cons in IH12.
    rewrite//= eval_dl2_cons in IH22.
    rewrite mem_head; split; first by [].
    rewrite//= eval_dl2_cons//=/sumR !big_cons big_nil addr0. 
    have ha := dl2_translation_le0 p _  a.
    have hb := dl2_translation_le0 p _  b. 
    have h : ([[a]]_dl2 + eval_dl2 A)%E <= eval_dl2 B ->
             ([[a]]_dl2 + [[b]]_dl2 + eval_dl2 A)%E <= eval_dl2 B. lra.
    rewrite (h IH12)//=.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
- destruct IHseq_calc_dl2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH21. 
   move/orP: IH21.
  move => [/eqP h2 | h2].
  + subst. exists (A |- a `++ b :: B). 
    rewrite mem_head; split; first by [].
    have ev_0 : eval_dl2 [::] = 0. rewrite /eval_dl2//= /sumR big_nil//=.
    rewrite//= !eval_dl2_cons addrA//= in IH22.
    rewrite//= eval_dl2_cons//=/sumR !big_cons big_nil addr0//=.
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
- destruct IHseq_calc_dl2_1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_dl2_2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. exists (A |- a `=> b :: B). 
    rewrite mem_head; split; first by [].
    rewrite//= in IH12.
    rewrite//= eval_dl2_cons eval_dl2_cons in IH22.
    rewrite//= eval_dl2_cons//=. rewrite/maxr; case: ifP; move => /eqP hc;
    rewrite ?oppr0 ?add0r//=. lra.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=.
- destruct IHseq_calc_dl2_1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_dl2_2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. exists (a `=> b :: A |- B). 
    rewrite mem_head; split; first by [].
    rewrite//= in IH12.
    rewrite//= eval_dl2_cons eval_dl2_cons in IH22.
    rewrite//= eval_dl2_cons//=. rewrite/maxr; case: ifP; move => /eqP hc.
    * rewrite oppr0 add0r//=.
    * lra.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=.
Qed.

Lemma prelinearity_dl2 : 
forall (Q : seq ( seq (@expr R (Bool_T_undef impl_def m_def l_undef)) 
                  * seq (@expr R (Bool_T_undef impl_def m_def l_undef))))
                   (A B : seq (@expr R (Bool_T_undef impl_def m_def l_undef)))
                   (a b : @expr R (Bool_T_undef impl_def m_def l_undef)),
    seq_calc_dl2 ([::( [::] |- [:: (a `=> b) `++ (b `=> a )])] ).
Proof.
Admitted.

End dl2_hyperseq_calc.
