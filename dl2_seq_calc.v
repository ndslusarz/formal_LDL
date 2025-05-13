From HB Require Import structures.
From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import reals ereal signed.
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

HB.instance Definition _ (R : realType) b := 
  @gen_choiceMixin (@expr R (Bool_T b)). 

Reserved Notation "Q |= P" (no associativity, at level 61).
Reserved Notation "Q |- P" (no associativity, at level 61).

Section connectives_axioms.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Axiom neg_impl  :forall (e : @expr R Bool_T_def), (`~ e) = (e `=> ldl_bool def false).

Axiom true_false :  (@ldl_bool R def true) = (`~ ldl_bool def false).

Axiom and_impl : 
forall (a b: @expr R Bool_T_def), (a `/\ b) = (`~ (a `=> `~b)).

Axiom or_impl : 
forall (a b : @expr R Bool_T_def), (a `\/ b) = ((`~ a) `=> b).

End connectives_axioms.


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

Inductive seq_calc_dl2 :  seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef))
(*-> {mset (seq {mset (@expr R Bool_T_def)})}*)
      -> Prop :=
| id_dl2 : forall (Q :  seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                (a : @expr R Bool_T_undef),
    seq_calc_dl2 ( ([::a] |- [:: a]) :: Q)
(*structural*)
| eex_dl2 : forall (Q P S1 S2: seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef))),
    seq_calc_dl2 (S1 ++ P ++ Q ++ S2) ->
    seq_calc_dl2 (S1 ++ Q ++ P ++ S2)
| ew_dl2 : forall (Q P : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef))),
    seq_calc_dl2 Q ->
    seq_calc_dl2 (Q ++ P) 
| ec_dl2 : forall (Q P : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef))),
    seq_calc_dl2 (Q ++ P ++ P) ->
    seq_calc_dl2 (Q ++ P)
| w_dl2 : forall (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                  (A B C : seq (@expr R Bool_T_undef)),
    seq_calc_dl2 ((A |- B) :: Q) ->
    seq_calc_dl2 ((A ++ C |- B) :: Q)
| comm_hyper_dl2 : forall (Q :  seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                  (A1 A2 B1 B2 C D: seq (@expr R Bool_T_undef)),
    seq_calc_dl2 (((A1 ++ B1) |- C) :: Q) ->
    seq_calc_dl2 (((A2 ++ B2) |- D) :: Q) ->               
    seq_calc_dl2 ( ((A1 ++ A2) |- C) :: ((B1 ++ B2) |- D) :: Q)
(*exchange*)
| exL_dl2 : forall (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                  (A B C X Y : seq (@expr R Bool_T_undef)),
    seq_calc_dl2 (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_dl2 (((X ++ B ++ A ++ Y) |- C) :: Q) 
| exR_dl2 : forall (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                  (A B C X Y : seq (@expr R Bool_T_undef)),
    seq_calc_dl2 ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_dl2 ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
| top_dl2 : forall Q 
                  (A B : seq (@expr R Bool_T_undef)),
    seq_calc_dl2 ((A |- (ldl_bool undef true) :: B) :: Q)
    
| andL_dl2 : forall (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                   (A B : seq (@expr R Bool_T_undef))
                   (a b : @expr R Bool_T_undef),
    seq_calc_dl2 ((a :: A |- B) :: Q) ->
    seq_calc_dl2 ((b :: A |- B) :: Q) ->
    seq_calc_dl2 (((a `/\ b) :: A |- B) :: Q)
| andR_dl2 : forall (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                   (A B : seq (@expr R Bool_T_undef))
                   (a b : @expr R Bool_T_undef),
    seq_calc_dl2 ((A |- a :: B) :: Q) ->
    seq_calc_dl2 ((A |- b :: B) :: Q) ->
    seq_calc_dl2 (( A |- (a `/\ b) :: B) :: Q)
| orL_dl2 : forall (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                   (A B : seq (@expr R Bool_T_undef))
                   (a b : @expr R Bool_T_undef),
    seq_calc_dl2 ((A |-  B) :: Q) ->
    seq_calc_dl2 ((a :: b :: A |-  B) :: Q) ->
    seq_calc_dl2 (( (a `\/ b) :: A |- B) :: Q)
| orR_dl2 : forall (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                   (A B : seq (@expr R Bool_T_undef))
                   (a b : @expr R Bool_T_undef),
    seq_calc_dl2 ((A |- a :: b ::  B) :: Q) ->
    seq_calc_dl2 ((  A |- (a `\/ b) :: B) :: Q)
(*|implL_dl2 : forall (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                   (A B : seq (@expr R Bool_T_undef))
                   (a b : @expr R Bool_T_undef),
    seq_calc_dl2 ((A |-  B) :: Q) ->
    seq_calc_dl2 ((( b :: B) |- a:: A) :: Q ) ->
    seq_calc_dl2 ((((a `=> b) :: B) |- A) :: Q)
| implR_l : forall (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef)))
                 (A B : seq (@expr R Bool_T_undef))
                 (a b : @expr R Bool_T_undef),
    seq_calc_dl2 ((A|- B) :: Q ) ->
    seq_calc_dl2  ((a::A |- b :: B) :: Q)  ->
    seq_calc_dl2 ((A |- (a `=> b) :: B) :: Q )*)
(*todo: go back to ldl and add impl if undef*).

Definition eval_dl2_and  (Q : seq (@expr R Bool_T_undef))
  := [[(ldl_and Q)]]_dl2 .

Definition eval_dl2_or  (Q : seq (@expr R Bool_T_undef))
  := [[(ldl_or Q)]]_dl2 .

Lemma eval_dl2_and_cat  (Q P : seq (@expr R Bool_T_undef)) :
 eval_dl2_and (Q ++ P) = (eval_dl2_and Q + eval_dl2_and P)%R.
Proof.
rewrite /eval_dl2_and//=/sumR !big_map !big_cat//=.
Qed.

Lemma eval_dl2_or_cat  (Q P : seq (@expr R Bool_T_undef)) :
 eval_dl2_or (Q ++ P) = (-1) * eval_dl2_or Q * eval_dl2_or P.
Proof.
rewrite /eval_dl2_or//=/prodR !big_map !big_cat//=.
have h : -1 * ((-1) ^+ (size Q).+1 * \prod_(j <- Q) [[j]]_dl2) * ((-1) ^+ (size P).+1 * 
\prod_(j <- P) [[j]]_dl2)
 =
(-1)^+ 1 * (-1) ^+ (size Q).+1 * (-1) ^+ (size P).+1 * \prod_(j <- Q) [[j]]_dl2 * 
\prod_(j <- P) [[j]]_dl2.
nra.
rewrite h (*-(expr1 (-1))*) -exprD -exprD size_cat.
have h1: (1 + (size Q).+1 + (size P).+1)%N = (size Q + size P).+1 + 2. 
rewrite//=.  admit. 
have H : (-1) ^+ (1 + (size Q).+1 + (size P).+1)%:R = 
           (-1) ^+ (size Q + size P).+1.
{intros. rewrite h1. admit.

Admitted.

Lemma eval_dl2_and_le0 (Q : seq (@expr R Bool_T_undef)):
  eval_dl2_and Q <= 0.
Proof.
have H := dl2_translation_le0 (ldl_and Q).
rewrite /eval_dl2_and//=.
Qed.

Lemma eval_dl2_or_le0 (Q : seq (@expr R Bool_T_undef)):
  eval_dl2_or Q <= 0.
Proof.
have H := dl2_translation_le0 (ldl_or Q).
rewrite /eval_dl2_or//=.
Qed.

Lemma sound_dl2 (Q : seq ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef))):
seq_calc_dl2 Q -> 
exists (q : ( seq (@expr R Bool_T_undef) * seq (@expr R Bool_T_undef))), q \in Q 
/\ 
eval_dl2_and (fst q)  <=  eval_dl2_or (snd q).
Proof.
intros; rewrite//=. dependent induction H.
- exists ([:: a] |- [:: a]). rewrite //= mem_head; split. by [].  
  rewrite /eval_dl2_and/eval_dl2_or//= /sumR/prodR. 
  rewrite !big_cons !big_nil addr0 mulr1. 
  by rewrite -(expr1 (-1)) sqrr_sign mul1r//=.
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
    rewrite //= eval_dl2_and_cat. 
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
    rewrite //= eval_dl2_and_cat in IH12.
    rewrite //= eval_dl2_and_cat in IH22.
    have temp : eval_dl2_and A2 <= eval_dl2_and B1 \/ eval_dl2_and A2 > eval_dl2_and B1. lra.
    destruct temp as [ab | ab].
    * exists (A1 ++ A2 |- C).
      rewrite !in_cons eq_refl !orTb //=. split; first by [].
      rewrite eval_dl2_and_cat. lra.
    * exists (B1 ++ B2 |- D).
      rewrite !in_cons eq_refl !orTb orbT//=. split; first by [].
      rewrite eval_dl2_and_cat. lra.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
End dl2_hyperseq_calc.
