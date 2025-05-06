From HB Require Import structures.
From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder finmap multiset.
Require Import mathcomp_extra analysis_extra ldl fuzzy.


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


Section seq_calc_bool.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope mset_scope. 
Context {R : realType}.
Context {K : choiceType}.
Implicit Types  (A : {mset K}) (s : seq K).
Local Notation "<< e >>" := (@bool_translation R _ e).

Inductive seq_calc_bool_ms : {mset (@expr R Bool_T_def)}
  -> {mset (@expr R Bool_T_def)} -> Prop :=
| init : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def),
     a +` Q |= a +` P
| bot : forall (Q P : {mset (@expr R Bool_T_def)}),
    (ldl_bool def false) +` Q |= P
| top : forall (Q P : {mset (@expr R Bool_T_def)}),
    Q |= (ldl_bool def true) +` P
| and_R : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    Q |= a +` P  ->  Q |= ( b) +` P ->
      Q |=  (a `/\ b) +` P
| andL1 :  forall (Q P : {mset (@expr R Bool_T_def)}) (a b : @expr R Bool_T_def),
    a +` Q  |= P ->
      (a `/\ b) +` Q |= P
| andL2 :  forall (Q P : {mset (@expr R Bool_T_def)}) (a b : @expr R Bool_T_def),
    b +` Q  |= P ->
      (a `/\ b) +` Q |= P
| orR1 : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    Q |=  a +` P ->
      Q |=  (a `\/ b) +` P
| orR2 : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    Q |=  b +` P ->
      Q |=  (a `\/ b) +` P
| orL :  forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    a+`Q  |= P ->  b +` Q |= P ->
      (a `\/ b)+`Q |= P
| negL : forall Q P a,
    Q |= a +` P ->
      (`~ a)+`Q|= P
where "Q |= P" := (seq_calc_bool_ms Q P).


Lemma sound_sc_bool_mseq' (Q P : {mset expr Bool_T_def}) :
Q |= P -> 
(forall (q : expr Bool_T_def), (q \in Q) -> <<q>> = <<ldl_bool def true>>) ->
               exists (p : expr Bool_T_def) , (p \in P) /\ <<p>> = <<ldl_bool def true>>.
Proof.
 rewrite //=. intros. dependent induction H.
- exists a. have H := H0 a. 
  rewrite in_mset1D eq_refl orTb ?andTb.
  move: H; rewrite in_mset1D eq_refl orTb ?andTb//=.
  auto.
- exfalso.  move: H0.
  rewrite//=. apply contrapT. rewrite  not_implyE.
  rewrite not_andE notE. left. 
  rewrite -existsNP.
  exists (ldl_bool def false).
  rewrite in_mset1D eq_refl orTb//=. 
  auto.
- exists (ldl_bool def true).
  by rewrite in_mset1D eq_refl orTb//=. 
- destruct (IHseq_calc_bool_ms1 H1) as [x [IH11 IH12]].
  destruct (IHseq_calc_bool_ms2 H1) as [y [IH21 IH22]].
  rewrite in_mset1D in IH11. move/orP: IH11.
  move => IH11.
  destruct IH11.
    + move/eqP: H2. move/esym => H2. subst. 
      rewrite in_mset1D in IH21. move/orP: IH21.
      move => IH21. destruct IH21. 
      * move/eqP: H2. move/esym => H2.
        subst. 
        exists (x `/\ y). 
        simpl; split; eauto.
        - by rewrite in_mset1D eq_refl orTb.
        - rewrite big_cons big_seq1. 
          by rewrite IH12 IH22.
      * exists y. rewrite IH22 in_mset1D H2 orbT. eauto.
    +  exists x.  rewrite IH12 in_mset1D H2 orbT. eauto.
- have H1 := (H0 (a `/\ b)). 
  rewrite in_mset1D eq_refl orTb in H1.
  simpl in H1.
  rewrite big_cons big_seq1 in H1.
  apply  IHseq_calc_bool_ms.
  intros. rewrite in_mset1D in H2. move/orP: H2.
      move => H2. destruct H2.
      * move/eqP: H2. move => H2.
        subst. apply andb_prop in H1.
        + destruct H1 as [ha hb].
          by apply ha.
        + by [].
      * apply H0. by rewrite in_mset1D H2 orbT.
- have H1 := (H0 (a `/\ b)). 
  rewrite in_mset1D eq_refl orTb in H1.
  simpl in H1.
  rewrite big_cons big_seq1 in H1.
  apply  IHseq_calc_bool_ms.
  intros. rewrite in_mset1D in H2. move/orP: H2.
      move => H2. destruct H2.
      * move/eqP: H2. move => H2.
        subst. apply andb_prop in H1.
        + destruct H1 as [ha hb].
          by apply hb.
        + by [].
      * apply H0. by rewrite in_mset1D H2 orbT.
- destruct (IHseq_calc_bool_ms H0) as [x [IH1 IH2]].
  rewrite in_mset1D in IH1. move/orP: IH1.
  move => IH1.
  destruct IH1.
    + move/eqP: H1. move => H1. subst. 
      exists (a `\/ b).
      rewrite in_mset1D eq_refl orTb//= big_cons big_seq1 IH2. 
      by rewrite orTb//.
    + exists x. 
      by rewrite IH2 in_mset1D H1 orbT//.
- destruct (IHseq_calc_bool_ms H0) as [x [IH1 IH2]].
  rewrite in_mset1D in IH1. move/orP: IH1.
  move => IH1.
  destruct IH1.
    + move/eqP: H1. move => H1. subst. 
      exists (a `\/ b).
      rewrite in_mset1D eq_refl orTb//= big_cons big_seq1 IH2. 
      by rewrite orbT//.
    + exists x. 
      by rewrite IH2 in_mset1D H1 orbT//.
- have H2 := (H1 (a `\/ b)). 
  rewrite in_mset1D eq_refl orTb in H2.
  simpl in H2.
  rewrite big_cons big_seq1 in H2.
  apply Bool.orb_prop in H2; rewrite//=.
  destruct H2 as [ha | hb].
  + apply  IHseq_calc_bool_ms1.
    intros. rewrite in_mset1D in H2. move/orP: H2.
      move => H2. destruct H2.
      * move/eqP: H2. move => H2.
        subst. by apply ha.
      * apply H1. by rewrite in_mset1D H2 orbT.
  + apply  IHseq_calc_bool_ms2.
    intros. rewrite in_mset1D in H2. move/orP: H2.
    move => H2. destruct H2.
    * move/eqP: H2. move => H2.
      subst. by apply hb.
    * apply H1. by rewrite in_mset1D H2 orbT.
- have H1 := H0 (`~ a). 
  rewrite in_mset1D eq_refl orTb in H1.
  destruct IHseq_calc_bool_ms as [x y]. 
  + intros. apply H0.
    by rewrite in_mset1D H2 orbT. 
  + exists x. destruct y as [h1 h2].
    rewrite h2.
    rewrite in_mset1D in h1. move/orP: h1. move => [h1 | h3].
    * move/eqP: h1. move => h1.
      subst. rewrite //= in H1.
      rewrite h2//= in H1.
      exfalso.
      move: H1. by auto.
    * by rewrite h3.
Qed.

End seq_calc_bool.

Section hypersequent_lukasiewicz.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope mset_scope. 

Context {R : realType}.
Context {K : choiceType}.
Implicit Types  (A : {mset K}) (s : seq K).
Variable p : R. 
Local Notation "[[ e ]]_ l" := (@translation R l p _ e).

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).
(*entailment as pair (A, B) where A |- B*)


(*soundness for minimal implicational fragment*)
Inductive seq_calc_luka_impl :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))
(*-> {mset (seq {mset (@expr R Bool_T_def)})}*)
      -> Prop :=
| id_l : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                (A : seq (@expr R Bool_T_def)),
    seq_calc_luka_impl ( (A |- A) :: Q)
| empty : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka_impl (([::] |- [::]) :: Q)
(*structural*)
| eex_l : forall (Q P S1 S2: seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka_impl (S1 ++ P ++ Q ++ S2) ->
    seq_calc_luka_impl (S1 ++ Q ++ P ++ S2)
| ew_l : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka_impl Q ->
    seq_calc_luka_impl (Q ++ P) 
| ec_l : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka_impl (Q ++ P ++ P) ->
    seq_calc_luka_impl (Q ++ P)
| w_l : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_luka_impl ((A |- B) :: Q) ->
    seq_calc_luka_impl ((A ++ C |- B) :: Q)
| split_l : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C D: seq (@expr R Bool_T_def)),
    seq_calc_luka_impl (((A ++ B) |- (C ++ D)) :: Q) ->
    seq_calc_luka_impl ((A |- C) ::  (B |- D) :: Q)
| mix_l : forall   (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C D: seq (@expr R Bool_T_def)),
    seq_calc_luka_impl ((A |- C) :: Q) ->
    seq_calc_luka_impl ((B |- D) :: Q) ->
    seq_calc_luka_impl (((A ++ B) |- (C ++ D)) :: Q)

(*exchange*)
| exL_l : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_luka_impl (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_luka_impl (((X ++ B ++ A ++ Y) |- C) :: Q) 
| exR_l : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_luka_impl ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_luka_impl ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
(*restricted to a single-conclusion case for Lukasiewicz*)
| bot_l : forall Q 
                 (A : seq (@expr R Bool_T_def))
                 (b : @expr R Bool_T_def),
    seq_calc_luka_impl (((ldl_bool def false :: A) |- [:: b]) :: Q)
(*new formulation, not standard rule*)
|implL_l : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                   (A B : seq (@expr R Bool_T_def))
                   (a b : @expr R Bool_T_def),
    seq_calc_luka_impl ((( b :: B) |- a:: A) :: Q ) ->
    seq_calc_luka_impl ((((a `=> b) :: B) |- A) :: Q)
| implR_l : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                 (A B : seq (@expr R Bool_T_def))
                 (a b : @expr R Bool_T_def),
    seq_calc_luka_impl ((A|- B) :: Q ) ->
    seq_calc_luka_impl  ((a::A |- b :: B) :: Q)  ->
    seq_calc_luka_impl ((A |- (a `=> b) :: B) :: Q ).


Inductive seq_calc_luka' :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))
(*-> {mset (seq {mset (@expr R Bool_T_def)})}*)
      -> Prop :=
| id_l' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                (A : seq (@expr R Bool_T_def)),
    seq_calc_luka' ( (A |- A) :: Q)
| empty' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka' (([::] |- [::]) :: Q)
(*structural*)
| eex_l' : forall (Q P S1 S2: seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka' (S1 ++ P ++ Q ++ S2) ->
    seq_calc_luka' (S1 ++ Q ++ P ++ S2)
| ew_l' : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka' Q ->
    seq_calc_luka' (Q ++ P) 
| ec_l' : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka' (Q ++ P ++ P) ->
    seq_calc_luka' (Q ++ P)
| w_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_luka' ((A |- B) :: Q) ->
    seq_calc_luka' ((A ++ C |- B) :: Q)
(*add split and mix rules*)
| split_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C D: seq (@expr R Bool_T_def)),
    seq_calc_luka' (((A ++ B) |- (C ++ D)) :: Q) ->
    seq_calc_luka' ((A |- C) ::  (B |- D) :: Q)
| mix_l' : forall   (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C D: seq (@expr R Bool_T_def)),
    seq_calc_luka' ((A |- C) :: Q) ->
    seq_calc_luka' ((B |- D) :: Q) ->
    seq_calc_luka' (((A ++ B) |- (C ++ D)) :: Q)
(*exchange*)
| exL_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_luka' (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_luka' (((X ++ B ++ A ++ Y) |- C) :: Q) 
| exR_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_luka' ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_luka' ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
(*both are restricted to a single-conclusion case for Lukasiewicz*)
| bot_l' : forall Q 
                 (A : {mset (@expr R Bool_T_def)})
                 (b : @expr R Bool_T_def),
    seq_calc_luka' (((ldl_bool def false :: A) |- [:: b]) :: Q)
| top_l' : forall Q 
                 (A : seq (@expr R Bool_T_def)),
    seq_calc_luka' ((A |- [:: (ldl_bool def true)]) :: Q)
(*new formulation, not standard conjunction rule*)
|andL_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                   (A B : seq (@expr R Bool_T_def))
                   (a b : @expr R Bool_T_def),
    seq_calc_luka' (((a ::  b :: B) |- A) :: Q ) ->
    seq_calc_luka' (((ldl_bool def false :: B) |- A) :: Q ) ->
    seq_calc_luka' ((((a `/\ b) :: B) |- A) :: Q)
| andR_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                 (A B : seq (@expr R Bool_T_def))
                 (a b : @expr R Bool_T_def),
    seq_calc_luka' ((A |- B) :: Q ) -> (*not needed for soundness, but this is needed
                                         fir this rule to be derivable*)
    seq_calc_luka'  ((A |- (a ::  b :: B)) :: (A |- (ldl_bool def false :: B)) :: Q)  ->
    seq_calc_luka' ((A |- (a `/\ b) :: B) :: Q )
(*all below derived by me. they are sound but would appreciate someone else's opinion*)
| negL_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                 (A B : seq (@expr R Bool_T_def))
                 (a : @expr R Bool_T_def),
    seq_calc_luka' (((ldl_bool def false :: A) |-  a :: B) :: Q) ->
    seq_calc_luka' ((((`~a) :: A) |- B) :: Q)
| negR_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                 (A B : seq (@expr R Bool_T_def))
                 (a : @expr R Bool_T_def),
    seq_calc_luka' ( ( A |- B):: Q) ->
    seq_calc_luka' (((a :: A) |-  ldl_bool def false :: B)::Q) ->
    seq_calc_luka' ((A |-  (`~a) :: B)::Q)
| orL_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                 (A B : seq (@expr R Bool_T_def))
                 (a b: @expr R Bool_T_def),
    seq_calc_luka' ( ( A |- B):: Q) -> 
    seq_calc_luka' (((a :: b :: A) |-  ldl_bool def false :: B) :: Q) ->
    seq_calc_luka' ((((a `\/ b) :: A) |- B) :: Q)
| orR_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                 (A B : seq (@expr R Bool_T_def))
                 (a b: @expr R Bool_T_def),
    seq_calc_luka' ( ( A |- B):: Q) -> 
    seq_calc_luka' (((ldl_bool def false :: A) |-  a :: b :: B) :: Q) ->
    seq_calc_luka' ((( A) |- (a `\/ b) :: B) :: Q)
.


Definition eval_luka'  (Q : seq (@expr R Bool_T_def))
  := 1%R + (\sum_(i <- Q) ([[i]]_Lukasiewicz - 1%R)).

Lemma eval_luka_add_el' (Q : seq (@expr R Bool_T_def)) (q : (@expr R Bool_T_def)) :
  eval_luka' (q :: Q) = eval_luka' Q + [[q]]_Lukasiewicz  - 1.
Proof.
rewrite /eval_luka'//=. rewrite big_cons//=. 
lra.
Qed.

Lemma eval_luka_add' (Q P : seq (@expr R Bool_T_def)) :
  eval_luka' (P ++ Q) = eval_luka' P + eval_luka' Q  - 1.
Proof.
rewrite /eval_luka'//=. rewrite big_cat. 
have helper : GRing.GRing_add__canonical__Monoid_Law R
     (\big[GRing.GRing_add__canonical__Monoid_Law R/0%R]_(i <- P) ([[i]]_Lukasiewicz - 1)%R)
     (\big[GRing.GRing_add__canonical__Monoid_Law R/0%R]_(i <- Q) ([[i]]_Lukasiewicz - 1)%R) = 
     (\big[GRing.GRing_add__canonical__Monoid_Law R/0%R]_(i <- P) ([[i]]_Lukasiewicz - 1)%R) +
     (\big[GRing.GRing_add__canonical__Monoid_Law R/0%R]_(i <- Q) ([[i]]_Lukasiewicz - 1)%R). {
  auto.}
rewrite helper !addrA.
have helper1:
  (1%R + (\sum_(i <- P) ([[i]]_Lukasiewicz - 1))%R + 1%R + (\sum_(i <- Q) ([[i]]_Lukasiewicz - 1))%R)%E - 1 
=  (1%R + (\sum_(i <- P) ([[i]]_Lukasiewicz - 1))%R + ((\sum_(i <- Q) ([[i]]_Lukasiewicz - 1))%R))%E. {
lra. }
rewrite helper1.
have big_sum' : forall (P : seq (expr Bool_T_def)),
 \big[GRing.GRing_add__canonical__Monoid_Law R/0%R]_(i <- P) ([[i]]_Lukasiewicz - 1)%R  = 
                  (\sum_(i <- P) ([[i]]_Lukasiewicz - 1))%R . {
by rewrite unlock//=.}
rewrite !big_sum'. lra.
Qed.

Lemma eval_luka1' (Q : seq (@expr R Bool_T_def)):
  eval_luka' Q <= 1.
Proof.
rewrite /eval_luka'.
have helper : forall (a : R), a<= 0 -> 1 + a <= 1. {intros. lra.}.
rewrite helper//=. 
rewrite sumr_le0//=. move => i _.
have h := @translate_Bool_T_01 R p Lukasiewicz (i).
have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
apply le_double in h. destruct h as [_ i1].
lra.
Qed.

Lemma le_or : forall (a b : R), a <= b \/ a >= b.
Proof.
 intros. lra.
Qed.

Lemma sound_luka_impl (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
seq_calc_luka_impl Q -> 
exists (q : ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
  q \in Q /\ (eval_luka' (fst q) <= eval_luka' (snd q)).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite //= mem_head. split. by [].  
  simpl. by lra.
- exists ([::] |- [::]). 
  rewrite mem_head.  split. by []. 
  rewrite /eval_luka'//=.
- destruct IHseq_calc_luka_impl as [M [IH1 IH2]]. 
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
- destruct IHseq_calc_luka_impl as [q [IH1 IH2]].
  exists q. rewrite mem_cat IH1 orTb.
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_luka_impl as [M [IH1 IH2]].   
  exists M. rewrite !mem_cat in IH1. 
  rewrite mem_cat. move/orP : IH1. 
  move => [h |/orP h].  rewrite h ?orbT; split; rewrite//=. 
  move: h. move => [h | h]; rewrite h ?orbT; split; rewrite//=.
- destruct IHseq_calc_luka_impl as [q [IH1 IH2]].
   rewrite in_cons in IH1. 
   move/orP : IH1. 
  move => [/eqP h | h].
  + exists (A ++ C |- B).
    subst. rewrite //= in IH2.
    rewrite in_cons eq_refl orTb. split. by [].
    rewrite //= eval_luka_add'.
    have hc := eval_luka1' C.
    lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=. 
- destruct IHseq_calc_luka_impl as [q1 [IH1 IH2]]. 
  rewrite in_cons in IH1. move/orP : IH1.
  move => [h1 | h2]; first last.
  + exists q1. rewrite !in_cons h2 !orbT.
    split; rewrite//=. 
  + move/eqP : h1.
    move => h1. 
    subst. rewrite !eval_luka_add' in IH2.
    have helper : 
      (eval_luka' A + eval_luka' B)%E - 1 <= (eval_luka' C + eval_luka' D)%E - 1 ->
      (eval_luka' A + eval_luka' B)%E - eval_luka' D - 1 <= ( eval_luka' C)%E  - 1 . {
    intros. 
    lra. }
    apply helper in IH2.
    move: helper. move =>_.
    have h1 := le_or (1 + eval_luka' B) (1 + eval_luka' D).
    destruct h1 as [h1 | h1].
    * exists (B |- D). split. 
      - by rewrite !in_cons eq_refl !orbT. 
      - by rewrite  //=; lra.
    * exists (A |- C). split. 
      - by rewrite !in_cons eq_refl !orTb. 
      - rewrite  //=.
        have helper : forall (D' B' : R), 1 + D' <= 1 + B' -> (B' - D' >= 0). {
        intros. lra.}
      apply helper in h1.
      have helper2 : forall (A' B' C' D' : R), 0 <= B' - D' ->
        A' + B' - D' - 1 <= C'-1 ->
        A'  <=  C' . {
        intros. lra.} 
      have hh := helper2 (eval_luka' A) (eval_luka' B) (eval_luka' C) (eval_luka' D).
      by rewrite (hh h1 IH2).
- destruct IHseq_calc_luka_impl1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_luka_impl2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + exists (A ++ B |- C ++ D). 
    rewrite mem_head. split. by [].
    subst.
    rewrite //= in IH12. 
    rewrite //= in IH22. 
    rewrite //=. 
    have IH := lerD IH12 IH22.
    rewrite !eval_luka_add'. lra.
  + exists q1. 
    by rewrite in_cons h1 IH12 orbT//=. 
  + exists q2. 
    by rewrite in_cons h2 IH22 orbT//=. 
  + exists q1. 
    by rewrite in_cons h1 IH12 orbT//=. 
- destruct IHseq_calc_luka_impl as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h | h].
  + subst. exists ((X ++ B ++ A ++ Y |- C)).
    rewrite mem_head. split. by [].
    rewrite//= !eval_luka_add' in IH2.
    rewrite//= !eval_luka_add'. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- destruct IHseq_calc_luka_impl as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h | h].
  + subst. exists (C |- X ++ B ++ A ++ Y).
    rewrite mem_head. split. by [].
    rewrite//= !eval_luka_add' in IH2.
    rewrite//= !eval_luka_add'. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- exists (ldl_bool def false :: A |- [:: b]).
  rewrite mem_head. split. by [].
  rewrite //= !eval_luka_add_el' addr0.
  have h := eval_luka1' A.
  have hb := @translate_Bool_T_01 R p Lukasiewicz (b).
  have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
  apply le_double in hb. destruct hb as [b0 b1].
  have helper : 0 <= (eval_luka' [::] + [[b]]_Lukasiewicz)%E - 1 ->
                eval_luka' A - 1 <= (eval_luka' [::] + [[b]]_Lukasiewicz)%E - 1. {
    intros. lra. }
  apply helper. rewrite /eval_luka'//= big_nil addr0.
  lra.
- destruct IHseq_calc_luka_impl as [q1 [IH1 IH2]]. 
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h1 | h2].
  + exists (a `=> b :: B |- A).
    rewrite mem_head. split. by [].
    subst.
    rewrite //= !eval_luka_add_el' in IH2.
    rewrite //= !eval_luka_add_el'//=/minr.
    case: ifP; move=>h; lra.
  + exists q1. rewrite !in_cons h2 !orbT.
    split; rewrite//=.
- destruct IHseq_calc_luka_impl1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_luka_impl2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + exists (A |- a `=> b :: B).
    rewrite mem_head. split. by [].
    subst.
    rewrite //= eval_luka_add_el'//=/minr.
    rewrite //= in IH12.
    rewrite //= !eval_luka_add_el' in IH22.
    case: ifP; move => h; lra.
  + exists q1. 
    by rewrite in_cons h1 IH12 orbT//=. 
  + exists q2. 
    by rewrite in_cons h2 IH22 orbT//=. 
  + exists q1. 
    by rewrite in_cons h1 IH12 orbT//=. 
Qed.

Lemma sound_luka (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
seq_calc_luka' Q -> 
exists (q : ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
  q \in Q /\ (eval_luka' (fst q) <= eval_luka' (snd q)).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite //= mem_head. split. by [].  
  simpl. by lra.
- exists ([::] |- [::]). 
  rewrite mem_head.  split. by []. 
  rewrite /eval_luka'//=.
- destruct IHseq_calc_luka' as [M [IH1 IH2]]. 
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
- destruct IHseq_calc_luka' as [q [IH1 IH2]].
  exists q. rewrite mem_cat IH1 orTb.
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_luka' as [M [IH1 IH2]].   
  exists M. rewrite !mem_cat in IH1. 
  rewrite mem_cat. move/orP : IH1. 
  move => [h |/orP h].  rewrite h ?orbT; split; rewrite//=. 
  move: h. move => [h | h]; rewrite h ?orbT; split; rewrite//=.
- destruct IHseq_calc_luka' as [q [IH1 IH2]].
   rewrite in_cons in IH1. 
   move/orP : IH1. 
  move => [/eqP h | h].
  + exists (A ++ C |- B).
    subst. rewrite //= in IH2.
    rewrite in_cons eq_refl orTb. split. by [].
    rewrite //= eval_luka_add'.
    have hc := eval_luka1' C.
    lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=. 
- destruct IHseq_calc_luka' as [q1 [IH1 IH2]]. 
  rewrite in_cons in IH1. move/orP : IH1.
  move => [h1 | h2]; first last.
  + exists q1. rewrite !in_cons h2 !orbT.
    split; rewrite//=. 
  + move/eqP : h1.
    move => h1. 
    subst. rewrite !eval_luka_add' in IH2.
    have helper : 
      (eval_luka' A + eval_luka' B)%E - 1 <= (eval_luka' C + eval_luka' D)%E - 1 ->
      (eval_luka' A + eval_luka' B)%E - eval_luka' D - 1 <= ( eval_luka' C)%E  - 1 . {
    intros. 
    lra. }
    apply helper in IH2.
    move: helper. move =>_.
    have h1 := le_or (1 + eval_luka' B) (1 + eval_luka' D).
    destruct h1 as [h1 | h1].
    * exists (B |- D). split. 
      - by rewrite !in_cons eq_refl !orbT. 
      - by rewrite  //=; lra.
    * exists (A |- C). split. 
      - by rewrite !in_cons eq_refl !orTb. 
      - rewrite  //=.
        have helper : forall (D' B' : R), 1 + D' <= 1 + B' -> (B' - D' >= 0). {
        intros. lra.}
      apply helper in h1.
      have helper2 : forall (A' B' C' D' : R), 0 <= B' - D' ->
        A' + B' - D' - 1 <= C'-1 ->
        A'  <=  C' . {
        intros. lra.} 
      have hh := helper2 (eval_luka' A) (eval_luka' B) (eval_luka' C) (eval_luka' D).
      by rewrite (hh h1 IH2).
- destruct IHseq_calc_luka'1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_luka'2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + exists (A ++ B |- C ++ D). 
    rewrite mem_head. split. by [].
    subst.
    rewrite //= in IH12. 
    rewrite //= in IH22. 
    rewrite //=. 
    have IH := lerD IH12 IH22.
    rewrite !eval_luka_add'. lra.
  + exists q1. 
    by rewrite in_cons h1 IH12 orbT//=. 
  + exists q2. 
    by rewrite in_cons h2 IH22 orbT//=. 
  + exists q1. 
    by rewrite in_cons h1 IH12 orbT//=. 
- destruct IHseq_calc_luka' as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h | h].
  + subst. exists ((X ++ B ++ A ++ Y |- C)).
    rewrite mem_head. split. by [].
    rewrite//= !eval_luka_add' in IH2.
    rewrite//= !eval_luka_add'. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- destruct IHseq_calc_luka' as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h | h].
  + subst. exists (C |- X ++ B ++ A ++ Y).
    rewrite mem_head. split. by [].
    rewrite//= !eval_luka_add' in IH2.
    rewrite//= !eval_luka_add'. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- exists (ldl_bool def false :: A |- [:: b]).
  rewrite mem_head. split. by [].
  rewrite //= !eval_luka_add_el' addr0.
  have h := eval_luka1' A.
  have hb := @translate_Bool_T_01 R p Lukasiewicz (b).
  have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
  apply le_double in hb. destruct hb as [b0 b1].
  have helper : 0 <= (eval_luka' [::] + [[b]]_Lukasiewicz)%E - 1 ->
                eval_luka' A - 1 <= (eval_luka' [::] + [[b]]_Lukasiewicz)%E - 1. {
    intros. lra. }
  apply helper. rewrite /eval_luka'//= big_nil addr0.
  lra.
- exists (A |- [:: ldl_bool def true]).
  rewrite mem_head. split. by [].
  rewrite //= !eval_luka_add_el'//= . 
  have h := eval_luka1' A.
  have helper : (eval_luka' [::] + 1%R)%E - 1 = 1. {
    rewrite /eval_luka' big_nil addr0. lra.
  }
  by rewrite helper h.
(*andL_l*)
- destruct IHseq_calc_luka'1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_luka'2 as [q2 [IH21 IH22]].
   rewrite in_cons in IH21.  rewrite in_cons in IH11.
   move/orP: IH21.
   move/orP: IH11.
   move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    exists (a `/\ b :: B |- A). rewrite //= in IH22. 
    rewrite eval_luka_add_el'//= in IH22.
    rewrite mem_head. split. by []. 
    rewrite addr0 in IH22.
    rewrite //= in IH12.
    rewrite !eval_luka_add_el' in IH12.
    rewrite eval_luka_add_el'.
    have h := @translate_Bool_T_01 R p Lukasiewicz (a `/\ b).
    have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
    apply le_double in h. destruct h as [ab0 ab1].
    rewrite//=/sumR big_cons big_seq1 /maxr.
    case: ifP; move => h_max.
    * rewrite addr0. by apply IH22.
    * rewrite addrA.
      have hh : (eval_luka' B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E - 1 = 
                (((eval_luka' B + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1. {lra. }
      by rewrite hh  IH12.
  + exists q2. 
    by rewrite in_cons h1 IH22 orbT//=. 
  + exists q1. 
    by rewrite in_cons h2 IH12 orbT//=. 
  + exists q1. 
    by rewrite in_cons h2 IH12 orbT//=. 
- destruct IHseq_calc_luka'2 as [q [IH1 IH2]].
  rewrite in_cons in_cons in IH1. move/orP: IH1.
  move => [/eqP h |/orP [/eqP h | h]].
  +  exists (A |- a `/\ b :: B);
                     rewrite mem_head; split; rewrite//=.
    * subst. rewrite //= in IH2.
      rewrite !eval_luka_add_el' in IH2.
      rewrite eval_luka_add_el'.
      have h := @translate_Bool_T_01 R p Lukasiewicz (a `/\ b).
      have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
      apply le_double in h. destruct h as [ab0 ab1].
      rewrite//=/sumR big_cons big_seq1 /maxr.
      case: ifP; move => h_max.
      + rewrite addr0.
        have hh : ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E = 
                 (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1)%R. {
        set (e := ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E) in *.
        lra.
        }
        rewrite hh in h_max. move: hh. move => _.
        have hh : eval_luka' A <= (((eval_luka' B + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1 ->
                  ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 < 0 ->
                  eval_luka' A <= eval_luka' B -1. {lra.}
        by  rewrite (hh IH2 h_max).
      + rewrite //= in h_max.
        * have hh : 
             (eval_luka' B + ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R))%E - 1 = 
              (((eval_luka' B + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1. {lra.}
          rewrite hh.
          by rewrite  IH2.
    * exists (A |- a `/\ b :: B);
                     rewrite mem_head; split; rewrite//=.
      subst. rewrite //= in IH2.
      rewrite eval_luka_add_el'.
      rewrite eval_luka_add_el'//= addr0 in IH2.
      have h := @translate_Bool_T_01 R p Lukasiewicz (a `/\ b).
      have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
      apply le_double in h. destruct h as [ab0 ab1].
      lra.      
  + exists q. 
    by rewrite in_cons h orbT IH2.
- destruct IHseq_calc_luka' as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP: IH1.
  move => [/eqP h | h].
  + subst.
    exists ((`~ a) :: A |- B).
    rewrite mem_head; split; rewrite//=.
    rewrite //= !eval_luka_add_el' //= addr0 in IH2.
    rewrite eval_luka_add_el'//=. 
    lra.
  + exists q. 
    by rewrite in_cons h orbT IH2.
-  destruct IHseq_calc_luka'2 as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP: IH1.
  move => [/eqP h | h].
  + subst.
    exists (A |- (`~ a) :: B).
    rewrite mem_head; split; rewrite//=.
    rewrite //= !eval_luka_add_el' //= addr0 in IH2.
    rewrite eval_luka_add_el'//=. 
    lra.
  + exists q. 
    by rewrite in_cons h orbT IH2.
- destruct IHseq_calc_luka'2 as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP: IH1.
  move => [/eqP h | h].
  + subst. 
    rewrite//= !eval_luka_add_el'//= addr0 in IH2. 
    exists (a `\/ b :: A |- B).
    rewrite mem_head; split; rewrite//=.
    rewrite eval_luka_add_el'//= /sumR big_cons big_seq1 /minr.
    case: ifP; move => h_min.
    *  have helper : (eval_luka' A + ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz))%E - 1 -1 <= 
                       eval_luka' B -1 ->
                     (eval_luka' A + ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz))%E - 1 <=
                       eval_luka' B . { intros. lra.}
       rewrite helper//=. lra.
    * have triv : (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E < 1) = false ->
                  (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E >= 1). {intros. lra.}
      apply triv in h_min.
      have helper :  
                      (((eval_luka' A + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1 <= 
                        eval_luka' B - 1 ->
                      (((eval_luka' A %R )%E)%R)%E  <= 
                        eval_luka' B . {intros. lra.}
      apply helper in IH2.
      lra. 
  + exists q. 
    by rewrite in_cons h orbT IH2.
- destruct IHseq_calc_luka'1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_luka'2 as [q2 [IH21 IH22]].
   rewrite in_cons in IH21.  rewrite in_cons in IH11.
   move/orP: IH21.
   move/orP: IH11.
   move => [/eqP h1 | h1]; move => [/eqP h2 | h2].
   + subst. 
     exists (A |- a `\/ b :: B). 
     rewrite mem_head. split. by []. 
     rewrite //= in IH22. rewrite //= in IH12. 
     rewrite !eval_luka_add_el'//= in IH22.
     rewrite addr0 in IH22.
     rewrite //= eval_luka_add_el'//=.
     rewrite//=/sumR big_cons big_seq1 /minr.
     case: ifP; move => h_min.
     * have  helper : eval_luka' A - 1 <= 
                        (((eval_luka' B + [[b]]_Lukasiewicz)%E - 1)%R + [[a]]_Lukasiewicz)%E - 1 ->
                      eval_luka' A <=
                        (((eval_luka' B + ([[a]]_Lukasiewicz)%E)%R + [[b]]_Lukasiewicz))%E - 1.
       {intros. lra.}
       apply helper in IH22.
(*there has to be a simpler way to do this, find one*)
       have really : (eval_luka' B + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 =
                     (eval_luka' B + ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz))%E - 1. {lra.}
       rewrite -really.
       by rewrite IH22.
     * move : IH22. move => _.
       lra.
  + exists q2. 
    by rewrite in_cons h2 IH22 orbT//=. 
  + exists q1. 
    by rewrite in_cons h1 IH12 orbT//=. 
  + exists q1. 
    by rewrite in_cons h1 IH12 orbT//=.
Qed.

Lemma luka_neg_impl_admissable (e : @expr R Bool_T_def):
 [[`~ e]]_Lukasiewicz = [[e `=> ldl_bool def false]]_Lukasiewicz.
Proof.
rewrite//= addr0 /minr. case: ifP; intros.
- lra. 
- have h := @translate_Bool_T_01 R p Lukasiewicz (e).
  lra.
Qed.

Lemma luka_true_false_admissable :
  [[@ldl_bool R def true]]_Lukasiewicz = [[`~ ldl_bool def false]]_Lukasiewicz.
Proof.
by rewrite//= subr0.
Qed.


Lemma luka_and_impl_admissable (a b: @expr R Bool_T_def):
  [[a `/\ b]]_Lukasiewicz = [[`~ (a `=> `~b)]]_Lukasiewicz.
Proof.
rewrite//=/maxr/minr.
case: ifP; case: ifP; rewrite//= => h1 h2; try lra.
- rewrite /sumR !big_cons big_nil addr0 in h2. 
  have ha := @translate_Bool_T_01 R p Lukasiewicz (a).
  have hb := @translate_Bool_T_01 R p Lukasiewicz (b).
  have helper1 : ((1 - [[a]]_Lukasiewicz)%R + (1 - [[b]]_Lukasiewicz)%R)%E < 1 ->
                 [[a]]_Lukasiewicz + [[b]]_Lukasiewicz > 1. {intros. lra.}
  apply helper1 in h1.
  have helper2 : ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E < 0 ->
            [[a]]_Lukasiewicz + [[b]]_Lukasiewicz < 1. {intros. lra.}
  apply helper2 in h2.
  lra.
- rewrite /sumR !big_cons big_nil addr0 in h2.
  rewrite /sumR !big_cons big_nil addr0. 
  have helper : 1 - ((1 - [[a]]_Lukasiewicz)%R + (1 - [[b]]_Lukasiewicz)%R)%E = 
                  1 - ((2 - [[a]]_Lukasiewicz - [[b]]_Lukasiewicz)%R)%E. {lra.}
  rewrite helper.
  have helper2 : 1 - (2 - [[a]]_Lukasiewicz - [[b]]_Lukasiewicz) =
                   -1 + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz. {lra.}
  rewrite helper2.
  have helper3 : ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E = 
                   ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1. {lra.}
  rewrite helper3. lra.
- rewrite /sumR !big_cons big_nil addr0 in h2.
  rewrite /sumR !big_cons big_nil addr0//=.
  have helper3 : ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E = 
                   ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1. {lra.}
  rewrite helper3//=. rewrite helper3 in h2.
  have helper : (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 < 0) = false ->
                ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E  >= 1. {intros. lra.}
  apply helper in h2.
  have helper2 : (((1 - [[a]]_Lukasiewicz)%R + (1 - [[b]]_Lukasiewicz)%R)%E < 1) = false ->
                 [[a]]_Lukasiewicz + [[b]]_Lukasiewicz <= 1.  {intros. lra.}
  apply helper2 in h1.
  lra. 
Qed.

Lemma luka_or_impl_admissable (a b: @expr R Bool_T_def):
  [[a `\/ b]]_Lukasiewicz = [[(`~a) `=> b]]_Lukasiewicz.
Proof.
rewrite//=/maxr/minr.
have helper : ((1 - (1 - [[a]]_Lukasiewicz))%R + [[b]]_Lukasiewicz)%E =
                   [[a]]_Lukasiewicz + [[b]]_Lukasiewicz. {lra.}
case: ifP; case: ifP; rewrite//= => h1 h2.
- rewrite /sumR !big_cons big_nil addr0.
  by rewrite helper//=.
- rewrite /sumR !big_cons big_nil addr0.
  rewrite helper in h1.
  rewrite /sumR !big_cons big_nil addr0 in h2.
  have helper1 : (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E < 1) = false ->
                  (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E >= 1). {intros. lra.}
  apply helper1 in h1.
  exfalso.
  have contra' : 1 <= ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E ->
                 ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E < 1 ->
                 False. {intros. lra.}
  have H := contra' h1 h2. move: H.
  by contra.
- rewrite /sumR !big_cons big_nil addr0 in h2.
  rewrite helper.
  have helper1 : (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E < 1) = false ->
                  (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E >= 1). {intros. lra.}
  apply helper1 in h2.
  rewrite helper in h1.
  lra.
Qed.

(*specific exchange rules for simpler cases*)

Lemma luka_eex_nil: forall (Q P: seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka_impl (P ++ Q) ->
    seq_calc_luka_impl (Q ++ P).
Proof.
intros.
have hxy X Y : X ++ Y = [::] ++ X ++ Y ++ [::].
{rewrite//= cats0//=.}
rewrite (hxy _  P Q) in H.
rewrite (hxy _  Q P).
apply eex_l.
by exact H.
Qed.


Lemma luka_exL_nil: forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_luka_impl (((A ++ B) |- C) :: Q) ->
    seq_calc_luka_impl (((B ++ A) |- C) :: Q).
Proof.
intros.
have hxy X Y : X ++ Y = [::] ++ X ++ Y ++ [::].
{rewrite//= cats0//=.}
rewrite (hxy _  A B) in H.
rewrite (hxy _  B A).
apply exL_l.
by exact H.
Qed.

Lemma luka_exR_nil: forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_luka_impl ((C |- (A ++ B)) :: Q) ->
    seq_calc_luka_impl ((C |- (B ++ A)) :: Q).
Proof.
intros.
have hxy X Y : X ++ Y = [::] ++ X ++ Y ++ [::].
{rewrite//= cats0//=.}
rewrite (hxy _  A B) in H.
rewrite (hxy _  B A).
apply exR_l.
by exact H.
Qed.


(*an alternate derivable implication rule*)
Lemma luka_implL_extended:
  forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                   (A B : seq (@expr R Bool_T_def))
                   (a b : @expr R Bool_T_def),
    seq_calc_luka_impl ((B |- A) ::(( b :: B) |- a:: A) :: Q ) ->
    seq_calc_luka_impl ((((a `=> b) :: B) |- A) :: Q).
Proof.
intros. rewrite -cat1s.
apply luka_eex_nil.
apply ec_l.
rewrite -(cat1s (a `=> b) B).
apply luka_eex_nil.
apply luka_exL_nil.
apply w_l.
rewrite -(cat1s _ Q). rewrite -cat1s.
apply luka_eex_nil. rewrite -catA. 
apply (@luka_eex_nil _ (Q ++ [:: B |- A])).
apply luka_eex_nil.
apply implL_l.
rewrite -cat1s.
rewrite -cat1s -(cat1s _ Q) in H.
apply (@luka_eex_nil ([:: b :: B |- a :: A] ++ Q) _ ) in H.
rewrite -catA in H.
by exact H.
Qed.


Lemma equivalence_luka (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
  seq_calc_luka' Q -> seq_calc_luka_impl Q.
Proof.
intros.
dependent induction H. 
- apply id_l.
- apply empty.
- apply eex_l. by exact IHseq_calc_luka'.
- apply ew_l. by exact IHseq_calc_luka'.
- apply ec_l. by exact IHseq_calc_luka'.
- apply w_l. by exact IHseq_calc_luka'.
- apply split_l. by exact IHseq_calc_luka'.
- apply mix_l. 
  + by exact IHseq_calc_luka'1.
  + by exact IHseq_calc_luka'2. 
- apply exL_l. by exact IHseq_calc_luka'.
- apply exR_l. by exact IHseq_calc_luka'.
- apply bot_l. 
- rewrite true_false. rewrite neg_impl.
  apply implR_l.
  + have h : [::] ++ A = A. {rewrite//=.}
    rewrite -h. 
    apply w_l. apply empty.
  + apply bot_l.
- rewrite and_impl. rewrite neg_impl.
  apply implL_l. apply implR_l.
  + by exact IHseq_calc_luka'2.
  + rewrite neg_impl. apply implR_l.
    * have helper : [:: a, ldl_bool def false & B] = [:: a] ++ ( ldl_bool def false :: B). {
                        rewrite//=.}
      rewrite helper.
      apply luka_exL_nil. apply w_l.
      by exact IHseq_calc_luka'2.
    * have helper : [:: b, a, ldl_bool def false & B] = [:: b; a] ++ (ldl_bool def false :: B). {
                        rewrite//=.}
      rewrite helper.
      apply luka_exL_nil.
      move: helper. move => _.
      have helper : (ldl_bool def false :: B) ++ [:: b; a] = [::ldl_bool def false] ++ B ++ [:: b; a ]. {
        rewrite//=. }
      rewrite helper.
      have cons_help (X : seq (expr (Bool_T def)))  :
        ldl_bool def false :: X = [:: ldl_bool def false] ++ X. {rewrite//=.}
      rewrite (cons_help _ A).
      apply mix_l.
      - 
        apply id_l.
      - move: helper. move => _.
        have helper: [:: b] ++[:: a] ++ [::] = [:: b; a]. {rewrite//=. }
        rewrite -helper. apply exL_l. rewrite cats0. 
        apply (@luka_exL_nil _ ([:: a] ++ [:: b]) B).
        have helper1 : [:: a, b & B] = ([:: a] ++ [:: b]) ++ B. {rewrite//=.}
        rewrite helper1 in IHseq_calc_luka'1.
        by exact IHseq_calc_luka'1.
- rewrite and_impl. rewrite neg_impl.
  apply implR_l.
  + by exact IHseq_calc_luka'1.
  + apply luka_implL_extended. rewrite neg_impl.
    have helper : [:: A |- ldl_bool def false :: B, 
                     b `=> ldl_bool def false ::A |- [:: a, ldl_bool def false & B] & Q] = 
                    [:: A |- ldl_bool def false :: B] ++ ((
                       b `=> ldl_bool def false :: A |- [:: a, ldl_bool def false & B]) :: Q).
    rewrite//=. 
    rewrite helper.
    apply luka_eex_nil. rewrite//=. 
    apply luka_implL_extended.
    have helper1 : [:: A |- [:: a, ldl_bool def false & B], ldl_bool def false :: A |- [:: b, a, ldl_bool def false & B]
      & Q ++ [:: A |- ldl_bool def false :: B]] = 
                     [:: A |- [:: a, ldl_bool def false & B]] ++
                       (( ldl_bool def false :: A |- [:: b, a, ldl_bool def false & B]) ::
      Q ++ [:: A |- ldl_bool def false :: B]).
    rewrite//=.
    rewrite helper1.
    apply luka_eex_nil.
    apply ew_l .
    have helper2 : (ldl_bool def false :: A |- [:: b, a, ldl_bool def false & B]) = 
                     ([::ldl_bool def false] ++ A |- [:: b] ++[:: a]++[:: ldl_bool def false] ++ B).
    rewrite//=.
    rewrite helper2. move: helper helper1 helper2. move => _ _ _.
    apply exR_l. apply(@luka_exR_nil _ ([:: ldl_bool def false] ++ [:: a] ++ B) ([:: b])).
    have helper : ([:: ldl_bool def false] ++ [:: a] ++ B) ++ [:: b] = 
                  ([:: ldl_bool def false]) ++ ([:: a] ++ B ++ [:: b]).
    rewrite//=. rewrite helper.
    apply mix_l.
    * apply  id_l.
    * rewrite catA. apply luka_exR_nil.
      have helper1 : [:: b] ++ [:: a] ++ B = [::] ++ [:: b] ++ [:: a] ++ B.
      rewrite//=. rewrite helper1.
      apply exR_l. rewrite//=.
      have helper2 : ((A |- [:: a, b & B]) :: Q ++ [:: A |- ldl_bool def false :: B]) = 
                       ([::A |- [:: a, b & B]] ++ Q ++ [:: A |- ldl_bool def false :: B] ++ [::]).
      rewrite//=. rewrite helper2.
      move: helper helper1 helper2. move => _ _ _.
      apply eex_l.
      by rewrite cats0 //=. 
- rewrite neg_impl. apply implL_l.
  by exact IHseq_calc_luka'.
- rewrite neg_impl. apply implR_l.
  + by exact IHseq_calc_luka'1.
  + by exact IHseq_calc_luka'2.
- rewrite or_impl. apply luka_implL_extended.
  rewrite neg_impl. 
  have helper : [:: A |- B, b :: A |- a `=> ldl_bool def false :: B & Q] =
                  [:: A |- B] ++ ((b :: A |- a `=> ldl_bool def false :: B) :: Q). {
                    rewrite//=.}
  rewrite helper.
  apply luka_eex_nil. rewrite //=.
  apply implR_l.
  + have mini_helper : forall X x, x :: X = [::x] ++ X. rewrite//=. 
    rewrite (mini_helper _ A b). apply luka_exL_nil.
    apply w_l. 
    rewrite (mini_helper _ (Q ++ [:: A |- B]) (A |- B)).
    rewrite catA.
    apply ew_l. 
    rewrite -(mini_helper _ Q ( A |- B)).
    by exact IHseq_calc_luka'1.
  + have helper1 : (([:: a, b & A] |- ldl_bool def false :: B) :: Q ++ [:: A |- B]) = 
                    ((([:: a, b & A] |- ldl_bool def false :: B) :: Q) ++ [:: A |- B]).
    rewrite//=.
    rewrite helper1.
    apply ew_l. 
    by exact  IHseq_calc_luka'2.
- rewrite or_impl. apply implR_l.
  + by exact IHseq_calc_luka'1.
  + rewrite neg_impl.  apply implL_l.
    by exact IHseq_calc_luka'2.
Qed.


End hypersequent_lukasiewicz.

Section hypersequent_product.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope mset_scope. 
Context {R : realType}.
Context {K : choiceType}.
Implicit Types  (A : {mset K}) (s : seq K).
Variable p : R. 
Local Notation "[[ e ]]_ l" := (@translation R l p _ e).

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).

(*small-language fragment*)
Inductive seq_calc_product :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))
      -> Prop :=
| id_p : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                (A : seq (@expr R Bool_T_def)),
    seq_calc_product ( (A |- A) :: Q)
| empty_p : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
     seq_calc_product (([::] |- [::]) :: Q)
(*structural*)
| eex_p : forall (Q P S1 S2: seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_product (S1 ++ P ++ Q ++ S2) ->
    seq_calc_product (S1 ++ Q ++ P ++ S2)
| ew_p : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_product Q ->
    seq_calc_product (Q ++ P) 
| ec_p : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_product (Q ++ P ++ P) ->
    seq_calc_product (Q ++ P)
(*add split and mix rules*)
| split_p : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C D: seq (@expr R Bool_T_def)),
    seq_calc_product (((A ++ B) |- (C ++ D)) :: Q) ->
    seq_calc_product ((A |- C) ::  (B |- D) :: Q)
| mix_p : forall   (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C D: seq (@expr R Bool_T_def)),
    seq_calc_product ((A |- C) :: Q) ->
    seq_calc_product ((B |- D) :: Q) ->
    seq_calc_product (((A ++ B) |- (C ++ D)) :: Q)
| exL_p : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_product (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_product (((X ++ B ++ A ++ Y) |- C) :: Q) 
| exR_p : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_product ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_product ((C |- (X ++ B ++ A ++ Y)) :: Q)
| w_p : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_product ((A |- B) :: Q) ->
    seq_calc_product ((A ++ C |- B) :: Q)
(*logical*)
| bot_p : forall   (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B: seq (@expr R Bool_T_def))
                 (b : @expr R Bool_T_def),
    seq_calc_product (((ldl_bool def false :: A) |- B) :: Q)
| andL_p : forall Q
                   (A B : seq (@expr R Bool_T_def))
                   (a b : @expr R Bool_T_def),
    seq_calc_product (((a :: b :: B) |- A) :: Q ) ->
    seq_calc_product ((((a `/\ b) :: B) |- A) :: Q )
| andR_p : forall Q
                  (A B : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_product ( (A |- a :: b ::B) :: Q ) ->
    seq_calc_product ((A |- (a `/\ b):: B ) :: Q )
| negL_p : forall Q
                  (A B  : seq (@expr R Bool_T_def))
                  (a  : @expr R Bool_T_def),
    seq_calc_product ((B |- [::a]) :: Q) ->
    seq_calc_product (  (((`~a) :: B) |- A) :: Q)
| implR_p : forall Q
                  (A B : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_product ((A |- B) :: Q) ->
    seq_calc_product ((a :: A |- b :: B) :: Q ) ->
    seq_calc_product (( A |- (a `=> b) :: B) :: Q )
| implL_p : forall Q
                  (A B : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
      seq_calc_product (((`~ a) :: A |- B) :: Q) ->
      seq_calc_product ((b :: A |- a :: B) :: Q ) ->
      seq_calc_product (((a `=> b) :: A |-  B) :: Q )
.

(*LDL language*)
Inductive seq_calc_product' :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))
      -> Prop :=
| id_p' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                (A : seq (@expr R Bool_T_def)),
    seq_calc_product' ( (A |- A) :: Q)
| empty_p' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
     seq_calc_product' (([::] |- [::]) :: Q)
(*structural*)
| eex_p' : forall (Q P S1 S2: seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_product' (S1 ++ P ++ Q ++ S2) ->
    seq_calc_product' (S1 ++ Q ++ P ++ S2)
| ew_p' : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_product' Q ->
    seq_calc_product' (Q ++ P) 
| ec_p' : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_product' (Q ++ P ++ P) ->
    seq_calc_product' (Q ++ P)
(*add split and mix rules*)
| split_p' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C D: seq (@expr R Bool_T_def)),
    seq_calc_product' (((A ++ B) |- (C ++ D)) :: Q) ->
    seq_calc_product' ((A |- C) ::  (B |- D) :: Q)
| mix_p' : forall   (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C D: seq (@expr R Bool_T_def)),
    seq_calc_product' ((A |- C) :: Q) ->
    seq_calc_product' ((B |- D) :: Q) ->
    seq_calc_product' (((A ++ B) |- (C ++ D)) :: Q)
| exL_p' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_product' (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_product' (((X ++ B ++ A ++ Y) |- C) :: Q) 
| exR_p' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_product' ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_product' ((C |- (X ++ B ++ A ++ Y)) :: Q)
| w_p' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_product' ((A |- B) :: Q) ->
    seq_calc_product' ((A ++ C |- B) :: Q)
(*logical*)
| bot_p' : forall   (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B: seq (@expr R Bool_T_def))
                 (b : @expr R Bool_T_def),
    seq_calc_product' (((ldl_bool def false :: A) |- B) :: Q)
| top_p' : forall Q 
                 (A : seq (@expr R Bool_T_def)),
   seq_calc_product' ((A |- [:: (ldl_bool def true)]) :: Q)

| andL_p' : forall Q
                   (A B : seq (@expr R Bool_T_def))
                   (a b : @expr R Bool_T_def),
    seq_calc_product' (((a :: b :: B) |- A) :: Q ) ->
    seq_calc_product' ((((a `/\ b) :: B) |- A) :: Q )
| andR_p' : forall Q
                  (A B : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_product' ( (A |- a :: b ::B) :: Q ) ->
    seq_calc_product' ((A |- (a `/\ b):: B ) :: Q )
(*| orL_p' : forall  Q
                  (A B : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_product' ((A |- B) :: Q) ->
    seq_calc_product' ((a :: b :: A |- ldl_bool def false :: B) :: Q) ->
    seq_calc_product' ( (((a `\/ b) :: A) |- B) :: Q)
| orR_p' : forall Q
                  (A B : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_product' ((A |- a :: B) :: (A |- b:: B)  :: Q) ->
    seq_calc_product' ((A |- (a `\/ b) :: B) :: Q)*)
| negR_p' : forall Q
                  (A B : seq (@expr R Bool_T_def))
                  (a  : @expr R Bool_T_def),
    seq_calc_product' ((A |- B) :: Q) ->
    seq_calc_product' ((a ::A |- ldl_bool def false :: B) :: Q) ->
    seq_calc_product' ((A |- (`~ a):: B) :: Q)
| negL_p' : forall Q
                  (A B  : seq (@expr R Bool_T_def))
                  (a  : @expr R Bool_T_def),
    seq_calc_product' ((B |- [::a]) :: Q) ->
    seq_calc_product' (  (((`~a) :: B) |- A) :: Q).

Definition eval_product  (Q : seq (@expr R Bool_T_def))
  := \prod_(i <- Q) ([[i]]_product).

Lemma eval_product_add (Q P : seq (@expr R Bool_T_def)) :
  eval_product (P ++ Q) = eval_product P * eval_product Q.
Proof.
rewrite /eval_product//=. rewrite big_cat. 
by rewrite unlock//=.
Qed.

Lemma eval_product_add_el (Q : seq (@expr R Bool_T_def)) q :
  eval_product (q :: Q) = ([[q]]_product) * eval_product Q.
Proof.
rewrite /eval_product//=. rewrite big_cons. 
by rewrite //=.
Qed.

Lemma eval_product_01 (Q : seq (@expr R Bool_T_def)) : 
  0 <= eval_product Q <= 1.
Proof.
rewrite /eval_product. 
elim: Q.
- rewrite big_nil; lra.
- move =>  a l H.
  rewrite big_cons.
  have ha := @translate_Bool_T_01 R p product (a).
  have spl : forall (x : R),  0 <= x <= 1 <->
              0  <= x  /\ x <= 1. split; intros; lra.
  apply spl; split; apply (spl) in H; apply spl in ha;
  destruct H as [H0 H1]; destruct ha as [h0 h1]; nra.
Qed.

Lemma eval_product_mul_le (P Q : seq (@expr R Bool_T_def)) :
  eval_product P * eval_product Q <= eval_product P.
Proof.
have hP := eval_product_01 P.
have hQ := eval_product_01 Q.
have hP01 : 0 = eval_product P \/ 0 < eval_product P. lra.
destruct hP01 as [p0 | p1].
- rewrite -p0 mul0r//=.
- nra.
Qed.

Lemma sound_product (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
seq_calc_product Q -> 
exists (q : ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
  q \in Q /\ (eval_product (fst q) <= eval_product (snd q)).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite //= mem_head. split. by [].  
  simpl. by lra.
- exists ([::] |- [::]). 
  rewrite mem_head;  split; first by []. 
  rewrite /eval_product//=.
- destruct IHseq_calc_product as [M [IH1 IH2]]. 
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
- destruct IHseq_calc_product as [q [IH1 IH2]].
  exists q. rewrite mem_cat IH1 orTb.
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_product as [M [IH1 IH2]].   
  exists M. rewrite !mem_cat in IH1. 
  rewrite mem_cat. move/orP : IH1. 
  move => [h |/orP h].  rewrite h ?orbT; split; rewrite//=. 
  move: h. move => [h | h]; rewrite h ?orbT; split; rewrite//=.
- destruct IHseq_calc_product as [q1 [IH1 IH2]]. 
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h1 | h2].
  + subst.
    rewrite //= !eval_product_add in IH2.
    have ha := (eval_product_01 A).
    have hb := (eval_product_01 B).
    have hc := (eval_product_01 C).
    have hd := (eval_product_01 D).
    have [h | h] := le_or (eval_product A) (eval_product C).
    * exists (A |- C). rewrite //= mem_head. split. by [].
      by rewrite h.
    * have helper : eval_product A * eval_product B <= eval_product A * eval_product D. nra.
      have helper1 : forall (a b d : R), a * b <= a * d ->
                                           0 < a ->
                                           b <= d. {intros; nra.}
      have ha' :  0 < eval_product A \/ 0 = eval_product A. lra.
      destruct ha' as [ha' | ha'].
      + exists (B |- D). rewrite //= !in_cons eq_refl orTb orbT. 
        split. by [].
        apply (helper1 _ _ _ helper) in ha'. rewrite//=.
      + exists (A |- C). rewrite //= mem_head. split. by [].
        lra.
  + exists q1. 
    by rewrite !in_cons h2 !orbT IH2//=.    
- destruct IHseq_calc_product1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_product2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + exists (A ++ B |- C ++ D).
    subst.
    rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= !eval_product_add.
    rewrite //= in IH12. rewrite //= in IH22.
    have helper : forall (x : R), 0 <= x <= 1 -> 0 <= x /\ x <= 1. {intros. lra.}
    have mulr_le1 : forall (x y: R), 0 <= x -> 0 <= y -> y <= 1 ->
                                     x * y <= x. {intros. nra.}
    have le_mul : forall ( a b c :R ),  0 <= a -> 0 <= b -> a <= c ->
                                        b <=1 -> a * b <= c * b. {intros. nra.}
    
    have [ha0 ha1] := helper _ (eval_product_01 A).
    have [hb0 hb1] := helper _ (eval_product_01 B).
    have [hc0 hc1] := helper _ (eval_product_01 C).
    have [hd0 hd1] := helper _ (eval_product_01 D).
    apply (le_mul _ _ (eval_product C) ha0 hb0) in IH12; first last. by exact hb1.
    have le_le : forall (a b c d : R),  0 <= a -> 0 <= b -> 0 <= c -> 0 <= d ->
                                        a* b <= c * b -> b <= d -> a * b <= c * d. {
      intros. nra.}
    apply (le_le (eval_product A) (eval_product B) (eval_product C) 
             (eval_product D) ha0 hb0 hc0 hd0) in IH22; first last. by exact IH12.
    by exact IH22.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
- destruct IHseq_calc_product as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h | h].
  + subst. exists ((X ++ B ++ A ++ Y |- C)).
    rewrite mem_head. split. by [].
    rewrite//= !eval_product_add in IH2.
    rewrite//= !eval_product_add. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- destruct IHseq_calc_product as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h | h].
  + subst. exists (C |- X ++ B ++ A ++ Y).
    rewrite mem_head. split. by [].
    rewrite//= !eval_product_add in IH2.
    rewrite//= !eval_product_add. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- destruct IHseq_calc_product as [q [IH1 IH2]].
  rewrite in_cons in IH1. 
  move/orP : IH1. 
  move => [/eqP h | h].
  + exists (A ++ C |- B).
    subst. rewrite //= in IH2.
    rewrite in_cons eq_refl orTb; split; first by [].
    rewrite //= eval_product_add . 
    have hac := eval_product_mul_le A C.
    nra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=. 
- exists (ldl_bool def false :: A |- B).
  rewrite in_cons eq_refl orTb. split. by [].
  rewrite//= /eval_product big_cons//= mul0r.
  have h := eval_product_01 B. rewrite /eval_product in h.
  have helper : forall (x : R), 0 <= x <= 1 -> 0 <= x /\ x <= 1. {intros. lra.}
  apply helper in h. destruct h as [h _].
  by rewrite h.
- destruct IHseq_calc_product as [q1 [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + subst.
    exists (a `/\ b :: B |- A).
    rewrite in_cons eq_refl orTb. split. by [].
    rewrite//= /eval_product !big_cons//= mulrA in IH2.
    rewrite//= /eval_product  !big_cons//= /prodR !big_cons big_nil mulr1.
    by exact IH2.
  + exists q1. 
    by rewrite !in_cons IH1 IH2 !orbT//=. 
- destruct IHseq_calc_product as [q1 [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + subst.
    exists (A |- a `/\ b :: B).
    rewrite in_cons eq_refl orTb. split. by [].
    rewrite//= /eval_product !big_cons//= mulrA in IH2.
    rewrite//= /eval_product  !big_cons//= /prodR !big_cons big_nil mulr1.
    by exact IH2.
  + exists q1. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_product as [q1 [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + subst.
    exists ((`~ a) :: B |- A).
    rewrite in_cons eq_refl orTb; split; first by [].
    rewrite //= /eval_product !big_cons big_nil mulr1 //= in IH2. 
    rewrite//= /eval_product  !big_cons//=. 
    case: ifP; intros; rewrite//=.
    * rewrite mul0r. 
      have hA := eval_product_01 A. rewrite /eval_product in hA.
      have hA' : 0 <= \prod_(i <- A) [[i]]_product <= 1 ->
                 0 <= \prod_(i <- A) [[i]]_product. intros; lra.
      by apply hA' in hA; exact hA.
    * rewrite mul1r.
      have ha := @translate_Bool_T_01 R p product (a).
      have hb : forall (x : R),  (0 < x) = false -> 
                 0 <= x <= 1 ->
                 0 = x. intros; lra.
      apply (hb _  n) in ha.
      rewrite -ha in IH2.
      have hA := eval_product_01 A. rewrite /eval_product in hA.
      have helper : \prod_(i <- B) [[i]]_product <= 0 ->
                    0 <= \prod_(i <- A) [[i]]_product <= 1 ->
                    \prod_(i <- B) [[i]]_product <= \prod_(i <- A) [[i]]_product.
      intros; lra.
      by apply (helper IH2) in hA; exact hA.
  + exists q1. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_product1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_product2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    exists (A |- a `=> b :: B).
    rewrite in_cons eq_refl orTb; split; first by [].
    rewrite //= /eval_product  //= in IH12.
    rewrite //= !eval_product_add_el in IH22. 
    rewrite//= !eval_product_add_el//=.
    case: ifP; intros.
    * have ha := @translate_Bool_T_01 R p product (a).
      have hb := @translate_Bool_T_01 R p product (b).
      have hA := eval_product_01 A.
      have hB := eval_product_01 B.
      have ha' :  [[a]]_product != 0 \/ 0 = [[a]]_product. lra.
      destruct ha' as [ha' | ha']; rewrite//=.
      - have helper:  [[a]]_product * eval_product A <=
                        [[b]]_product * ([[a]]_product / [[a]]_product) * eval_product B ->
                      eval_product A <= [[b]]_product / [[a]]_product * eval_product B.
        {intros; nra.}
        have h := divff ha' . rewrite h mulr1 in helper.
        rewrite helper//=. 
      - lra.
    * rewrite mul1r//=.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
- destruct IHseq_calc_product1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_product2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    exists (a `=> b :: A |- B).
    rewrite in_cons eq_refl orTb; split; first by [].
    rewrite //= !eval_product_add_el  //= in IH12.
    rewrite //= !eval_product_add_el in IH22. 
    rewrite//= !eval_product_add_el//=.
    have ha := @translate_Bool_T_01 R p product (a).
    have hb := @translate_Bool_T_01 R p product (b).
    have hB := eval_product_01 B.
    have hA := eval_product_01 A.
    move: IH12; case: ifP; case: ifP; intros; try rewrite mul0r in IH12.
    * have ha' :  [[a]]_product != 0 \/ 0 = [[a]]_product. lra.
      destruct ha' as [ha' | ha']; rewrite//=.
      - have helper:  [[b]]_product * ([[a]]_product / [[a]]_product) * eval_product A <=
                         [[a]]_product * eval_product B ->
                      [[b]]_product / [[a]]_product * eval_product A <=  eval_product B.
        {intros; nra.}
        have h := divff ha' . rewrite h mulr1 in helper.
        rewrite helper//=. 
      - lra.
    * rewrite mul1r//=.
      have lelt : ([[b]]_product < [[a]]_product) = false <->
                    [[b]]_product >= [[a]]_product.
      split; intros; lra.
      apply lelt in n.
      have helper : [[b]]_product * eval_product A <= [[a]]_product * eval_product B ->
                    [[a]]_product * eval_product A <= [[a]]_product * eval_product B.
      intros; nra.
      apply helper in IH22. nra.
    * rewrite mul1r//= in IH12.
      nra.
    * rewrite mul1r//= in IH12. rewrite mul1r//=.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=.     
Qed.


Lemma sound_product' (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
seq_calc_product' Q -> 
exists (q : ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
  q \in Q /\ (eval_product (fst q) <= eval_product (snd q)).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite //= mem_head. split. by [].  
  simpl. by lra.
- exists ([::] |- [::]). 
  rewrite mem_head.  split. by []. 
  rewrite /eval_product//=.
- destruct IHseq_calc_product' as [M [IH1 IH2]]. 
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
- destruct IHseq_calc_product' as [q [IH1 IH2]].
  exists q. rewrite mem_cat IH1 orTb.
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_product' as [M [IH1 IH2]].   
  exists M. rewrite !mem_cat in IH1. 
  rewrite mem_cat. move/orP : IH1. 
  move => [h |/orP h].  rewrite h ?orbT; split; rewrite//=. 
  move: h. move => [h | h]; rewrite h ?orbT; split; rewrite//=.
- destruct IHseq_calc_product' as [q1 [IH1 IH2]]. 
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h1 | h2].
  + subst.
    rewrite //= !eval_product_add in IH2.
    have ha := (eval_product_01 A).
    have hb := (eval_product_01 B).
    have hc := (eval_product_01 C).
    have hd := (eval_product_01 D).
    have [h | h] := le_or (eval_product A) (eval_product C).
    * exists (A |- C). rewrite //= mem_head. split. by [].
      by rewrite h.
    * have helper : eval_product A * eval_product B <= eval_product A * eval_product D. nra.
      have helper1 : forall (a b d : R), a * b <= a * d ->
                                           0 < a ->
                                           b <= d. {intros; nra.}
      have ha' :  0 < eval_product A \/ 0 = eval_product A. lra.
      destruct ha' as [ha' | ha'].
      + exists (B |- D). rewrite //= !in_cons eq_refl orTb orbT. 
        split. by [].
        apply (helper1 _ _ _ helper) in ha'. rewrite//=.
      + exists (A |- C). rewrite //= mem_head. split. by [].
        lra.
  + exists q1. 
    by rewrite !in_cons h2 !orbT IH2//=.   
- destruct IHseq_calc_product'1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_product'2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11; move/orP: IH21;
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + exists (A ++ B |- C ++ D).
    subst.
    rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= !eval_product_add.
    rewrite //= in IH12. rewrite //= in IH22.
    have helper : forall (x : R), 0 <= x <= 1 -> 0 <= x /\ x <= 1. {intros; lra.}
    have mulr_le1 : forall (x y: R), 0 <= x -> 0 <= y -> y <= 1 ->
                                     x * y <= x. {intros; nra.}
    have le_mul : forall ( a b c :R ),  0 <= a -> 0 <= b -> a <= c ->
                                        b <=1 -> a * b <= c * b. {intros. nra.}
    
    have [ha0 ha1] := helper _ (eval_product_01 A).
    have [hb0 hb1] := helper _ (eval_product_01 B).
    have [hc0 hc1] := helper _ (eval_product_01 C).
    have [hd0 hd1] := helper _ (eval_product_01 D).
    apply (le_mul _ _ (eval_product C) ha0 hb0) in IH12; first last. by exact hb1.
    have le_le : forall (a b c d : R),  0 <= a -> 0 <= b -> 0 <= c -> 0 <= d ->
                                        a* b <= c * b -> b <= d -> a * b <= c * d. {
      intros. nra.}
    apply (le_le (eval_product A) (eval_product B) (eval_product C) 
             (eval_product D) ha0 hb0 hc0 hd0) in IH22; first last. by exact IH12.
    by exact IH22.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
- destruct IHseq_calc_product' as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h | h].
  + subst. exists ((X ++ B ++ A ++ Y |- C)).
    rewrite mem_head. split. by [].
    rewrite//= !eval_product_add in IH2.
    rewrite//= !eval_product_add. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- destruct IHseq_calc_product' as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP h | h].
  + subst. exists (C |- X ++ B ++ A ++ Y).
    rewrite mem_head. split. by [].
    rewrite//= !eval_product_add in IH2.
    rewrite//= !eval_product_add. lra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=.
- destruct IHseq_calc_product' as [q [IH1 IH2]].
  rewrite in_cons in IH1. 
  move/orP : IH1. 
  move => [/eqP h | h].
  + exists (A ++ C |- B).
    subst. rewrite //= in IH2.
    rewrite in_cons eq_refl orTb; split; first by [].
    rewrite //= eval_product_add . 
    have hac := eval_product_mul_le A C.
    nra.
  + exists q. 
    by rewrite in_cons h IH2 orbT//=. 
- exists (ldl_bool def false :: A |- B).
  rewrite in_cons eq_refl orTb. split. by [].
  rewrite//= /eval_product big_cons//= mul0r.
  have h := eval_product_01 B. rewrite /eval_product in h.
  have helper : forall (x : R), 0 <= x <= 1 -> 0 <= x /\ x <= 1. {intros. lra.}
  apply helper in h. destruct h as [h _].
  by rewrite h.
- exists (A |- [:: ldl_bool def true]).
  rewrite in_cons eq_refl orTb. split. by [].
  rewrite//= /eval_product big_cons//= mul1r big_nil.
  have h := eval_product_01 A. rewrite /eval_product in h.
  have helper : forall (x : R), 0 <= x <= 1 -> 0 <= x /\ x <= 1. {intros. lra.}
  apply helper in h. destruct h as [ _ h].
  by rewrite h.
- destruct IHseq_calc_product' as [q1 [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + subst.
    exists (a `/\ b :: B |- A).
    rewrite in_cons eq_refl orTb. split. by [].
    rewrite//= /eval_product !big_cons//= mulrA in IH2.
    rewrite//= /eval_product  !big_cons//= /prodR !big_cons big_nil mulr1.
    by exact IH2.
  + exists q1. 
    by rewrite !in_cons IH1 IH2 !orbT//=. 
- destruct IHseq_calc_product' as [q1 [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + subst.
    exists (A |- a `/\ b :: B).
    rewrite in_cons eq_refl orTb. split. by [].
    rewrite//= /eval_product !big_cons//= mulrA in IH2.
    rewrite//= /eval_product  !big_cons//= /prodR !big_cons big_nil mulr1.
    by exact IH2.
  + exists q1. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
(*- admit. 
- destruct IHseq_calc_product' as [q1 [IH1 IH2]].
  rewrite in_cons in IH1; move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + subst.
    exists (A |- a `\/ b :: B).
    rewrite in_cons eq_refl orTb; split; first by [].
    rewrite//= /eval_product//= !big_cons//= in IH2.
    rewrite//= /eval_product !big_cons//= /prodR/product_dl_prod !big_cons big_nil.
    rewrite /product_dl_mul !addr0 mulr0 subr0.
    have helper1 : forall (x y : R), 0 <= x <= 1 -> 0 <= y <= 1 ->
                                     x + y - x*y >= x.
    {intros; nra.}
    have helper2 : forall (X Y x z : R), 0 <= X <= 1 ->
                                         0 <= Y <= 1 ->
                                         X <= x * Y ->
                                         z >= x ->
                                         X <= z * Y.
    {intros; nra.}
    have hA := (eval_product_01 A).
    have hB := (eval_product_01 B).
    have ha := @translate_Bool_T_01 R p product (a).
    have hb := @translate_Bool_T_01 R p product (b).
    have h:= helper1 ([[a]]_product) ([[b]]_product) ha hb.
    have hh := helper2 _ _ _ _ hA hB IH2 h.
    rewrite /eval_product in hh.
    by exact hh.
  + rewrite in_cons in IH1. move/orP : IH1.
    move => [/eqP IH1 | IH1].
    subst.
    exists (A |- a `\/ b :: B).
    rewrite in_cons eq_refl orTb; split; first by [].
    rewrite//= /eval_product//= !big_cons//= in IH2.
    rewrite//= /eval_product !big_cons//= /prodR/product_dl_prod !big_cons big_nil.
    rewrite /product_dl_mul !addr0 mulr0 subr0.
    have helper1 : forall (x y : R), 0 <= x <= 1 -> 0 <= y <= 1 ->
                                     x + y - x*y >= y.
    {intros; nra.}
    have helper2 : forall (X Y x z : R), 0 <= X <= 1 ->
                                         0 <= Y <= 1 ->
                                         X <= x * Y ->
                                         z >= x ->
                                         X <= z * Y.
    {intros; nra.}
    have hA := (eval_product_01 A).
    have hB := (eval_product_01 B).
    have ha := @translate_Bool_T_01 R p product (a).
    have hb := @translate_Bool_T_01 R p product (b).
    have h:= helper1 ([[a]]_product) ([[b]]_product) ha hb.
    have hh := helper2 _ _ _ _ hA hB IH2 h.
    rewrite /eval_product in hh.
    by exact hh.
  + exists q1. 
    by rewrite !in_cons IH1 IH2 !orbT//=. *)
- destruct IHseq_calc_product'1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_product'2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11; move/orP: IH21;
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst.
    exists (A |- (`~ a) :: B).
    rewrite in_cons eq_refl orTb; split; first by [].
    rewrite //= !eval_product_add_el//= mul0r in IH22. 
    rewrite //= in IH12. 
    rewrite//= eval_product_add_el//=. 
    case: ifP; intros.
    * rewrite mul0r. nra.
    * rewrite mul1r//=.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
- destruct IHseq_calc_product' as [q1 [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + subst.
    exists ((`~ a) :: B |- A).
    rewrite in_cons eq_refl orTb; split; first by [].
    rewrite //= /eval_product !big_cons big_nil mulr1 //= in IH2. 
    rewrite//= /eval_product  !big_cons//=. 
    case: ifP; intros; rewrite//=.
    * rewrite mul0r. 
      have hA := eval_product_01 A. rewrite /eval_product in hA.
      have hA' : 0 <= \prod_(i <- A) [[i]]_product <= 1 ->
                 0 <= \prod_(i <- A) [[i]]_product. intros; lra.
      by apply hA' in hA; exact hA.
    * rewrite mul1r.
      have ha := @translate_Bool_T_01 R p product (a).
      have hb : forall (x : R),  (0 < x) = false -> 
                 0 <= x <= 1 ->
                 0 = x. intros; lra.
      apply (hb _  n) in ha.
      rewrite -ha in IH2.
      have hA := eval_product_01 A. rewrite /eval_product in hA.
      have helper : \prod_(i <- B) [[i]]_product <= 0 ->
                    0 <= \prod_(i <- A) [[i]]_product <= 1 ->
                    \prod_(i <- B) [[i]]_product <= \prod_(i <- A) [[i]]_product.
      intros; lra.
      by apply (helper IH2) in hA; exact hA.
  + exists q1. 
    by rewrite !in_cons IH1 IH2 !orbT//=. 
Qed.

Lemma product_true_false_admissable :
  [[@ldl_bool R def true]]_product = [[`~ ldl_bool def false]]_product.
Proof.
rewrite//=; case: ifP; intros; lra.
Qed.

Lemma product_neg_impl_admissable (e : @expr R Bool_T_def):
 [[`~ e]]_product = [[e `=> ldl_bool def false]]_product.
Proof.
rewrite//=. repeat case: ifP; intros; by rewrite ?mul0r//=.
Qed.

(*this is not true. I cannot construct the or in any way from
the connectives I have*)
(*because of this, the equivalence cannot be proven*)
(*Lemma product_or_impl_admissable (a b  : @expr R Bool_T_def):
  [[a `\/ b]]_product = [[(`~a) `=> b]]_product.
Proof.
rewrite//=; repeat case: ifP; intros.
- have hb := @translate_Bool_T_01 R p product (b).
  lra.
- rewrite divr1 /product_dl_prod !big_cons big_nil.
  rewrite /product_dl_mul !addr0 !mulr0 !subr0//=.
Admitted.*)


Lemma equivalence_product (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
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
- rewrite true_false neg_impl. apply implR_p. 
  + have h : [::] ++ A = A. {rewrite//=.}
    rewrite -h. 
    apply w_p. apply empty_p.
  + have h : ldl_bool def false :: A = [::ldl_bool def false] ++ A.
    {rewrite//=.}
    rewrite h . apply w_p. apply id_p.
- apply andL_p. by exact IHseq_calc_product'.
- apply andR_p. by exact IHseq_calc_product'.
(*- admit.
- admit.*)
- rewrite neg_impl. apply implR_p; rewrite//=. 
- apply negL_p. by exact IHseq_calc_product'.
Qed.

 End hypersequent_product.


Section hypersequent_godel.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope mset_scope. 
Context {R : realType}.
Context {K : choiceType}.
Implicit Types  (A : {mset K}) (s : seq K).
Variable p : R. 
Local Notation "[[ e ]]_ l" := (@translation R l p _ e).

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).
(*entailment as pair (A, B) where A |- B*)

(*hypersequent calculus as per literature*)
Inductive seq_calc_godel :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))
      -> Prop :=
| id_g : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                (A : seq (@expr R Bool_T_def)),
    seq_calc_godel ( (A |- A) :: Q)
(*structural*)
| eex_g : forall (Q P S1 S2: seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_godel (S1 ++ P ++ Q ++ S2) ->
    seq_calc_godel (S1 ++ Q ++ P ++ S2)
| ew_g : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_godel Q ->
    seq_calc_godel (Q ++ P) (*correct order*)
| ec_g : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_godel (Q ++ P ++ P) ->
    seq_calc_godel (Q ++ P)
| comm_hyper_g : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A1 A2 B1 B2 C D: seq (@expr R Bool_T_def)),
    seq_calc_godel (((A1 ++ B1) |- C) :: Q) ->
    seq_calc_godel (((A2 ++ B2) |- D) :: Q) ->               
    seq_calc_godel ( ((A1 ++ A2) |- C) :: ((B1 ++ B2) |- D) :: Q)
| comm_g : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_godel (((A ++ B ++ B) |- C) :: Q) ->
    seq_calc_godel (((A ++ B) |- C) :: Q)
| weak_g : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_godel ((A |- C) :: Q ) ->
    seq_calc_godel (((A ++ B) |- C) :: Q )
| exL_g : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_godel (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_godel (((X ++ B ++ A ++ Y) |- C) :: Q) 
| exR_g : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_godel ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_godel ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
| bot_g : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                 (A B : seq (@expr R Bool_T_def)),
    seq_calc_godel (((ldl_bool def false :: A) |- B) :: Q)
| top_g : forall Q 
                 (A : seq (@expr R Bool_T_def)),
    seq_calc_godel ((A |- [::ldl_bool def true]) :: Q )
| andL_g : forall Q 
                   (A B : seq (@expr R Bool_T_def))
                   (a b : @expr R Bool_T_def),
    seq_calc_godel (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_godel ((((a `/\ b) :: B) |- A) :: Q) 
| andR_g : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A  : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_godel ( (A |- [:: a]) :: Q ) ->
    seq_calc_godel ( (A |- [:: b]) :: Q) ->
    seq_calc_godel ((A |- [:: (a `/\ b)]) :: Q )
| orL_g : forall  Q
                  (A B : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_godel ( ((b :: B) |- A) :: Q) ->
    seq_calc_godel ( ((a :: B) |- A) :: Q) ->
    seq_calc_godel (((a `\/ b) :: B |- A) :: Q)
| orR_g : forall Q
                  (A  : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (( A |- [::a] ) :: ( A |- [::b]) :: Q ) ->
    seq_calc_godel (( A |- [::(a `\/ b)] ) :: Q) 
| implR_g : forall Q
                  (A B : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_godel ((a :: A |- [::b]) :: Q) ->
    seq_calc_godel ((A |- [:: (a `=> b)]) :: Q)
| implL_g : forall Q
                  (A1 A2 B  : seq (@expr R Bool_T_def))
                  (a b: @expr R Bool_T_def),
    seq_calc_godel ((A1 |- [:: a]) :: Q) ->
    seq_calc_godel ((b :: A2 |- B) :: Q) ->
    seq_calc_godel (( (a `=> b) :: A1 ++ A2 |- B) :: Q)
.


Inductive seq_calc_godel' :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))
      -> Prop :=
| id_g' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                (A : seq (@expr R Bool_T_def)),
    seq_calc_godel' ( (A |- A) :: Q)
(*structural*)
| eex_g' : forall (Q P S1 S2: seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_godel' (S1 ++ P ++ Q ++ S2) ->
    seq_calc_godel' (S1 ++ Q ++ P ++ S2)
| ew_g' : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_godel' Q ->
    seq_calc_godel' (Q ++ P) (*correct order*)
| ec_g' : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_godel' (Q ++ P ++ P) ->
    seq_calc_godel' (Q ++ P)
| comm_hyper_g' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A1 A2 B1 B2 C D: seq (@expr R Bool_T_def)),
    seq_calc_godel' (((A1 ++ B1) |- C) :: Q) ->
    seq_calc_godel' (((A2 ++ B2) |- D) :: Q) ->               
    seq_calc_godel' ( ((A1 ++ A2) |- C) :: ((B1 ++ B2) |- D) :: Q)
| comm_g' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_godel' (((A ++ B ++ B) |- C) :: Q) ->
    seq_calc_godel' (((A ++ B) |- C) :: Q)
| weak_g' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C : seq (@expr R Bool_T_def)),
    seq_calc_godel' ((A |- C) :: Q ) ->
    seq_calc_godel' (((A ++ B) |- C) :: Q )
| exL_g' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_godel' (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_godel' (((X ++ B ++ A ++ Y) |- C) :: Q) 
| exR_g' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C X Y : seq (@expr R Bool_T_def)),
    seq_calc_godel' ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_godel' ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
| bot_g' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                 (A B : seq (@expr R Bool_T_def)),
    seq_calc_godel' (((ldl_bool def false :: A) |- B) :: Q)
| top_g' : forall Q 
                 (A : seq (@expr R Bool_T_def)),
    seq_calc_godel' ((A |- [::ldl_bool def true]) :: Q )
| andL_g' : forall Q 
                   (A B : seq (@expr R Bool_T_def))
                   (a b : @expr R Bool_T_def),
    seq_calc_godel' (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_godel' ((((a `/\ b) :: B) |- A) :: Q) 
| andR_g' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A  : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_godel' ( (A |- [:: a]) :: Q ) ->
    seq_calc_godel' ( (A |- [:: b]) :: Q) ->
    seq_calc_godel' ((A |- [:: (a `/\ b)]) :: Q )
| orL_g' : forall  Q
                  (A B : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_godel' ( ((b :: B) |- A) :: Q) ->
    seq_calc_godel' ( ((a :: B) |- A) :: Q) ->
    seq_calc_godel' (((a `\/ b) :: B |- A) :: Q)
| orR_g' : forall Q
                  (A  : seq (@expr R Bool_T_def))
                  (a b : @expr R Bool_T_def),
    seq_calc_godel' (( A |- [::a] ) :: ( A |- [::b]) :: Q ) ->
    seq_calc_godel' (( A |- [::(a `\/ b)] ) :: Q) 
| negR_g : forall Q
                  (A  : seq (@expr R Bool_T_def))
                  (a : @expr R Bool_T_def),
    seq_calc_godel' ((a :: A |- [:: ldl_bool def false]) :: Q) ->
    seq_calc_godel' ((A |- [:: (`~ a)]) :: Q)
| negL_g : forall Q
                  (A1 A2 B  : seq (@expr R Bool_T_def))
                  (a : @expr R Bool_T_def),
    seq_calc_godel' ((A1 |- [:: a]) :: Q) ->
    seq_calc_godel' (((ldl_bool def false) :: A2 |- B) :: Q) ->
    seq_calc_godel' (( (`~ a) :: A1 ++ A2 |- B) :: Q)
.

Lemma big_maxr_godel_le1 (A : seq (@expr R Bool_T_def)) : 
   \big[maxr/0]_(j <- (A)) [[j]]_Godel <= 1.
Proof.
have h := @translate_Bool_T_01 R p Godel (ldl_or A).
rewrite //= /maxR big_map in h.
have reshape : 0 <= \big[maxr/0]_(j <- A) [[j]]_Godel <= 1 ->
               \big[maxr/0]_(j <- A) [[j]]_Godel <= 1. intros. lra.
apply reshape in h.
by exact h.
Qed.

Lemma big_minr_godel_le1 (A : seq (@expr R Bool_T_def)) : 
   \big[minr/1]_(j <- (A)) [[j]]_Godel <= 1.
Proof.
have h := @translate_Bool_T_01 R p Godel (ldl_and A).
rewrite //= /minR big_map in h.
have reshape : 0 <= \big[minr/1]_(j <- A) [[j]]_Godel <= 1 ->
               \big[minr/1]_(j <- A) [[j]]_Godel <= 1. intros. lra.
apply reshape in h.
by exact h.
Qed.


Lemma big_maxr_godel_ge0 (A : seq (@expr R Bool_T_def)) : 
   0 <= \big[maxr/0]_(j <- (A)) [[j]]_Godel .
Proof.
have h := @translate_Bool_T_01 R p Godel (ldl_or A).
rewrite //= /maxR big_map in h.
have reshape : 0 <= \big[maxr/0]_(j <- A) [[j]]_Godel <= 1 ->
               0 <= \big[maxr/0]_(j <- A) [[j]]_Godel. intros. lra.
apply reshape in h.
by exact h.
Qed.

Lemma big_minr_godel_ge0 (A : seq (@expr R Bool_T_def)) : 
   0 <= \big[minr/1]_(j <- (A)) [[j]]_Godel .
Proof.
have h := @translate_Bool_T_01 R p Godel (ldl_and A).
rewrite //= /minR big_map in h.
have reshape : 0 <= \big[minr/1]_(j <- A) [[j]]_Godel <= 1 ->
               0 <= \big[minr/1]_(j <- A) [[j]]_Godel. intros. lra.
apply reshape in h.
by exact h.
Qed.

Lemma minrA : forall (x y z : R), minr x (minr y z) = minr (minr x y) z.
Proof.
intros. rewrite /minr.
repeat case: ifP; intros; lra.
Qed.

Lemma minrC : forall (x y : R), minr x y = minr y x.
Proof.
intros. rewrite /minr.
repeat case: ifP; intros; lra.
Qed.

Lemma big_min_cat_godel (A B: seq (@expr R Bool_T_def)):
\big[minr/1]_(j <- (A ++ B)) [[j]]_Godel = 
  minr (\big[minr/1]_(j <- (A)) [[j]]_Godel) (\big[minr/1]_(j <- (B)) [[j]]_Godel).
Proof.
elim: A => [|x xs IH].
  - rewrite /= big_nil//=. 
    have H := big_minr_godel_le1 B.
    rewrite {2}/minr. case: ifP; intros; try lra.
    have triv: \big[minr/1]_(j <- B) [[j]]_Godel <= 1 ->
               1 < \big[minr/1]_(j <- B) [[j]]_Godel ->
               \big[minr/1]_(j <- B) [[j]]_Godel = 1. intros. lra. 
    by apply (triv H i). 
  - simpl. rewrite  !big_cons -minrA. f_equal.
    by exact IH.
Qed.

Lemma maxrA : forall (x y z : R), maxr x (maxr y z) = maxr (maxr x y) z.
Proof.
intros. rewrite /maxr.
repeat case: ifP; intros; lra.
Qed.

Lemma big_max_cat_godel (A B: seq (@expr R Bool_T_def)):
\big[maxr/0]_(j <- (A ++ B)) [[j]]_Godel = 
  maxr (\big[maxr/0]_(j <- (A)) [[j]]_Godel) (\big[maxr/0]_(j <- (B)) [[j]]_Godel).
Proof.
elim: A => [|x xs IH].
  - rewrite /= big_nil//=. 
    have H := big_maxr_godel_ge0 B.
    rewrite {2}/maxr. case: ifP; intros; try lra.
    have triv: 0 <= \big[maxr/0]_(j <- B) [[j]]_Godel  ->
               (0 < \big[maxr/0]_(j <- B) [[j]]_Godel) = false ->
               \big[maxr/0]_(j <- B) [[j]]_Godel = 0. intros. lra. 
    by apply (triv H n). 
  - simpl. rewrite  !big_cons -maxrA. f_equal.
    by exact IH.
Qed.


Lemma big_minr_if (A B : seq (@expr R Bool_T_def)) : 
  if \big[minr/1]_(j <- (A)) [[j]]_Godel <= \big[minr/1]_(j <- (B)) [[j]]_Godel then
                \big[minr/1]_(j <- (A ++ B)) [[j]]_Godel = \big[minr/1]_(j <- (A)) [[j]]_Godel else
                \big[minr/1]_(j <- (A ++ B)) [[j]]_Godel = \big[minr/1]_(j <- (B)) [[j]]_Godel.
Proof.
have H := big_min_cat_godel A B. 
rewrite {2}/minr in H. rewrite//=.
move: H. case: ifP;
case: ifPn; intros; rewrite//=; try lra.
- have hab : ~~ (\big[minr/1]_(j <- A) [[j]]_Godel <= \big[minr/1]_(j <- B) [[j]]_Godel) ->
             \big[minr/1]_(j <- A) [[j]]_Godel < \big[minr/1]_(j <- B) [[j]]_Godel ->
             False. intros. lra.
  apply (hab n) in i. contradiction.
- have hab : \big[minr/1]_(j <- A) [[j]]_Godel <= \big[minr/1]_(j <- B) [[j]]_Godel ->
             (\big[minr/1]_(j <- A) [[j]]_Godel < \big[minr/1]_(j <- B) [[j]]_Godel) = false ->
             (\big[minr/1]_(j <- A) [[j]]_Godel = \big[minr/1]_(j <- B) [[j]]_Godel).
  intros. lra.
  apply (hab i) in n.
  rewrite n//=. 
Qed.

Lemma minr_lt_godel (A B C: seq (@expr R Bool_T_def)) :
  \big[minr/1]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- (A)) [[j]]_Godel /\ 
    \big[minr/1]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- ( B)) [[j]]_Godel <->
 (\big[minr/1]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- (A ++ B)) [[j]]_Godel).
Proof.
split.
- move => [h1 h2].
  have h := big_minr_if A B. move: h.
  case: ifP; intros; rewrite h//=.
- move => h. 
  have H := big_minr_if A B. move: H.
  case: ifP; intros;
  rewrite H in h; rewrite h;
  split; first by []; lra.
Qed.

Lemma minr_le_godel (A B C: seq (@expr R Bool_T_def)) :
 (\big[minr/1]_(j <- (A ++ B)) [[j]]_Godel <= \big[minr/1]_(j <- C) [[j]]_Godel) ->
  (\big[minr/1]_(j <- A) [[j]]_Godel <= \big[minr/1]_(j <- (B)) [[j]]_Godel /\
    \big[minr/1]_(j <- A) [[j]]_Godel <= \big[minr/1]_(j <- (C)) [[j]]_Godel )\/ 
    (\big[minr/1]_(j <- B) [[j]]_Godel <= \big[minr/1]_(j <- ( C)) [[j]]_Godel /\
\big[minr/1]_(j <- B) [[j]]_Godel <= \big[minr/1]_(j <- (A)) [[j]]_Godel).
Proof.
intros. have h := big_minr_if A B. move: h.
case: ifP; intros. 
- rewrite h in H. left. by rewrite H//=.
- right. rewrite h in H. rewrite H. split; first by []. lra.
Qed.

Lemma minr_maxr_lt_godel (A B C: seq (@expr R Bool_T_def)) :
  \big[maxr/0]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- (A)) [[j]]_Godel /\ 
    \big[maxr/0]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- ( B)) [[j]]_Godel <->
 (\big[maxr/0]_(j <- C) [[j]]_Godel < \big[minr/1]_(j <- (A ++ B)) [[j]]_Godel).
Proof.
split.
- move => [h1 h2].
  have h := big_minr_if A B. move: h.
  case: ifP; intros; rewrite h//=.
- move => h. 
  have H := big_minr_if A B. move: H.
  case: ifP; intros;
  rewrite H in h; rewrite h;
  split; first by []; lra.
Qed.

Lemma minr_maxr_le_godel (A B C: seq (@expr R Bool_T_def)) :
 (\big[minr/1]_(j <- (A ++ B)) [[j]]_Godel <= \big[maxr/0]_(j <- C) [[j]]_Godel) ->
  (\big[minr/1]_(j <- A) [[j]]_Godel <= \big[minr/1]_(j <- (B)) [[j]]_Godel /\
    \big[minr/1]_(j <- A) [[j]]_Godel <= \big[maxr/0]_(j <- (C)) [[j]]_Godel )\/ 
    (\big[minr/1]_(j <- B) [[j]]_Godel <= \big[maxr/0]_(j <- ( C)) [[j]]_Godel /\
\big[minr/1]_(j <- B) [[j]]_Godel <= \big[minr/1]_(j <- (A)) [[j]]_Godel).
Proof.
intros. have h := big_minr_if A B. move: h.
case: ifP; intros. 
- rewrite h in H. left. by rewrite H//=.
- right. rewrite h in H. rewrite H. split; first by []. lra.
Qed.

Lemma sound_godel (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
seq_calc_godel Q -> 
exists (q : ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))), q \in Q 
/\ 
(minR (map (translation Godel p) (fst q))  <=  maxR (map (translation Godel p) (snd q))).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite //= mem_head. split. by []. 
  rewrite /minR/maxR !big_map. 
   admit. (*need helper lemma*)
   (*simple*)
- destruct IHseq_calc_godel as [M [IH1 IH2]]. 
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
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  exists q. rewrite mem_cat IH1 orTb.
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_godel as [M [IH1 IH2]].   
  exists M. rewrite !mem_cat in IH1. 
  rewrite mem_cat. move/orP : IH1. 
  move => [h |/orP h].  rewrite h ?orbT; split; rewrite//=. 
  move: h. move => [h | h]; rewrite h ?orbT; split; rewrite//=.
- destruct IHseq_calc_godel1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_godel2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    rewrite //=/minR/maxR !big_map in IH12.
    rewrite //=/minR/maxR !big_map in IH22.
    rewrite //=/maxR/minR. 
    have helper : forall (a b : R), a < b <-> ~(b <= a). {intros. lra.}
          have contr_comp : forall (a b : R), a < b -> b <= a -> false. {
          intros. lra.}
    have hq : exists q : seq (expr Bool_T_def) * seq (expr Bool_T_def),
        q = (A1 ++ A2 |- C) \/ q = B1 ++ B2 |- D. {
      exists (A1 ++ A2 |- C). auto.}
    have h:  ~(exists q : seq (expr Bool_T_def) * seq (expr Bool_T_def),
    (q \in [:: A1 ++ A2 |- C, B1 ++ B2 |- D & Q] /\ \big[minr/1]_(i <- [seq [[i]]_Godel | i <- q.1]) i <= 
               \big[maxr/0]_(i <- [seq [[i]]_Godel | i <- q.2]) i)) -> false. {
        apply minr_maxr_le_godel in IH12; destruct IH12 as [h1 | h1];
        apply minr_maxr_le_godel in IH22; destruct IH22 as [h2 | h2];
        destruct h1 as [h1 h1']; destruct h2 as [h2 h2'];intro;
        rewrite -forallNP in H1;
        have H11 :=  H1 (A1 ++ A2 |- C); rewrite not_andE in H11;
        have H22 := H1 (B1 ++ B2 |- D); rewrite not_andE in H22;
        rewrite mem_head //= !big_map in H11; destruct H11 as [H11 | H11];
        rewrite  !in_cons eq_refl orbT //= !big_map in H22; destruct H22 as [H22 | H22]; auto;
        rewrite -helper in H11; rewrite -helper in H22;
        rewrite -minr_maxr_lt_godel in H11; rewrite -minr_maxr_lt_godel in H22;
        destruct H11 as [H11 H11']; destruct H22 as [H22 H22']; lra.}
     apply contrapT. auto.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (A ++ B |- C).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR !big_map.
    rewrite //= /minR !big_map in IH2.
    have min_weak : 
      \big[minr/1]_(j <- (A ++ B ++ B)) [[j]]_Godel = \big[minr/1]_(j <- (A ++ B)) [[j]]_Godel. { 
      rewrite !big_min_cat_godel {1}/minr {2}/minr {7}/minr {11}/minr. repeat case: ifP; 
      intros; rewrite//=; lra. }
    rewrite min_weak in IH2. by exact IH2.
  + exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (A ++ B |- C).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR !big_map.
    rewrite //= /minR !big_map in IH2.
    have h := (big_minr_if A B). move: h.
    case: ifP; intros.
    * rewrite -h in IH2. by exact IH2.
    * rewrite h. 
      have le_false : forall (a b : R), a<= b = false -> b <= a. {intros. lra.}
      apply le_false in n. 
      have lerT : forall (a b c : R), a <= c -> b <= a -> b <= c. {intros. lra.}
      by rewrite (lerT _ _ _ IH2 n).
  + exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (X ++ B ++ A ++ Y |- C). 
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_map.
    rewrite //= /minR/maxR !big_map in IH2.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {3}/minr {8}/minr {13}/minr {14}/minr {19}/minr.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {3}/minr {8}/minr {13}/minr {14}/minr {19}/minr in IH2.
    move: IH2.
    repeat case: ifP; intros; rewrite//=; try lra.
    have h : (\big[minr/1]_(j <- B) [[j]]_Godel < \big[minr/1]_(j <- A) [[j]]_Godel) = false ->
             (\big[minr/1]_(j <- A) [[j]]_Godel < \big[minr/1]_(j <- B) [[j]]_Godel) = false ->
             (\big[minr/1]_(j <- A) [[j]]_Godel = \big[minr/1]_(j <- B) [[j]]_Godel). intros. lra.
    apply (h n) in n1.
    rewrite n1. by exact IH2.
(*to do: this is  be brute-forcing cases
            -  come up with a smarter way if possible*)
  + exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (C |- X ++ B ++ A ++ Y).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_map.
    rewrite //= /minR/maxR !big_map in IH2.
    rewrite !big_max_cat_godel {1}/maxr {2}/maxr {3}/maxr {7}/maxr {12}/maxr {13}/maxr {18}/maxr.
    rewrite !big_max_cat_godel {1}/maxr {2}/maxr {3}/maxr {7}/maxr {12}/maxr {13}/maxr {18}/maxr in IH2.
    move: IH2.
    repeat case: ifP; intros; rewrite//=; try lra.
    have h : (\big[maxr/0]_(j <- B) [[j]]_Godel < \big[maxr/0]_(j <- A) [[j]]_Godel) = false ->
             (\big[maxr/0]_(j <- A) [[j]]_Godel < \big[maxr/0]_(j <- B) [[j]]_Godel) = false ->
             (\big[maxr/0]_(j <- A) [[j]]_Godel = \big[maxr/0]_(j <- B) [[j]]_Godel). intros. lra.
    apply (h n0) in n2.
    rewrite -n2. by exact IH2.
  + exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- exists (ldl_bool def false :: A |- B). 
  rewrite in_cons eq_refl orTb. split; first by [].
  rewrite /minR/maxR//= !big_cons !big_map.
  have h : forall (a : R), 0 <= a -> minr 0 (a) = 0. {
    intros. rewrite /minr; case: ifP; rewrite//=; intros; lra.}
  rewrite h.
  * by rewrite big_maxr_godel_ge0.
  * by rewrite big_minr_godel_ge0.
-  exists (A |- [:: ldl_bool def true]).
   rewrite in_cons eq_refl orTb. split; first by [].
   rewrite /minR/maxR//= !big_cons !big_map big_nil.
   rewrite /maxr; case: ifP; intros.
   + exfalso. lra. 
   + by rewrite big_minr_godel_le1.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite !in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (a `/\ b :: B |- A).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons big_nil !big_map.
    rewrite //= /minR/maxR !big_cons !big_map in IH2.
    have hb : (minr ([[b]]_Godel) 1) = [[b]]_Godel. {
      have h := @translate_Bool_T_01 R p Godel b.
      rewrite /minr; case: ifP; rewrite//=; intros.
      lra.}
    rewrite {1}/minr; case: ifP; rewrite hb; move => h.
    * have lerT : forall (a b c : R), a < b -> b <= c -> a <= c. {intros. lra.}
      have lerT1 : forall (a b c : R), a <= b -> b <= c -> a <= c. {intros. lra.}
      rewrite /minr; rewrite{1}/minr in h; move: h; case: ifP; intros;
        move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
      - by rewrite (lerT _ _ _ h IH2).
      - have helper : ([[a]]_Godel < [[b]]_Godel) = false ->
                      [[b]]_Godel <= [[a]]_Godel. { intros. lra.}
        apply helper in n. 
        by rewrite (lerT1 _ _ _ n IH2).
      - by rewrite (lerT _ _ _ h IH2).
    * have lerT : forall (a b c : R), a < b -> b <= c -> a <= c. {intros. lra.}
      have lerT1 : forall (a b c : R), a <= b -> b <= c -> a <= c. {intros. lra.}
      rewrite{1}/minr in h; move: h; case: ifP; intros;
      move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
      - move: i0. by rewrite h//=.
      - have helper : forall (a b : R), a < b = false ->
                      b <= a. { intros. lra.}
        apply helper in n. apply helper in h.
        have ler_mix : forall (a b A B : R), b<= a ->
                       B <= b -> a <= A -> B <= A. {intros. lra.}
        by rewrite (ler_mix _ _ _ _ n h IH2).
  + move/orP: IH1. move => [/eqP IH1 | IH1]. exists (a `/\ b :: B |- A).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons big_nil !big_map.
    rewrite //= /minR/maxR !big_cons !big_map in IH2.
    have hb : (minr ([[b]]_Godel) 1) = [[b]]_Godel. {
      have h := @translate_Bool_T_01 R p Godel b.
      rewrite /minr; case: ifP; rewrite//=; intros.
      lra.}
    rewrite {1}/minr; case: ifP; rewrite hb; move => h.
    * have lerT : forall (a b c : R), a < b -> b <= c -> a <= c. {intros. lra.}
      have lerT1 : forall (a b c : R), a <= b -> b <= c -> a <= c. {intros. lra.}
      rewrite /minr; rewrite{1}/minr in h; move: h; case: ifP; intros;
        move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
      - by rewrite (lerT _ _ _ i IH2).
      - by rewrite (lerT _ _ _ h IH2).
    * have lerT : forall (a b c : R), a < b -> b <= c -> a <= c. {intros. lra.}
      have lerT1 : forall (a b c : R), a <= b -> b <= c -> a <= c. {intros. lra.}
      rewrite{1}/minr in h; move: h; case: ifP; intros;
      move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
  +  exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_godel2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    rewrite //=/minR/maxR !big_map big_cons big_nil in IH12.
    rewrite //=/minR/maxR !big_map big_cons big_nil in IH22.
    have hb_max : forall (x : @expr R Bool_T_def), (maxr ([[x]]_Godel) 0) = [[x]]_Godel. {
      intros.
      have h := @translate_Bool_T_01 R p Godel x.
      rewrite /maxr; case: ifP; rewrite//=; intros.
      lra.}
    have hb_min : forall (x : @expr R Bool_T_def), (minr ([[x]]_Godel) 1) = [[x]]_Godel. {
      intros.
      have h := @translate_Bool_T_01 R p Godel x.
      rewrite /minr; case: ifP; rewrite//=; intros.
      lra.}
    rewrite hb_max in IH12. rewrite hb_max in IH22.
    exists (A |- [:: a `/\ b]).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons !big_nil !big_map.
    rewrite hb_min {2}/minr.
    by case: ifP; intros; rewrite hb_max; lra.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=.
- destruct IHseq_calc_godel1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_godel2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    rewrite //=/minR/maxR !big_map big_cons in IH12.
    rewrite //=/minR/maxR !big_map big_cons in IH22.
    exists (a `\/ b :: B |- A).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons !big_nil !big_map.
    have hb_max : forall (x : @expr R Bool_T_def), (maxr ([[x]]_Godel) 0) = [[x]]_Godel. {
      intros.
      have h := @translate_Bool_T_01 R p Godel x.
      rewrite /maxr; case: ifP; rewrite//=; intros.
      lra.}
    rewrite hb_max {1}/maxr{1}/minr. case: ifP; case: ifP; intros.
    * rewrite {1}/minr in IH12; move: IH12; case: ifP; intros.
      lra. rewrite big_map i0 in n. exfalso. rewrite//=.
    * rewrite {1}/minr !big_map in IH22; move: IH22; case: ifP; intros; rewrite//=.
      rewrite i in n0. exfalso. rewrite//=.
    * rewrite {1}/minr !big_map in IH12; move: IH12; case: ifP; intros; rewrite//=.
      exfalso. rewrite i0 in n. rewrite //=.
    * rewrite {1}/minr !big_map in IH22; move: IH22; case: ifP; intros; rewrite//=.
      rewrite i in n0. exfalso. rewrite//=.    
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite !in_cons in IH1. move/orP : IH1.
    have hb_max : forall (x : @expr R Bool_T_def), (maxr ([[x]]_Godel) 0) = [[x]]_Godel. {
      intros.
      have h := @translate_Bool_T_01 R p Godel x.
      rewrite /maxr; case: ifP; rewrite//=; intros.
      lra.}
  move => [/eqP IH1 | IH1].
  + exists (A |- [:: a `\/ b]).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons big_nil !big_map.
    rewrite //= /minR/maxR !big_cons !big_map big_nil in IH2.
    rewrite hb_max {2}/maxr. rewrite hb_max in IH2.
    case: ifP; intros; rewrite hb_max//=.
    have lerT : forall (a b A : R), a < b -> A <= a -> A <= b. {intros. lra.}
    by rewrite (lerT _ _ _ i IH2).
  + move/orP: IH1. move => [/eqP IH1 | IH1]. 
    exists (A |- [:: a `\/ b]).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons big_nil !big_map.
    rewrite //= /minR/maxR !big_cons !big_map big_nil in IH2.
    rewrite hb_max in IH2. rewrite hb_max {2}/maxr.
    case: ifP; intros; rewrite hb_max//=.
    have abf : forall (a b : R), a < b = false -> b <= a. {intros. lra.}
    apply abf in n.
    have lerT : forall (a b A : R), b <= a -> A <= b -> A <= a. {intros. lra.}
    by rewrite (lerT _ _ _ n IH2).
  +  exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite !in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (A |- [:: a `=> b]). 
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons !big_map.
    rewrite //= /minR/maxR !big_cons !big_map  in IH2.
    case: ifP; intros.
    * rewrite {1}/maxr; rewrite {1}/maxr{1}/minr in IH2; move: IH2;
      case: ifP; case: ifP;
      intros; try lra.
      rewrite big_nil in i0.
      have hb := @translate_Bool_T_01 R p Godel b.
      lra.
    * rewrite big_nil//=. 
      have ha := big_minr_godel_le1 A.
      rewrite /maxr; case: ifP; intros; try lra; rewrite//=.
  +  exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_godel2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + exists (a `=> b :: A1 ++ A2 |- B).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons !big_map.
    rewrite //= /minR/maxR !big_cons !big_map in IH12.
    rewrite //= /minR/maxR !big_cons !big_map in IH22.
    case: ifP; intros; rewrite {1}/minr; case: ifP; rewrite//=;  intros.
    * rewrite big_nil /maxr in IH12.
      have ha := @translate_Bool_T_01 R p Godel a.
      move:  IH12. case: ifP; intros; try lra.
      have hAA := big_minr_if A1 A2.
      rewrite {1}/minr in IH22.
      move: hAA IH22; case: ifP; case: ifP; intros; try lra; rewrite//=.
      - rewrite hAA in i0. 
        have helper: [[b]]_Godel < \big[minr/1]_(j <- A1) [[j]]_Godel ->
                     \big[minr/1]_(j <- A1) [[j]]_Godel <= \big[minr/1]_(j <- A2) [[j]]_Godel ->
                     [[b]]_Godel <= \big[minr/1]_(j <- A2) [[j]]_Godel. {intros. lra.}
        apply (helper i0) in i1. 
        move: i0 helper hAA. move => _ _ _.
        have helper : [[b]]_Godel <= \big[minr/1]_(j <- A2) [[j]]_Godel ->
                      ([[b]]_Godel < \big[minr/1]_(j <- A2) [[j]]_Godel) = false ->
                      [[b]]_Godel = \big[minr/1]_(j <- A2) [[j]]_Godel. {intros. lra.}
        apply (helper i1) in n0.
        rewrite -n0 in IH22.
        by exact IH22.
      - rewrite hAA in i0. move: n hAA. move => _ _. 
        have contr : ([[b]]_Godel < \big[minr/1]_(j <- A2) [[j]]_Godel) = false ->
                     [[b]]_Godel < \big[minr/1]_(j <- A2) [[j]]_Godel ->
                     False. {intros. lra.}
        apply (contr n0) in i0.
        by contradiction.
    * rewrite big_nil /maxr in IH12. move: IH12.
      have ha := @translate_Bool_T_01 R p Godel a.
      case: ifP; intros; try lra.
      rewrite {1}/minr in IH22.
      move: IH22. case: ifP; intros; try lra.
      -  have helper : ([[b]]_Godel < \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel) = false ->
                      [[b]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel ->
                      \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel. 
        {intros. lra.}
        apply (helper n IH22).   
        have hAA := big_minr_if A1 A2.
        move: hAA; case: ifP; intros; rewrite//=; rewrite hAA; rewrite hAA in n; try lra; rewrite//=.
        have helper: \big[minr/1]_(j <- A2) [[j]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel ->
                     \big[minr/1]_(j <- A1) [[j]]_Godel <= \big[minr/1]_(j <- A2) [[j]]_Godel ->
                     \big[minr/1]_(j <- A1) [[j]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel. 
        {intros. lra.}
        by apply (helper IH22 i0).        
      - rewrite big_nil /maxr in IH12. move: IH12.
      have ha := @translate_Bool_T_01 R p Godel a.
      case: ifP; intros; try lra.
    * have hAA := big_minr_godel_le1 (A1++A2).
      have contr : \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel <= 1 ->
                   1 < \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel ->
                   False. {intros. lra.}
      apply (contr hAA) in i.
      by contradiction.
    * move: n0. move => _.
      rewrite big_nil /maxr in IH12. move: IH12.
      have ha := @translate_Bool_T_01 R p Godel a.
      case: ifP; intros; try lra.
      have hAA := big_minr_if A1 A2.
      rewrite {1}/minr in IH22.
      move: hAA IH22; case: ifP; case: ifP; intros; rewrite  hAA; try lra; rewrite//=.
      - have helper : ([[b]]_Godel < [[a]]_Godel) = false ->
                       \big[minr/1]_(j <- A1) [[j]]_Godel <= [[a]]_Godel ->
                       [[b]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel ->
                        \big[minr/1]_(j <- A1) [[j]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel.
        {intros. lra.}
        by apply (helper n IH12 IH22).
      - have helper : \big[minr/1]_(j <- A1) [[j]]_Godel <= \big[minr/1]_(j <- A2) [[j]]_Godel ->
                      \big[minr/1]_(j <- A2) [[j]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel ->
                      \big[minr/1]_(j <- A1) [[j]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel.
        {intros. lra.}
        by apply (helper i IH22).
      - have helper: ([[b]]_Godel < [[a]]_Godel) = false ->
             \big[minr/1]_(j <- A1) [[j]]_Godel <= [[a]]_Godel ->
             (\big[minr/1]_(j <- A1) [[j]]_Godel <= \big[minr/1]_(j <- A2) [[j]]_Godel) = false ->
             [[b]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel ->
             \big[minr/1]_(j <- A2) [[j]]_Godel <= \big[maxr/0]_(j <- B) [[j]]_Godel.
        {intros. lra.}
        by apply (helper n IH12 n1 IH22).      
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=.
Admitted.


Lemma sound_godel' (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
seq_calc_godel' Q -> 
exists (q : ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))), q \in Q 
/\ 
(minR (map (translation Godel p) (fst q))  <=  maxR (map (translation Godel p) (snd q))).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite //= mem_head. split. by []. 
  rewrite /minR/maxR !big_map. admit. (*need helper lemma*)
   (*simple*)
- destruct IHseq_calc_godel' as [M [IH1 IH2]]. 
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
- destruct IHseq_calc_godel' as [q [IH1 IH2]].
  exists q. rewrite mem_cat IH1 orTb.
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_godel' as [M [IH1 IH2]].   
  exists M. rewrite !mem_cat in IH1. 
  rewrite mem_cat. move/orP : IH1. 
  move => [h |/orP h].  rewrite h ?orbT; split; rewrite//=. 
  move: h. move => [h | h]; rewrite h ?orbT; split; rewrite//=.
- destruct IHseq_calc_godel'1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_godel'2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    rewrite //=/minR/maxR !big_map in IH12.
    rewrite //=/minR/maxR !big_map in IH22.
    rewrite //=/maxR/minR. 
    have helper : forall (a b : R), a < b <-> ~(b <= a). {intros. lra.}
          have contr_comp : forall (a b : R), a < b -> b <= a -> false. {
          intros. lra.}
    have hq : exists q : seq (expr Bool_T_def) * seq (expr Bool_T_def),
        q = (A1 ++ A2 |- C) \/ q = B1 ++ B2 |- D. {
      exists (A1 ++ A2 |- C). auto.}
    have h:  ~(exists q : seq (expr Bool_T_def) * seq (expr Bool_T_def),
    (q \in [:: A1 ++ A2 |- C, B1 ++ B2 |- D & Q] /\ \big[minr/1]_(i <- [seq [[i]]_Godel | i <- q.1]) i <= 
               \big[maxr/0]_(i <- [seq [[i]]_Godel | i <- q.2]) i)) -> false. {
        apply minr_maxr_le_godel in IH12; destruct IH12 as [h1 | h1];
        apply minr_maxr_le_godel in IH22; destruct IH22 as [h2 | h2];
        destruct h1 as [h1 h1']; destruct h2 as [h2 h2'];intro;
        rewrite -forallNP in H1;
        have H11 :=  H1 (A1 ++ A2 |- C); rewrite not_andE in H11;
        have H22 := H1 (B1 ++ B2 |- D); rewrite not_andE in H22;
        rewrite mem_head //= !big_map in H11; destruct H11 as [H11 | H11];
        rewrite  !in_cons eq_refl orbT //= !big_map in H22; destruct H22 as [H22 | H22]; auto;
        rewrite -helper in H11; rewrite -helper in H22;
        rewrite -minr_maxr_lt_godel in H11; rewrite -minr_maxr_lt_godel in H22;
        destruct H11 as [H11 H11']; destruct H22 as [H22 H22']; lra.}
     apply contrapT. auto.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
- destruct IHseq_calc_godel' as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (A ++ B |- C).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR !big_map.
    rewrite //= /minR !big_map in IH2.
    have min_weak : 
      \big[minr/1]_(j <- (A ++ B ++ B)) [[j]]_Godel = \big[minr/1]_(j <- (A ++ B)) [[j]]_Godel. { 
      rewrite !big_min_cat_godel {1}/minr {2}/minr {7}/minr {11}/minr. repeat case: ifP; 
      intros; rewrite//=; lra. }
    rewrite min_weak in IH2. by exact IH2.
  + exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel' as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (A ++ B |- C).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR !big_map.
    rewrite //= /minR !big_map in IH2.
    have h := (big_minr_if A B). move: h.
    case: ifP; intros.
    * rewrite -h in IH2. by exact IH2.
    * rewrite h. 
      have le_false : forall (a b : R), a<= b = false -> b <= a. {intros. lra.}
      apply le_false in n. 
      have lerT : forall (a b c : R), a <= c -> b <= a -> b <= c. {intros. lra.}
      by rewrite (lerT _ _ _ IH2 n).
  + exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (X ++ B ++ A ++ Y |- C). 
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_map.
    rewrite //= /minR/maxR !big_map in IH2.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {3}/minr {8}/minr {13}/minr {14}/minr {19}/minr.
    rewrite !big_min_cat_godel {1}/minr {2}/minr {3}/minr {8}/minr {13}/minr {14}/minr {19}/minr in IH2.
    move: IH2.
    repeat case: ifP; intros; rewrite//=; try lra.
    have h : (\big[minr/1]_(j <- B) [[j]]_Godel < \big[minr/1]_(j <- A) [[j]]_Godel) = false ->
             (\big[minr/1]_(j <- A) [[j]]_Godel < \big[minr/1]_(j <- B) [[j]]_Godel) = false ->
             (\big[minr/1]_(j <- A) [[j]]_Godel = \big[minr/1]_(j <- B) [[j]]_Godel). intros. lra.
    apply (h n) in n1.
    rewrite n1. by exact IH2.
(*to do: this is  be brute-forcing cases
            -  come up with a smarter way if possible*)
  + exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (C |- X ++ B ++ A ++ Y).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_map.
    rewrite //= /minR/maxR !big_map in IH2.
    rewrite !big_max_cat_godel {1}/maxr {2}/maxr {3}/maxr {7}/maxr {12}/maxr {13}/maxr {18}/maxr.
    rewrite !big_max_cat_godel {1}/maxr {2}/maxr {3}/maxr {7}/maxr {12}/maxr {13}/maxr {18}/maxr in IH2.
    move: IH2.
    repeat case: ifP; intros; rewrite//=; try lra.
    have h : (\big[maxr/0]_(j <- B) [[j]]_Godel < \big[maxr/0]_(j <- A) [[j]]_Godel) = false ->
             (\big[maxr/0]_(j <- A) [[j]]_Godel < \big[maxr/0]_(j <- B) [[j]]_Godel) = false ->
             (\big[maxr/0]_(j <- A) [[j]]_Godel = \big[maxr/0]_(j <- B) [[j]]_Godel). intros. lra.
    apply (h n0) in n2.
    rewrite -n2. by exact IH2.
  + exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- exists (ldl_bool def false :: A |- B). 
  rewrite in_cons eq_refl orTb. split; first by [].
  rewrite /minR/maxR//= !big_cons !big_map.
  have h : forall (a : R), 0 <= a -> minr 0 (a) = 0. {
    intros. rewrite /minr; case: ifP; rewrite//=; intros; lra.}
  rewrite h.
  * by rewrite big_maxr_godel0.
  * by rewrite big_minr_godel0.
-  exists (A |- [:: ldl_bool def true]).
   rewrite in_cons eq_refl orTb. split; first by [].
   rewrite /minR/maxR//= !big_cons !big_map big_nil.
   rewrite /maxr; case: ifP; intros.
   + exfalso. lra. 
   + by rewrite big_minr_godel_le1.
- destruct IHseq_calc_godel' as [q [IH1 IH2]].
  rewrite !in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (a `/\ b :: B |- A).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons big_nil !big_map.
    rewrite //= /minR/maxR !big_cons !big_map in IH2.
    have hb : (minr ([[b]]_Godel) 1) = [[b]]_Godel. {
      have h := @translate_Bool_T_01 R p Godel b.
      rewrite /minr; case: ifP; rewrite//=; intros.
      lra.}
    rewrite {1}/minr; case: ifP; rewrite hb; move => h.
    * have lerT : forall (a b c : R), a < b -> b <= c -> a <= c. {intros. lra.}
      have lerT1 : forall (a b c : R), a <= b -> b <= c -> a <= c. {intros. lra.}
      rewrite /minr; rewrite{1}/minr in h; move: h; case: ifP; intros;
        move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
      - by rewrite (lerT _ _ _ h IH2).
      - have helper : ([[a]]_Godel < [[b]]_Godel) = false ->
                      [[b]]_Godel <= [[a]]_Godel. { intros. lra.}
        apply helper in n. 
        by rewrite (lerT1 _ _ _ n IH2).
      - by rewrite (lerT _ _ _ h IH2).
    * have lerT : forall (a b c : R), a < b -> b <= c -> a <= c. {intros. lra.}
      have lerT1 : forall (a b c : R), a <= b -> b <= c -> a <= c. {intros. lra.}
      rewrite{1}/minr in h; move: h; case: ifP; intros;
      move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
      - move: i0. by rewrite h//=.
      - have helper : forall (a b : R), a < b = false ->
                      b <= a. { intros. lra.}
        apply helper in n. apply helper in h.
        have ler_mix : forall (a b A B : R), b<= a ->
                       B <= b -> a <= A -> B <= A. {intros. lra.}
        by rewrite (ler_mix _ _ _ _ n h IH2).
  + move/orP: IH1. move => [/eqP IH1 | IH1]. exists (a `/\ b :: B |- A).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons big_nil !big_map.
    rewrite //= /minR/maxR !big_cons !big_map in IH2.
    have hb : (minr ([[b]]_Godel) 1) = [[b]]_Godel. {
      have h := @translate_Bool_T_01 R p Godel b.
      rewrite /minr; case: ifP; rewrite//=; intros.
      lra.}
    rewrite {1}/minr; case: ifP; rewrite hb; move => h.
    * have lerT : forall (a b c : R), a < b -> b <= c -> a <= c. {intros. lra.}
      have lerT1 : forall (a b c : R), a <= b -> b <= c -> a <= c. {intros. lra.}
      rewrite /minr; rewrite{1}/minr in h; move: h; case: ifP; intros;
        move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
      - by rewrite (lerT _ _ _ i IH2).
      - by rewrite (lerT _ _ _ h IH2).
    * have lerT : forall (a b c : R), a < b -> b <= c -> a <= c. {intros. lra.}
      have lerT1 : forall (a b c : R), a <= b -> b <= c -> a <= c. {intros. lra.}
      rewrite{1}/minr in h; move: h; case: ifP; intros;
      move: IH2; rewrite {1}/minr; case: ifP; intros; rewrite//=; try lra.
  +  exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel'1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_godel'2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    rewrite //=/minR/maxR !big_map big_cons big_nil in IH12.
    rewrite //=/minR/maxR !big_map big_cons big_nil in IH22.
    have hb_max : forall (x : @expr R Bool_T_def), (maxr ([[x]]_Godel) 0) = [[x]]_Godel. {
      intros.
      have h := @translate_Bool_T_01 R p Godel x.
      rewrite /maxr; case: ifP; rewrite//=; intros.
      lra.}
    have hb_min : forall (x : @expr R Bool_T_def), (minr ([[x]]_Godel) 1) = [[x]]_Godel. {
      intros.
      have h := @translate_Bool_T_01 R p Godel x.
      rewrite /minr; case: ifP; rewrite//=; intros.
      lra.}
    rewrite hb_max in IH12. rewrite hb_max in IH22.
    exists (A |- [:: a `/\ b]).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons !big_nil !big_map.
    rewrite hb_min {2}/minr.
    by case: ifP; intros; rewrite hb_max; lra.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=.
- destruct IHseq_calc_godel'1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_godel'2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    rewrite //=/minR/maxR !big_map big_cons in IH12.
    rewrite //=/minR/maxR !big_map big_cons in IH22.
    exists (a `\/ b :: B |- A).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons !big_nil !big_map.
    have hb_max : forall (x : @expr R Bool_T_def), (maxr ([[x]]_Godel) 0) = [[x]]_Godel. {
      intros.
      have h := @translate_Bool_T_01 R p Godel x.
      rewrite /maxr; case: ifP; rewrite//=; intros.
      lra.}
    rewrite hb_max {1}/maxr{1}/minr. case: ifP; case: ifP; intros.
    * rewrite {1}/minr in IH12; move: IH12; case: ifP; intros.
      lra. rewrite big_map i0 in n. exfalso. rewrite//=.
    * rewrite {1}/minr !big_map in IH22; move: IH22; case: ifP; intros; rewrite//=.
      rewrite i in n0. exfalso. rewrite//=.
    * rewrite {1}/minr !big_map in IH12; move: IH12; case: ifP; intros; rewrite//=.
      exfalso. rewrite i0 in n. rewrite //=.
    * rewrite {1}/minr !big_map in IH22; move: IH22; case: ifP; intros; rewrite//=.
      rewrite i in n0. exfalso. rewrite//=.    
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=.
- destruct IHseq_calc_godel' as [q [IH1 IH2]].
  rewrite !in_cons in IH1. move/orP : IH1.
    have hb_max : forall (x : @expr R Bool_T_def), (maxr ([[x]]_Godel) 0) = [[x]]_Godel. {
      intros.
      have h := @translate_Bool_T_01 R p Godel x.
      rewrite /maxr; case: ifP; rewrite//=; intros.
      lra.}
  move => [/eqP IH1 | IH1].
  + exists (A |- [:: a `\/ b]).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons big_nil !big_map.
    rewrite //= /minR/maxR !big_cons !big_map big_nil in IH2.
    rewrite hb_max {2}/maxr. rewrite hb_max in IH2.
    case: ifP; intros; rewrite hb_max//=.
    have lerT : forall (a b A : R), a < b -> A <= a -> A <= b. {intros. lra.}
    by rewrite (lerT _ _ _ i IH2).
  + move/orP: IH1. move => [/eqP IH1 | IH1]. 
    exists (A |- [:: a `\/ b]).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons big_nil !big_map.
    rewrite //= /minR/maxR !big_cons !big_map big_nil in IH2.
    rewrite hb_max in IH2. rewrite hb_max {2}/maxr.
    case: ifP; intros; rewrite hb_max//=.
    have abf : forall (a b : R), a < b = false -> b <= a. {intros. lra.}
    apply abf in n.
    have lerT : forall (a b A : R), b <= a -> A <= b -> A <= a. {intros. lra.}
    by rewrite (lerT _ _ _ n IH2).
  +  exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel' as [q [IH1 IH2]].
  rewrite !in_cons in IH1. move/orP : IH1.
  move => [/eqP IH1 | IH1].
  + exists (A |- [:: `~ a]).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons big_nil !big_map.
    rewrite //= /minR/maxR !big_cons !big_map big_nil in IH2.
    case: ifP; move => h.
    * have maxr00 : maxr 0 0 = 0. {intros; rewrite/maxr; case:ifP; intros; rewrite//=.}
      rewrite maxr00 in IH2.
      rewrite /maxr; case: ifP; intros; rewrite//=; 
      rewrite {1}/minr in IH2; move: IH2; case: ifP; intros; rewrite//=.
      - lra.
      - have ha := @translate_Bool_T_01 R p Godel a.
        have hA := @translate_Bool_T_01 R p Godel (ldl_and A).
        rewrite//= /minR big_map in hA.
        lra.
    * have maxr10 : @maxr R 1 0 = 1. {intros; rewrite/maxr; case:ifP; intros; lra.}
      rewrite maxr10.
      have maxr00 : maxr 0 0 = 0. {intros; rewrite/maxr; case:ifP; intros; rewrite//=.}
      rewrite maxr00 in IH2.
      rewrite {1}/minr in IH2; move: IH2; case: ifP; intros; rewrite//=; by rewrite (big_minr_godel_le1 A).
  +  exists q. 
    by rewrite !in_cons IH1 IH2 !orbT//=.
- destruct IHseq_calc_godel'1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_godel'2 as [q2 [IH21 IH22]].
  rewrite in_cons in IH11. rewrite in_cons in IH21. 
  move/orP : IH11. move/orP: IH21.
  move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  +  exists ((`~ a) :: A1 ++ A2 |- B).
    subst. rewrite in_cons eq_refl orTb. split; first by [].
    rewrite //= /minR/maxR !big_cons !big_map.
    rewrite //= /minR/maxR !big_cons !big_map big_nil in IH12.
    rewrite //= /minR/maxR !big_cons !big_map in IH22.
    rewrite {1}/minr. case: ifP; case: ifP; intros; rewrite//=.
    * have hB := @translate_Bool_T_01 R p Godel (ldl_or B).
      rewrite//= /maxR big_map in hB.
      have triv : 0 <= \big[maxr/0]_(j <- B) [[j]]_Godel <= 1 ->
                  0 <= \big[maxr/0]_(j <- B) [[j]]_Godel. {intros. lra.}
      apply triv in hB.
      by exact hB.
    * have hAA := big_minr_godel_le1 (A1 ++ A2).
      have contr : 1 < \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel ->
                   \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel <= 1 ->
                   False. {intros. lra.}
      apply (contr i) in hAA.
      contradiction.
    *  have hAA :=  @translate_Bool_T_01 R p Godel (ldl_and (A1 ++ A2)).
       rewrite//= /minR big_map in hAA.
       have helper :(0 < \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel) = false ->
                     0 <= \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel <= 1 ->
                     \big[minr/1]_(j <- (A1 ++ A2)) [[j]]_Godel = 0. {intros; lra.}
       apply (helper n) in hAA.
       have hB :=  @translate_Bool_T_01 R p Godel (ldl_or B).
       rewrite//= /maxR big_map in hB.
       rewrite hAA. 
       have triv : 0 <= \big[maxr/0]_(j <- B) [[j]]_Godel <= 1 ->
                  0 <= \big[maxr/0]_(j <- B) [[j]]_Godel. {intros; lra.}
      apply triv in hB.
      by exact hB.
    * rewrite /maxr in IH12. move: IH12.
      have ha :=  @translate_Bool_T_01 R p Godel a.
      case: ifP; intros; rewrite//=; first lra.
      have hx : forall (x : R), (0 < x) = false -> (0 <= x <= 1) ->
                 x = 0. {intros; lra.}
      apply (hx ([[a]]_Godel) n) in ha. move: n n1. move => _ _ . 
      rewrite ha in IH12.
      have hA1 :=  @translate_Bool_T_01 R p Godel (ldl_and (A1)).
       rewrite//= /minR big_map in hA1.
      have helper : \big[minr/1]_(j <- A1) [[j]]_Godel <= 0 ->
                    0 <= \big[minr/1]_(j <- A1) [[j]]_Godel <= 1 ->
                     \big[minr/1]_(j <- A1) [[j]]_Godel = 0. {intro; lra.}
      apply (helper IH12) in hA1.
      have hAA := big_minr_if A1 A2. move: hAA.
      have hA2 :=  @translate_Bool_T_01 R p Godel (ldl_and (A2)).
       rewrite//= /minR big_map in hA2.
      case: ifP; intros; rewrite//=.
      - rewrite hAA  hA1.
        have hB :=  @translate_Bool_T_01 R p Godel (ldl_or B).
        rewrite//= /maxR big_map in hB.
        have triv : 0 <= \big[maxr/0]_(j <- B) [[j]]_Godel <= 1 ->
                  0 <= \big[maxr/0]_(j <- B) [[j]]_Godel. {intros; lra.}
        apply triv in hB.
        by exact hB.
      - move: helper IH12 hx ha n0. move => _ _ _ _ _.
        have helper : (\big[minr/1]_(j <- A1) [[j]]_Godel <= \big[minr/1]_(j <- A2) [[j]]_Godel) = false ->
                      (\big[minr/1]_(j <- A1) [[j]]_Godel > \big[minr/1]_(j <- A2) [[j]]_Godel). 
        {intros; lra.}
        apply helper in n. rewrite hA1 in n.
        have contr : 0 <= \big[minr/1]_(j <- A2) [[j]]_Godel <= 1 ->
                     \big[minr/1]_(j <- A2) [[j]]_Godel < 0 ->
                     False. {intros; lra.}
        apply (contr hA2) in n.
        contradiction.
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=. 
  + exists q2. 
    by rewrite !in_cons h2 IH22 !orbT//=. 
  + exists q1. 
    by rewrite !in_cons h1 IH12 !orbT//=.
Admitted.

Lemma godel_neg_impl_admissable (e : @expr R Bool_T_def):
 [[`~ e]]_Godel = [[e `=> ldl_bool def false]]_Godel.
Proof.
rewrite//=.
Qed. 

Lemma equivalence_godel (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
  seq_calc_godel' Q -> seq_calc_godel Q.
Proof.
intros.
dependent induction H. 
- apply id_g.
- apply eex_g. by exact IHseq_calc_godel'.
- apply ew_g. by exact IHseq_calc_godel'.
- apply ec_g. by exact IHseq_calc_godel'.
- apply comm_hyper_g. 
  + by exact IHseq_calc_godel'1. 
  + by exact IHseq_calc_godel'2. 
- apply comm_g. by exact IHseq_calc_godel'.
- apply weak_g. by exact IHseq_calc_godel'.
- apply exL_g. by exact IHseq_calc_godel'.
- apply exR_g. by exact IHseq_calc_godel'.
- apply bot_g. 
- apply top_g.
- apply andL_g. by exact IHseq_calc_godel'.
- apply andR_g.
  + by exact IHseq_calc_godel'1. 
  + by exact IHseq_calc_godel'2. 
- apply orL_g.
  + by exact IHseq_calc_godel'1. 
  + by exact IHseq_calc_godel'2. 
- apply orR_g. by exact IHseq_calc_godel'.
- rewrite neg_impl. apply implR_g; rewrite//=.
- rewrite neg_impl. apply implL_g; rewrite//=.
Qed.
 
End hypersequent_godel.
