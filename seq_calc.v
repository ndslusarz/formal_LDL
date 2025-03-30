From HB Require Import structures.
From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder finmap multiset.
Require Import mathcomp_extra analysis_extra ldl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Reserved Notation "{[ e ]}" (format "{[  e  ]}").

HB.instance Definition _ (R : realType) b :=
  @gen_eqMixin (@expr R (Bool_T b)).
HB.instance Definition _ (R : realType) b := 
  @gen_choiceMixin (@expr R (Bool_T b)). 

Reserved Notation "Q |= P" (no associativity, at level 61).
Reserved Notation "Q |- P" (no associativity, at level 61).

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
(*not in lnguage for now, may add for fuzzy logic because of residuums*)
(*| implR : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
     a+`Q |= b +`P ->
      Q |= (a `=> b) +` P
| implL : forall (Q P S : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    Q |= a +` P ->   b+`Q |= S ->
      (a `=> b)+`Q |=  P `+` S
| negR : forall Q P a,
    a +`Q  |= P ->
      Q |= (`~ a) +` P*)
| negL : forall Q P a,
    Q |= a +` P ->
      (`~ a)+`Q|= P
where "Q |= P" := (seq_calc_bool_ms Q P).


Proposition sc_bool_consistent_weak : ~ (mset0 |= [mset ldl_bool def false]).
Proof.

(*have H3 := ms_non0 a Q. by [].*)
admit. (*probably not useful need a stronger version?*)
Admitted.

Proposition sc_bool_consistent (Q P : {mset expr Bool_T_def}): 
  Q |= P ->
  (forall (q : expr Bool_T_def), q \in Q -> <<q>> = <<ldl_bool def true>>) ->
     (forall (p : expr Bool_T_def) , (p \in P) -> <<p>> != <<ldl_bool def false>>).
Proof.
 rewrite //=. move => H0 H. dependent induction H0; move => p p0.
- have H1 := H p. rewrite in_mset1D in H1. (*after i apply H1 I'll have one non-provable case, must be
wrong lemma statement*)

Admitted.


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


Inductive seq_calc_godel :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}
(*-> {mset (seq {mset (@expr R Bool_T_def)})}*)
      -> Prop :=
| id_g : forall (Q :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})})
                (A : {mset (@expr R Bool_T_def)}),
    seq_calc_godel ( (A |- A) +` Q)
(*structural*)
| ew_g : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_godel Q ->
    seq_calc_godel (Q `+` P) (*correct order*)
| ec_g : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_godel (Q `+` P `+` P) ->
    seq_calc_godel (Q `+` P)
(*this was a single conclusion version*)
(*| comm_hyper_g : forall  Q 
                  (A1 A2 B1 B2 C D: {mset (@expr R Bool_T_def)}),
    seq_calc_godel (((A1 `+` B1) |- C) +` Q) ->
    seq_calc_godel (((A2 `+` B2) |- D) +` Q) ->               
    seq_calc_godel (Q `+` [mset ((A1 `+` A2) |- C)] `+` [mset ((B1 `+` B2) |- D)])*)
| comm_hyper_g : forall  Q 
                  (A1 A2 B1 B2 C1 C2 D1 D2: {mset (@expr R Bool_T_def)}),
    seq_calc_godel (((A1 `+` B1) |- C1 `+` D1) +` Q) ->
    seq_calc_godel (((A2 `+` B2) |- C2 `+` D2) +` Q) ->               
    seq_calc_godel (Q `+` [mset ((A1 `+` A2) |- C1 `+` C2)] `+` [mset ((B1 `+` B2) |- D1 `+` D2)])
| comm_g : forall Q 
                  (A B C : {mset (@expr R Bool_T_def)}),
    seq_calc_godel (((A `+` B `+` B) |- C) +` Q) ->
    seq_calc_godel (((A `+` B) |- C) +` Q)
| weak_g : forall Q 
                  (A B C : {mset (@expr R Bool_T_def)}),
    seq_calc_godel ((A |- C) +` Q ) ->
    seq_calc_godel (((A `+` B) |- C) +` Q )
(*logical*)
| bot_g : forall Q 
                 (A B : {mset (@expr R Bool_T_def)}),
    seq_calc_godel (((ldl_bool def false +` A) |- B) +` Q)
| top_g : forall Q 
                 (A : {mset (@expr R Bool_T_def)}),
    seq_calc_godel ((A |- [mset (ldl_bool def true)]) +` Q )
| andL_g1 : forall Q 
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_godel (((a +` B) |- A) +` Q ) ->
    seq_calc_godel ((((a `/\ b) +` B) |- A) +` Q) 
| andL_g2 : forall Q
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_godel (((b +` B) |- A) +` Q ) ->
    seq_calc_godel ((((a `/\ b) +` B) |- A) +` Q )
| andR_g : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel ( (A |- [mset a]) +` Q ) ->
    seq_calc_godel ( (B |- [mset b]) +` Q) ->
    seq_calc_godel ((A |- [mset (a `/\ b)]) +` Q )
(*| orL_g : forall  Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((b +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset ((a +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset (((a `\/ b) +` B) |- A)])
| orR_g1 : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset a])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (a `\/ b)])])
| orR_g2 : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset b])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (a `\/ b)])])
| negR_g : forall Q
                  (A : {mset (@expr R Bool_T_def)})
                  (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset a])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (`~ a)])])
| negL_g : forall Q
                  (A B: {mset (@expr R Bool_T_def)})
                  (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((a +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset (((`~a) +` B) |- A)])*)

(*cut rule*)
| cut_g : forall Q
                 (A1 A2 B: {mset (@expr R Bool_T_def)})
                 (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((a +` A1) |- B)]) ->
    seq_calc_godel (Q `+` [mset (A2 |-[mset a])]) ->
    seq_calc_godel (Q `+` [mset ((A1 `+` A2) |- B)]).

(*or should it not be equal to 1? greater then something? or just non-equal to zero*)
Lemma sound_godel_1 (Q : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}):
seq_calc_godel Q -> 
exists (q : ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})), q \in Q 
/\ 
       (
         (forall (x : expr (Bool_T def)), x \in (fst q) -> [[x]]_Godel = [[ldl_bool def true]]_Godel) ->
         (exists (y : expr (Bool_T def)), y \in (snd q) /\ [[y]]_Godel = [[ldl_bool def true]]_Godel)

       ).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite in_mset1D eq_refl orTb. split. by [].  
  simpl. intros. exists (ldl_bool def true). rewrite//=. 
  split; first last.  by rewrite//=. 
  have H1 := H (ldl_bool def true). 
  rewrite//= in H1. move: H1.
  
  admit. (*I just need to make erefl work*)
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  exists q. rewrite in_msetD IH1 orTb. 
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_godel as [M [IH1 IH2]].   
  exists M. (*trivial, rearrange*) admit. 
(*the interesting one, communication ruleu*)
- destruct IHseq_calc_godel1 as [q1 [IH11 IH12]]. 
  destruct IHseq_calc_godel2 as [q2 [IH21 IH22]].
  have in_msetD3 : forall (q : K) (Q A B : {mset K}), q \in Q `+` A `+` B =
                         (q \in Q) || (q \in A) || (q \in B). {
    admit. 
  } 
  have h : exists qq, qq = q1 \/ qq = q2. {
  exists q1. left. by apply Logic.eq_refl.}
  destruct h as [qq Hq].
  exists qq. (*I don't think this exists will work*)
  split. 
  + admit.
  +
 admit.
 admit. admit.
- exists (ldl_bool def false +` A |- B).
  rewrite in_mset1D eq_refl orTb. split. by [].
  simpl. intros.
  have H1 := H (ldl_bool def false).
  rewrite//= in H1.
  exfalso. move: H1. apply contrapT. rewrite  not_implyE.
  rewrite not_andE notE. left. 
  rewrite in_mset1D eq_refl orTb//=.
  rewrite  not_implyE. split. by []. 
  
  (*just searching for right lemma, got 1<>0*)
  admit.
- exists ((A |- [mset ldl_bool def true])).
  split. admit. (*obvious, in_mset1D*)
  rewrite//=; move => _. 
  exists (ldl_bool def true). 
  rewrite mset11. split; rewrite//=; by []. 
- destruct IHseq_calc_godel as [Qa [IH1 IH2]].
  exists (a `/\ b +` B |- A).
  split. 
  + admit. (*obvious, belongs*)
  + rewrite//=. intros. 
    have H1 := H0 (a `/\ b).
    have h1 : a `/\ b \in a `/\ b +` B. {
      by  rewrite in_mset1D eq_refl orTb.
      }
    have Hab := H1 h1. rewrite//= in Hab.
    (*from this should be able to get that both a, b = 1 - given the proof of 
      domain consistency that can be borrowed from fuzzy.v*)

admit.
Admitted.


(*
nope, not this one, left as reminder, delete later
Lemma sound_hypersec_godel (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})})
                           (s : ({mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)}) ) :
(forall (q : expr (Bool_T def)), q \in (snd s) ->
                                      [[q]]_Godel = [[ldl_bool def true]]_Godel) ->
                seq_calc_godel (Q `+` [mset s] `+` P) -> (*does not work without P - but P not sufficient*)
                forall (x : expr (Bool_T def)), x \in (fst s) ->
                [[x ]]_Godel = [[ldl_bool def true]]_Godel.
Proof.
Admitted.*)
End hypersequent_godel.

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


Inductive seq_calc_luka :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}
(*-> {mset (seq {mset (@expr R Bool_T_def)})}*)
      -> Prop :=
| id_l : forall (Q :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})})
                (A : {mset (@expr R Bool_T_def)}),
    seq_calc_luka ( (A |- A) +` Q)
(*structural*)
| ew_l : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_luka Q ->
    seq_calc_luka (Q `+` P) (*correct order*)
| ec_l : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_luka (Q `+` P `+` P) ->
    seq_calc_luka (Q `+` P)
(*add split and mix rules*)
| split_l : forall Q 
                  (A B C D: {mset (@expr R Bool_T_def)}),
    seq_calc_luka (((A `+` B) |- (C `+` D)) +` Q) ->
    seq_calc_luka ([mset (A |- C)] `+` [mset (B |- D)] `+` Q)
(*logical*)
| bot_l : forall Q 
                 (A B : {mset (@expr R Bool_T_def)}),
    seq_calc_luka (((ldl_bool def false +` A) |- B) +` Q)
| top_l : forall Q 
                 (A : {mset (@expr R Bool_T_def)}),
    seq_calc_luka ((A |- [mset (ldl_bool def true)]) +` Q )
| andL_l1 : forall Q 
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_luka (((a +` B) |- A) +` Q ) ->
    seq_calc_luka ((((a `/\ b) +` B) |- A) +` Q) 
| andL_l2 : forall Q
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_luka (((b +` B) |- A) +` Q ) ->
    seq_calc_luka ((((a `/\ b) +` B) |- A) +` Q )
| andR_l : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_luka ( (A |- [mset a]) +` Q ) ->
    seq_calc_luka ( (B |- [mset b]) +` Q) ->
    seq_calc_luka ((A |- [mset (a `/\ b)]) +` Q )
(*| orL_g : forall  Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((b +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset ((a +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset (((a `\/ b) +` B) |- A)])
| orR_g1 : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset a])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (a `\/ b)])])
| orR_g2 : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset b])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (a `\/ b)])])
| negR_g : forall Q
                  (A : {mset (@expr R Bool_T_def)})
                  (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset a])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (`~ a)])])
| negL_g : forall Q
                  (A B: {mset (@expr R Bool_T_def)})
                  (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((a +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset (((`~a) +` B) |- A)])*).

Definition eval_luka  (Q : {mset (@expr R Bool_T_def)})
  := 1%R + (size Q)%:R - sumR (map (translation Lukasiewicz p) Q).



Lemma sound_luka_1 (Q : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}):
seq_calc_luka Q -> 
exists (q : ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})), q \in Q 
/\ 
       (

         eval_luka (fst q) <= eval_luka (snd q)

       ).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite in_mset1D eq_refl orTb. split. by [].  
  simpl. by lra.
- destruct IHseq_calc_luka as [q [IH1 IH2]].
  exists q. rewrite in_msetD IH1 orTb. 
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_luka as [M [IH1 IH2]].   
  exists M. rewrite !in_msetD in IH1. 
  rewrite in_msetD. move/orP : IH1. 
  by move => [h | h]; rewrite h ?orbT; split; rewrite//=. 
- destruct IHseq_calc_luka as [q1 [IH1 IH2]]. 
  rewrite in_msetD in IH1. move/orP : IH1.
  move => [h1 | h2]; first last.
  + exists q1. rewrite in_msetD h2 orbT.
    split; rewrite//=. 
  + rewrite in_mset1 in h1. move/eqP : h1.
    move => h1. 
    subst.
    rewrite /eval_luka//= in IH2.
    exists (A |- C).
    rewrite in_msetD in_mset2 eq_refl !orTb. split. by [].
    rewrite /eval_luka//=.
    admit. (*bit gnarly math, but does work on paper I think due to the domain
             being 0,1, will need helper lemmas*)
- exists (ldl_bool def false +` A |- B).
  rewrite in_mset1D eq_refl orTb. split. by [].
  simpl. intros.
  have H1 := H (ldl_bool def false).
  rewrite//= in H1.
  exfalso. move: H1. apply contrapT. rewrite  not_implyE.
  rewrite not_andE notE. left. 
  rewrite in_mset1D eq_refl orTb//=.
  rewrite  not_implyE. split. by []. 
  
  (*just searching for right lemma, got 1<>0*)
  admit.
- exists ((A |- [mset ldl_bool def true])).
  split. admit. (*obvious, in_mset1D*)
  rewrite//=; move => _. 
  exists (ldl_bool def true). 
  rewrite mset11. split; rewrite//=; by []. 
- destruct IHseq_calc_godel as [Qa [IH1 IH2]].
  exists (a `/\ b +` B |- A).
  split. 
  + admit. (*obvious, belongs*)
  + rewrite//=. intros. 
    have H1 := H0 (a `/\ b).
    have h1 : a `/\ b \in a `/\ b +` B. {
      by  rewrite in_mset1D eq_refl orTb.
      }
    have Hab := H1 h1. rewrite//= in Hab.


admit.
Admitted.

End hypersequent_lukasiewicz.
