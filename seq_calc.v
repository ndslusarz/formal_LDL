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
(*| bot_g : forall Q 
                 (A B : {mset (@expr R Bool_T_def)}),
    seq_calc_godel (((ldl_bool def false +` A) |- B) +` Q)*)
| bot_g : forall Q 
                 (B : {mset (@expr R Bool_T_def)}),
    seq_calc_godel (([mset (ldl_bool def false )] |- B) +` Q)
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
.

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
- (*exists (ldl_bool def false +` A |- B).
  rewrite in_mset1D eq_refl orTb. split. by [].
  simpl. intros.
  have H1 := H (ldl_bool def false).
  rewrite//= in H1.
  exfalso. move: H1. apply contrapT. rewrite  not_implyE.
  rewrite not_andE notE. left. 
  rewrite in_mset1D eq_refl orTb//=.
  rewrite  not_implyE. split. by []. *)
  
  (*commented out, was for old version of bot rule*)
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

(*generalise later?*)
Lemma sum_in_msetD_expr (A B : {mset (@expr R Bool_T_def)}):
    (\sum_(i <- [seq [[i]]_Godel | i <- A `+` B]) i) = 
      (\sum_(i <- [seq [[i]]_Godel | i <- A]) i) + (\sum_(i <- [seq [[i]]_Godel | i <- B]) i).
Proof.
Admitted.

(*proof is in fuzzy.v - either import from there or move proof here?*)
(*Lemma translate_Bool_T_01 dl (e : expr Bool_T_def) :
  0 <= [[ e ]]_ dl <= 1.
Proof.
Admitted.

(*based on Łukasiewicz definition*)
Lemma sound_godel_2 (Q : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}):
seq_calc_godel Q -> 
exists (q : ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})), q \in Q 
/\ 
(sumR (map (translation Godel p) (fst q)) <= sumR (map (translation Godel p) (snd q))).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite in_mset1D eq_refl orTb. split. by [].  
  simpl. by lra.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  exists q. rewrite in_msetD IH1 orTb. 
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_godel as [M [IH1 IH2]].   
  exists M. rewrite !in_msetD in IH1. 
  rewrite in_msetD. move/orP : IH1. 
  by move => [h | h]; rewrite h ?orbT; split; rewrite//=. 
- destruct IHseq_calc_godel1 as [q1 [IH11 IH12]]. 
  destruct IHseq_calc_godel2 as [q2 [IH21 IH22]].
  rewrite in_mset1D in IH11.
  rewrite in_mset1D in IH21.
  move/orP: IH11. move/orP: IH21.
  move => [h1 | h1] [h2 | h2]; rewrite//=.
  + move/eqP: h1. move/eqP : h2.  
    move => h1 h2. 
    subst. 
    have IH := lerD IH12 IH22.
    rewrite /sumR //= in IH. 
    rewrite !sum_in_msetD_expr in IH.
    set (a1 := (\sum_(i <- [seq [[i]]_Godel | i <- A1]) i)) in *.
    set (a2 := (\sum_(i <- [seq [[i]]_Godel | i <- A2]) i)) in *.
    set (b1 := (\sum_(i <- [seq [[i]]_Godel | i <- B1]) i)) in *.
    set (b2 := (\sum_(i <- [seq [[i]]_Godel | i <- B2]) i)) in *.
    set (c1 := (\sum_(i <- [seq [[i]]_Godel | i <- C1]) i)) in *.
    set (c2 := (\sum_(i <- [seq [[i]]_Godel | i <- C2]) i)) in *.
    set (d1 := (\sum_(i <- [seq [[i]]_Godel | i <- D1]) i)) in *.
    set (d2 := (\sum_(i <- [seq [[i]]_Godel | i <- D2]) i)) in *.
    have helper : 
    ((a1 + b1 + a2 + b2) <= (c1 + d1 + c2 +d2)) -> 
    ((a1 + a2 + b1 + b2 - d1 - d2) <= (c1 + c2)).  {
      lra. }
    rewrite !addrA in IH.
    apply helper in IH. move: helper. move => _. 
    have le_or : forall (a b : R), a <= b \/ a >= b. { intros. lra.} 
    have h1 := le_or (b1 + b2) (d1 + d2).
    destruct h1 as [h1 | h1].
    * exists (B1 `+` B2 |- D1 `+` D2). split. 
      - by rewrite in_msetD//= mset11 orbT. 
      - rewrite /sumR //= !sum_in_msetD_expr.
        rewrite /b1/b2/d1/d2 in h1.
        by apply h1. 
    * have helper1 : d1 + d2 <= b1 + b2 -> (b1 + b2 - d1 - d2 >= 0). {
        lra.}
     apply helper1 in h1.
      have helper2 : 0 <= (b1 + b2)%E - d1 - d2 ->
        a1 + a2 + b1 + b2 - d1 - d2 <= c1 + c2 ->
        a1 + a2  <= c1 + c2. {
        intros. lra.} 
      have hh := helper2 h1 IH.
      exists (A1 `+` A2 |- C1 `+` C2). split. 
      - by rewrite msetDAC in_msetD//= mset11 orbT. 
(* if I do in_msetD//= mset11. without changing order
 this times out? I didn't think it'd be complex enough*)
      - rewrite /sumR //= !sum_in_msetD_expr.
        rewrite /a1/a2/c1/c2 in hh.
        by apply hh. 
  + exists q1. 
    rewrite !in_msetD h2 IH12. 
    split; rewrite//=. 
  + exists q2. 
    rewrite !in_msetD h1 IH22. 
    split; rewrite//=. 
  + exists q1. 
    rewrite !in_msetD h2 IH12. 
    split; rewrite//=. 
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite in_mset1D in IH1. move/orP: IH1.
  move => [/eqP h | h]. 
  + subst. rewrite /sumR//= in IH2.
    rewrite !sum_in_msetD_expr in IH2.
    set (a := (\sum_(i <- [seq [[i]]_Godel | i <- A]) i)) in *.
    set (b := (\sum_(i <- [seq [[i]]_Godel | i <- B]) i)) in *.
    set (c := (\sum_(i <- [seq [[i]]_Godel | i <- C]) i)) in *.
    have le_add2 : forall (a b c : R), b >= 0 -> a + b + b <= c -> a + b <= c. { intros. lra.} 
    apply le_add2 in IH2; first last.
    * rewrite /b//=. rewrite big_map sumr_ge0//=. move => i _.
      have t01 := translate_Bool_T_01 Godel i.
      have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
      apply le_double in t01. destruct t01 as [t0 t1].
      by apply t0.
    exists (A `+` B |- C). split. 
    * by rewrite in_mset1D eq_refl orTb.
    * rewrite /sumR//= sum_in_msetD_expr.
      rewrite /a/b in IH2.
      by apply IH2.
  + exists q. 
    rewrite !in_msetD h IH2. 
    split; rewrite ?orbT //=.
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  rewrite in_mset1D in IH1. move/orP: IH1.
  move => [/eqP h | h].
  + subst. rewrite//= in IH2.
  admit.
- exists (ldl_bool def false +` A |- B). 
  
admit.
- admit.
- admit.
- admit.
Admitted.*)


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
| empty : forall (Q :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_luka ((mset0 |- mset0) +` Q)
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
| mix_l : forall Q 
                  (A B C D: {mset (@expr R Bool_T_def)}),
    seq_calc_luka ((A |- C) +` Q) ->
    seq_calc_luka ((B |- D) +` Q) ->
    seq_calc_luka (((A `+` B) |- (C `+` D)) +` Q)
(*logical*)
(*both are restricted to a single-conclusion case for Lukasiewicz*)
| bot_l : forall Q 
                 (A : {mset (@expr R Bool_T_def)})
                 (b : @expr R Bool_T_def),
    seq_calc_luka (((ldl_bool def false +` A) |- [mset b]) +` Q)
| top_l : forall Q 
                 (A : {mset (@expr R Bool_T_def)}),
    seq_calc_luka ((A |- [mset (ldl_bool def true)]) +` Q)
(*new formulation, not standard conjunction rule*)
|andL_l : forall Q 
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_luka (((a +` [mset b] `+` B) |- A) +` Q ) ->
    seq_calc_luka (((ldl_bool def false +` B) |- A) +` Q ) ->
    seq_calc_luka ((((a `/\ b) +` B) |- A) +` Q)
| andR_l : forall Q 
                 (A B : {mset (@expr R Bool_T_def)})
                 (a b : @expr R Bool_T_def),
    seq_calc_luka ( (A |- (a +` [mset b] `+` B)) +` [mset (A |- (ldl_bool def false +` B))] `+` Q )  ->
    seq_calc_luka ((A |- (a `/\ b) +` B) +` Q )
(*| andL_l1 : forall Q 
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
    seq_calc_luka ( (A |- a +` B) +` Q ) ->
    seq_calc_luka ( (A |-  b +` B) +` Q) ->
    seq_calc_luka ((A |- (a `/\ b) +` B) +` Q )*)
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

Lemma sum_in_msetD_expr_Luka (A B : {mset (@expr R Bool_T_def)}):
    (\sum_(i <- [seq [[i]]_Lukasiewicz | i <- A `+` B]) i) = 
      (\sum_(i <- [seq [[i]]_Lukasiewicz | i <- A]) i)%R + (\sum_(i <- [seq [[i]]_Lukasiewicz | i <- B]) i)%R.
Proof.
Admitted.

Lemma big_mset_add_el :
  forall [R : Type] (idx : R) (op : R -> R -> R) [K : choiceType] (i : K) (r : {mset K}) (P : pred K) (F : K -> R),
  let x := \big[op/idx]_(j <- r | P j) F j in
  \big[op/idx]_(j <- (i +` r) | P j) F j = (if P i then op (F i) x else x).
Proof.
intros. 
case: ifP; intros.
- 
Admitted.

Lemma size_mset1 (a : K) : (size [mset a])%R = 1.
Proof.
rewrite size_mset. 
Admitted.



Definition eval_luka  (Q : {mset (@expr R Bool_T_def)})
  := 1%R + \sum_(i  <-Q) ([[i]]_Lukasiewicz -1).

(*- (size  Q)%:R *)(*+ (\sum_(i <- [seq [[i]]_Lukasiewicz | i <-Q]) i)%R.*)

(*(sumR (map (translation Lukasiewicz p) Q))%R.*)

Lemma eval_luka_add_el (Q : {mset (@expr R Bool_T_def)}) (q : (@expr R Bool_T_def)) :
  eval_luka (q +` Q) = eval_luka Q + [[q]]_Lukasiewicz -1.
Proof.
rewrite /eval_luka//=. rewrite big_mset_add_el addrA. 

Admitted.

Lemma eval_luka_el (q : (@expr R Bool_T_def)) :
  eval_luka ([mset q]) = [[q]]_Lukasiewicz.
Proof.
rewrite/eval_luka.
Admitted.

Lemma eval_luka1 (Q : {mset (@expr R Bool_T_def)}):
  eval_luka Q <= 1.
Proof.
Admitted.


(*used enough times to move outside of proof*)
Lemma le_or : forall (a b : R), a <= b \/ a >= b.
Proof.
 intros. lra.
Qed.

Lemma size_msetAdd (A B : {mset K}) : (size (A `+` B))%E = size A + size B.
Proof.


Admitted.


(*proof is in fuzzy.v - either import from there or move proof here?*)
Lemma translate_Bool_T_01 dl (e : expr Bool_T_def) :
  0 <= [[ e ]]_ dl <= 1.
Proof.
Admitted.


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
- exists (mset0 |- mset0). 
  rewrite in_mset1D eq_refl orTb. split. by []. 
  rewrite /eval_luka//=.
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
    rewrite /eval_luka//=/sumR.
    
    
    admit. (*bit gnarly math, but does work on paper due to the domain
             being 0,1, will need helper lemmas*)
- destruct IHseq_calc_luka1 as [q1 [IH11 IH12]]. 
  destruct IHseq_calc_luka2 as [q2 [IH21 IH22]].
  rewrite in_mset1D in IH11. rewrite in_mset1D in IH21.
  move/orP: IH11. move/orP: IH21.
  move => [/eqP h1 | h1]; move => [/eqP h2 | h2].
  + subst. rewrite //= in IH12. 
    rewrite //= in IH22.
    have IH := lerD IH12 IH22.
    (*have helper : (A' + B' <= C' + D') -> (A' + B' - D' <= C').  {
      lra. }
    apply helper in IH. move: helper. move => _. *)
    exists (A `+` B |- C `+` D).
    rewrite in_mset1D eq_refl orTb//=. split. by [].
    
    admit.

  + exists q1. 
    by rewrite !in_msetD h2 IH12 orbT//=. 
  + exists q2. 
    by rewrite in_msetD h1 IH22 orbT//=. 
  + exists q1. 
    by rewrite !in_msetD h2 IH12 orbT//=. 
- exists (ldl_bool def false +` A |- [mset b]).
  rewrite in_mset1D eq_refl orTb. split. by [].
  rewrite //= eval_luka_add_el//= addr0.
  have hA := eval_luka1 A.
  have hb := eval_luka1 ([mset b]).
  set (a := eval_luka A) in *. rewrite /eval_luka//=.
  (*easy to see, but need to figure out two things: get size of [mset _]
    and figure out how \sum and mset interact, they should trivially evaluate*)
  admit.
- exists (A |- [mset ldl_bool def true]).
  rewrite in_mset1D eq_refl orTb. split. by []. 
  rewrite//=.
  have hA := eval_luka1 A.
  set (a := eval_luka A) in *. rewrite /eval_luka//=.
  (*exact same issue as above*)
admit.
(*andL_l*)
- destruct IHseq_calc_luka1 as [q1 [IH11 IH12]].
  destruct IHseq_calc_luka2 as [q2 [IH21 IH22]].
   rewrite in_mset1D in IH21.  rewrite in_mset1D in IH11.
   move/orP: IH21.
   move/orP: IH11.
   move => [/eqP h2 | h2]; move => [/eqP h1 | h1].
  + subst. 
    exists (a `/\ b +` B |- A). rewrite //= in IH22. 
    rewrite eval_luka_add_el//= in IH22.
    rewrite in_mset1D eq_refl orTb//=. split. by []. 
    rewrite addr0 in IH22.
    rewrite //= in IH12.
    have eval_1 : eval_luka ([mset a; b] `+` B) 
                  = eval_luka B + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz - 2. { admit.}
    rewrite eval_1 in IH12.
    rewrite eval_luka_add_el.
    have h := translate_Bool_T_01 Lukasiewicz (a `/\ b).
    have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
    apply le_double in h. destruct h as [ab0 ab1].
    rewrite//=/sumR big_cons big_seq1 /maxr.
    case: ifP; move => h_max.
    * rewrite addr0. by apply IH22.
    * rewrite addrA.
      have hh : (eval_luka B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E - 1 = 
                 eval_luka B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R. {
        set (e := eval_luka B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R) in *.
        lra.
        }
      by rewrite hh !addrA IH12.
  + exists q2. 
    by rewrite !in_mset1D h1 IH22 orbT//=. 
  + exists q1. 
    by rewrite !in_msetD h2 IH12 orbT//=. 
  + exists q1. 
    by rewrite !in_msetD h2 IH12 orbT//=. 
- destruct IHseq_calc_luka as [q [IH1 IH2]].
  rewrite in_msetD in_mset2 in IH1. move/orP: IH1.
  move => [/orP h | h].
  + move: h. move => [/eqP h | /eqP h]; exists (A |- a `/\ b +` B);
                     rewrite in_mset1D eq_refl orTb; split; rewrite//=.
    * subst. rewrite //= in IH2.
(*same helper as previous case, consider moving outside*)
      have eval_1 : eval_luka ([mset a; b] `+` B) 
                  = eval_luka B + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz - 2. { admit.}
      rewrite eval_1 in IH2.
      rewrite eval_luka_add_el.
      have h := translate_Bool_T_01 Lukasiewicz (a `/\ b).
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
        have hh : eval_luka A <= (eval_luka B + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2 ->
                  ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 < 0 ->
                  eval_luka A <= eval_luka B -1. {lra.}
        by  rewrite (hh IH2 h_max).
      + rewrite //= in h_max.
        * have hh : 
             (eval_luka B + ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R))%E - 1 = 
              eval_luka B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R. {lra.}
          rewrite hh.
          by rewrite !addrA IH2.
    * subst. rewrite //= in IH2.
      rewrite eval_luka_add_el.
      rewrite eval_luka_add_el//= addr0 in IH2.
      have h := translate_Bool_T_01 Lukasiewicz (a `/\ b).
      have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
      apply le_double in h. destruct h as [ab0 ab1].
      lra.      
  + exists q. 
    by rewrite !in_msetD h IH2 orbT//=. 
(* (*old conjunction cases, these do not hold, discard later*)
-  destruct IHseq_calc_luka as [q1 [IH1 IH2]]. 
   rewrite in_msetD in IH1. move/orP : IH1.
  move => [h1 | h2]; first last.
  + exists q1. rewrite in_msetD h2 orbT.
    split; rewrite//=. 
  + rewrite in_mset1 in h1. move/eqP : h1.
    move => h1. 
    subst. rewrite//= in IH2.
    rewrite eval_luka_add_el in IH2.
    exists (a `/\ b +` B |- A).
    rewrite in_mset1D eq_refl orTb//=. split. by [].
    rewrite eval_luka_add_el.
    have ab01 := translate_Bool_T_01 Lukasiewicz (a `/\ b).
    have a01 := translate_Bool_T_01 Lukasiewicz (a).
    have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
    apply le_double in a01. destruct a01 as [a0 a1].
    apply le_double in ab01. destruct ab01 as [ab0 ab1].
    (*have le_add_ge0 : forall (a b c : R), a + b  <= c -> b >= 0 -> a  <= c. { intros. lra.} 
    apply le_add_ge0 in IH2; first last. by apply a0. *)
    have le_add_le : forall (a b c d : R), a + d <= c -> b <= d -> a + b <= c. { intros. lra.}
    have add_luka : forall a b, [[a `/\ b]]_ Lukasiewicz <= [[a]]_ Lukasiewicz. {
      intros. rewrite//=/sumR big_cons big_seq1 /maxr.
      case: ifP.
      * admit.
      * admit.
    }
    apply (le_add_le _ _ _ ([[a]]_Lukasiewicz)).
    * by apply IH2.
    * by apply add_luka.
-  destruct IHseq_calc_luka as [q1 [IH1 IH2]]. 
   rewrite in_msetD in IH1. move/orP : IH1.
  move => [h1 | h2]; first last.
  + exists q1. rewrite in_msetD h2 orbT.
    split; rewrite//=. 
  + rewrite in_mset1 in h1. move/eqP : h1.
    move => h1. 
    subst. rewrite//= in IH2.
    rewrite eval_luka_add_el in IH2.
    exists (a `/\ b +` B |- A).
    rewrite in_mset1D eq_refl orTb//=. split. by [].
    rewrite eval_luka_add_el.
    have ab01 := translate_Bool_T_01 Lukasiewicz (a `/\ b).
    have b01 := translate_Bool_T_01 Lukasiewicz (b).
    have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
    apply le_double in b01. destruct b01 as [b0 b1].
    apply le_double in ab01. destruct ab01 as [ab0 ab1].
    (*have le_add_ge0 : forall (a b c : R), a + b  <= c -> b >= 0 -> a  <= c. { intros. lra.} 
    apply le_add_ge0 in IH2; first last. by apply a0. *)
    have le_add_le : forall (a b c d : R), a + d <= c -> b <= d -> a + b <= c. { intros. lra.}
    have add_luka : forall a b, [[a `/\ b]]_ Lukasiewicz <= [[b]]_ Lukasiewicz. {
      intros. rewrite//=/sumR big_cons big_seq1 /maxr.
      case: ifP.
      * admit.
      * admit.
    }
    apply (le_add_le _ _ _ ([[b]]_Lukasiewicz)).
    * by apply IH2.
    * by apply add_luka.
- destruct IHseq_calc_luka1 as [q1 [IH11 IH12]]. 
  destruct IHseq_calc_luka2 as [q2 [IH21 IH22]].
  rewrite in_mset1D in IH11. rewrite in_mset1D in IH21.
  move/orP: IH11. move/orP: IH21.
  move => [/eqP h1 | h1]; first last.
  + exists q2. rewrite in_msetD h1 orbT.
    by split; rewrite//=. 
  + move => [/eqP h2 | h2]; first last.
    * exists q1. rewrite in_msetD h2 orbT.
      by split; rewrite//=.
    * subst. rewrite //= in IH12. 
      rewrite //= in IH22.
      exists (A |- a `/\ b +` B).
      rewrite in_mset1D eq_refl orTb.
      split. by [].
      rewrite//=. 
      rewrite eval_luka_add_el/eval_luka. 
      rewrite !eval_luka_add_el/eval_luka in IH12 IH22.
      set (A' := (1%R + (size A)%:R)%E - \sum_(i <- [seq [[i]]_Lukasiewicz | i <- A]) i) in *.
      set (B' := ((1%R + (size B)%:R)%E - \sum_(i <- [seq [[i]]_Lukasiewicz | i <- B]) i)) in *.
      have h :=*)
Admitted.


Definition eval_luka'  (Q : seq (@expr R Bool_T_def))
  := 1%R (*- (size  Q)%:R*) + (\sum_(i <- Q) ([[i]]_Lukasiewicz - 1%R)).

Lemma eval_luka_add_el' (Q : seq (@expr R Bool_T_def)) (q : (@expr R Bool_T_def)) :
  eval_luka' (q :: Q) = eval_luka' Q + [[q]]_Lukasiewicz  - 1.
Proof.
rewrite /eval_luka'//=. rewrite big_cons//=. 
lra.
Qed.

(*testing a sequence version because I am loosing my patience rapidly*)

Inductive seq_calc_luka' :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))
(*-> {mset (seq {mset (@expr R Bool_T_def)})}*)
      -> Prop :=
| id_l' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                (A : seq (@expr R Bool_T_def)),
    seq_calc_luka' ( (A |- A) :: Q)
| empty' : forall (Q :  seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka' (([::] |- [::]) :: Q)
(*structural*)
| ew_l' : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka' Q ->
    seq_calc_luka' (Q ++ P) 
| ec_l' : forall (Q P : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))),
    seq_calc_luka' (Q ++ P ++ P) ->
    seq_calc_luka' (Q ++ P)
(*add split and mix rules*)
| split_l' : forall (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def)))
                  (A B C D: seq (@expr R Bool_T_def)),
    seq_calc_luka' (((A ++ B) |- (C ++ D)) :: Q) ->
    seq_calc_luka' ((A |- C) ::  (B |- D) :: Q)
(*| mix_l : forall Q 
                  (A B C D: {mset (@expr R Bool_T_def)}),
    seq_calc_luka ((A |- C) +` Q) ->
    seq_calc_luka ((B |- D) +` Q) ->
    seq_calc_luka (((A `+` B) |- (C `+` D)) +` Q)*)
(*logical*)
(*both are restricted to a single-conclusion case for Lukasiewicz*)
| bot_l' : forall Q 
                 (A : {mset (@expr R Bool_T_def)})
                 (b : @expr R Bool_T_def),
    seq_calc_luka' (((ldl_bool def false :: A) |- [:: b]) :: Q)
(*| top_l : forall Q 
                 (A : {mset (@expr R Bool_T_def)}),
    seq_calc_luka ((A |- [mset (ldl_bool def true)]) +` Q)*)
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
    seq_calc_luka'  ((A |- (a ::  b :: B)) :: (A |- (ldl_bool def false :: B)) :: Q)  ->
    seq_calc_luka' ((A |- (a `/\ b) :: B) :: Q )
.

Lemma big_sum_cat [T : Type] (X Y : seq (@expr R Bool_T_def) ):
 (\sum_(i <- (X ++ Y)) ([[i]]_Lukasiewicz -1 )) = 
    (\sum_(i <- X) ([[i]]_Lukasiewicz -1)) + (\sum_(i <- Y) ([[i]]_Lukasiewicz -1)).
Proof.

Admitted.

Lemma eval_luka1' (Q : seq (@expr R Bool_T_def)):
  eval_luka' Q <= 1.
Proof.
rewrite /eval_luka'.
have helper : forall (a : R), a<= 0 -> 1 + a <= 1. {intros. lra.}.
rewrite helper//=. 
rewrite sumr_le0//=. move => i _.
have h := translate_Bool_T_01 Lukasiewicz (i).
have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
apply le_double in h. destruct h as [_ i1].
lra.
Qed.


Lemma sound_luka_' (Q : seq ( seq (@expr R Bool_T_def) * seq (@expr R Bool_T_def))):
seq_calc_luka' Q -> 
exists (q : ( seq (@expr R Bool_T_def) * seq (@expr R
 Bool_T_def))), q \in Q 
/\ 
       (

         eval_luka' (fst q) <= eval_luka' (snd q)

       ).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite //= mem_head. split. by [].  
  simpl. by lra.
- exists ([::] |- [::]). 
  rewrite mem_head.  split. by []. 
  rewrite /eval_luka'//=.
- destruct IHseq_calc_luka' as [q [IH1 IH2]].
  exists q. rewrite mem_cat IH1 orTb.
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_luka' as [M [IH1 IH2]].   
  exists M. rewrite !mem_cat in IH1. 
  rewrite mem_cat. move/orP : IH1. 
  move => [h |/orP h].  rewrite h ?orbT; split; rewrite//=. 
  move: h. move => [h | h]; rewrite h ?orbT; split; rewrite//=.
- destruct IHseq_calc_luka' as [q1 [IH1 IH2]]. 
  rewrite in_cons in IH1. move/orP : IH1.
  move => [h1 | h2]; first last.
  + exists q1. rewrite !in_cons h2 !orbT.
    split; rewrite//=. 
  + move/eqP : h1.
    move => h1. 
    subst.
    rewrite /eval_luka'//= in IH2.
    rewrite !big_sum_cat//= in IH2.
    have helper : 
      (1%R + ((\sum_(i <- A) ([[i]]_Lukasiewicz - 1))%R + (\sum_(i <- B) ([[i]]_Lukasiewicz - 1))%R))%E <=
    (1%R + ((\sum_(i <- C) ([[i]]_Lukasiewicz - 1))%R + (\sum_(i <- D) ([[i]]_Lukasiewicz - 1))%R))%E ->
      (1%R + ((\sum_(i <- A) ([[i]]_Lukasiewicz - 1))%R + (\sum_(i <- B) ([[i]]_Lukasiewicz - 1))%R))%E 
       - (\sum_(i <- D) ([[i]]_Lukasiewicz - 1))%R<=
    (1%R + ((\sum_(i <- C) ([[i]]_Lukasiewicz - 1))%R))%E. {
      set (A' := (\sum_(i <- A) ([[i]]_Lukasiewicz - 1))) in *.
    set (B' := (\sum_(i <- B) ([[i]]_Lukasiewicz - 1))) in *.
    set (C' := (\sum_(i <- C) ([[i]]_Lukasiewicz - 1))) in *.
    set (D' := (\sum_(i <- D) ([[i]]_Lukasiewicz - 1))) in *.
    intros. 
    lra. }
    apply helper in IH2. move: helper. move =>_.
    rewrite !addrA in IH2. 
    set (A' := (\sum_(i <- A) ([[i]]_Lukasiewicz - 1))) in *.
    set (B' := (\sum_(i <- B) ([[i]]_Lukasiewicz - 1))) in *.
    set (C' := (\sum_(i <- C) ([[i]]_Lukasiewicz - 1))) in *.
    set (D' := (\sum_(i <- D) ([[i]]_Lukasiewicz - 1))) in *.
    have h1 := le_or (1 + B') (1 + D').
    destruct h1 as [h1 | h1].
    * exists (B |- D). split. 
      - by rewrite !in_cons eq_refl !orbT. 
      - by rewrite  //=/eval_luka'.
    * exists (A |- C). split. 
      - by rewrite !in_cons eq_refl !orTb. 
      - rewrite  //=/eval_luka'.
        have helper : 1 + D' <= 1 + B' -> (B' - D' >= 0). {
        lra.}
      apply helper in h1.
      have helper2 : 0 <= B' - D' ->
        1 + A' + B' - D' <= 1+ C' ->
        1 + A'  <= 1 + C'. {
        intros. lra.} 
      by rewrite (helper2 h1 IH2).
(*- admit. commented out for now*)
- exists (ldl_bool def false :: A |- [:: b]).
  rewrite mem_head. split. by [].
  rewrite //= !eval_luka_add_el' addr0.
  have h := eval_luka1' A.
  have hb := translate_Bool_T_01 Lukasiewicz (b).
  have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
  apply le_double in hb. destruct hb as [b0 b1].
  have helper : 0 <= (eval_luka' [::] + [[b]]_Lukasiewicz)%E - 1 ->
                eval_luka' A - 1 <= (eval_luka' [::] + [[b]]_Lukasiewicz)%E - 1. {
    intros. lra. }
  apply helper. rewrite /eval_luka'//= big_nil addr0.
  lra.
(*- exists (A |- [mset ldl_bool def true]).
  rewrite in_mset1D eq_refl orTb. split. by []. 
  rewrite//=.
  have hA := eval_luka1 A.
  set (a := eval_luka A) in *. rewrite /eval_luka//=.
  (*exact same issue as above*)
admit.*)
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
    have eval_1 : eval_luka' [:: a, b & B] 
                  = eval_luka' B + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz - 2. { admit.}
    rewrite eval_1 in IH12.
    rewrite eval_luka_add_el'.
    have h := translate_Bool_T_01 Lukasiewicz (a `/\ b).
    have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
    apply le_double in h. destruct h as [ab0 ab1].
    rewrite//=/sumR big_cons big_seq1 /maxr.
    case: ifP; move => h_max.
    * rewrite addr0. by apply IH22.
    * rewrite addrA.
      have hh : (eval_luka' B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R)%E - 1 = 
                 eval_luka' B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R. {
        set (e := eval_luka' B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R) in *.
        lra.
        }
      by rewrite hh !addrA IH12.
  + exists q2. 
    by rewrite in_cons h1 IH22 orbT//=. 
  + exists q1. 
    by rewrite in_cons h2 IH12 orbT//=. 
  + exists q1. 
    by rewrite in_cons h2 IH12 orbT//=. 
- destruct IHseq_calc_luka' as [q [IH1 IH2]].
  rewrite in_cons in_cons in IH1. move/orP: IH1.
  move => [/eqP h |/orP [/eqP h | h]].
  +  exists (A |- a `/\ b :: B);
                     rewrite mem_head; split; rewrite//=.
    * subst. rewrite //= in IH2.
(*same helper as previous case, consider moving outside*)
      have eval_1 : eval_luka' [:: a, b & B] 
                  = eval_luka' B + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz - 2. { admit.}
      rewrite eval_1 in IH2.
      rewrite eval_luka_add_el'.
      have h := translate_Bool_T_01 Lukasiewicz (a `/\ b).
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
        have hh : eval_luka' A <= (eval_luka' B + [[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2 ->
                  ([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 1 < 0 ->
                  eval_luka' A <= eval_luka' B -1. {lra.}
        by  rewrite (hh IH2 h_max).
      + rewrite //= in h_max.
        * have hh : 
             (eval_luka' B + ((([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R + 1%R))%E - 1 = 
              eval_luka' B + (([[a]]_Lukasiewicz + [[b]]_Lukasiewicz)%E - 2)%R. {lra.}
          rewrite hh.
          by rewrite !addrA IH2.
    * exists (A |- a `/\ b :: B);
                     rewrite mem_head; split; rewrite//=.
      subst. rewrite //= in IH2.
      rewrite eval_luka_add_el'.
      rewrite eval_luka_add_el'//= addr0 in IH2.
      have h := translate_Bool_T_01 Lukasiewicz (a `/\ b).
      have le_double : forall (a b c : R), a <= b <= c -> a <= b /\ b <= c. { intros. lra.}
      apply le_double in h. destruct h as [ab0 ab1].
      lra.      
  + exists q. 
    by rewrite in_cons h orbT IH2.

Admitted.


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

Inductive seq_calc_product :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}
      -> Prop :=
| id_p : forall (Q :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})})
                (A : {mset (@expr R Bool_T_def)}),
    seq_calc_product ( (A |- A) +` Q)
| empty_p : forall (Q :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
     seq_calc_product ((mset0 |- mset0) +` Q)
(*structural*)
| ew_p : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_product Q ->
    seq_calc_product (Q `+` P)
| ec_p : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_product (Q `+` P `+` P) ->
    seq_calc_product (Q `+` P)
(*add split and mix rules*)
| split_p : forall Q 
                  (A B C D: {mset (@expr R Bool_T_def)}),
    seq_calc_product (((A `+` B) |- (C `+` D)) +` Q) ->
    seq_calc_product ([mset (A |- C)] `+` [mset (B |- D)] `+` Q)
| mix_p : forall Q 
                  (A B C D: {mset (@expr R Bool_T_def)}),
    seq_calc_product ((A |- C) +` Q) ->
    seq_calc_product ((B |- D) +` Q) ->
    seq_calc_product (((A `+` B) |- (C `+` D)) +` Q)
(*logical*)
| bot_p : forall Q 
                 (A B : {mset (@expr R Bool_T_def)}),
    seq_calc_product (((ldl_bool def false +` A) |- B) +` Q)
| top_p : forall Q 
                 (A : {mset (@expr R Bool_T_def)}),
    seq_calc_product ((A |- [mset (ldl_bool def true)]) +` Q )
| andL_p1 : forall Q 
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_product (((a +` B) |- A) +` Q ) ->
    seq_calc_product ((((a `/\ b) +` B) |- A) +` Q) 
| andL_p2 : forall Q
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_product (((b +` B) |- A) +` Q ) ->
    seq_calc_product ((((a `/\ b) +` B) |- A) +` Q )
| andR_p : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_product ( (A |- [mset a]) +` Q ) ->
    seq_calc_product ( (B |- [mset b]) +` Q) ->
    seq_calc_product ((A |- [mset (a `/\ b)]) +` Q )
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

Lemma sum_in_msetD_expr_product (A B : {mset (@expr R Bool_T_def)}):
    (\sum_(i <- [seq [[i]]_product | i <- A `+` B]) i) = 
      (\sum_(i <- [seq [[i]]_product | i <- A]) i)%R + (\sum_(i <- [seq [[i]]_product | i <- B]) i)%R.
Proof.
Admitted.

Definition eval_product  (Q : {mset (@expr R Bool_T_def)})
  := (\prod_(i <- [seq [[i]]_product | i <- Q]) i).

Lemma sound_product (Q : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}):
seq_calc_product Q -> 
exists (q : ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})), 
  q \in Q  /\  (eval_product (fst q) <= eval_product (snd q)).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite in_mset1D eq_refl orTb. split. by [].  
  simpl. by lra.
- exists (mset0 |- mset0). 
  rewrite in_mset1D eq_refl orTb. split. by []. 
  rewrite /eval_luka//=.
- destruct IHseq_calc_product as [q [IH1 IH2]].
  exists q. rewrite in_msetD IH1 orTb. 
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_product as [M [IH1 IH2]].   
  exists M. rewrite !in_msetD in IH1. 
  rewrite in_msetD. move/orP : IH1. 
  by move => [h | h]; rewrite h ?orbT; split; rewrite//=. 
- destruct IHseq_calc_product as [q [IH1 IH2]]. 
  rewrite in_msetD in IH1. move/orP : IH1.
  move => [h1 | h2]; first last.
  + exists q. rewrite in_msetD h2 orbT.
    split; rewrite//=. 
  + rewrite in_mset1 in h1. move/eqP : h1.
    move => h1. 
    subst.
    rewrite /eval_product//= in IH2.
    exists (A |- C).
    rewrite in_msetD in_mset2 eq_refl !orTb. split. by [].
    rewrite /eval_luka//=/sumR.
    rewrite /sumR !sum_in_msetD_expr_Luka in IH2.
    set (A' := \sum_(i <- [seq [[i]]_Lukasiewicz | i <- A]) i) in *.
    set (B' := \sum_(i <- [seq [[i]]_Lukasiewicz | i <- B]) i) in *.
    set (C' := \sum_(i <- [seq [[i]]_Lukasiewicz | i <- C]) i) in *.
    set (D' := \sum_(i <- [seq [[i]]_Lukasiewicz | i <- D]) i) in *.

Admitted.

End hypersequent_product.
