From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder finmap multiset.
Require Import mathcomp_extra analysis_extra ldl stl_infty.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory Order.TTheory.
Import numFieldTopology.Exports.

Section stl_hypersequent_calc.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Context {K : choiceType}.
Implicit Types (s : seq K).
Local Notation "[[ e ]]_stli" := (@stl_infty_translation R _ e).

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).
(*entailment as pair (A, B) where A |- B*)

Let formula := @expr R (boolT_def impl_def m_def l_def).
Let hypersequent := seq (seq formula * seq formula).

Implicit Type Q P S : hypersequent.
Implicit Type A B C D X Y : seq formula.


Inductive seq_calc_stli : hypersequent -> Prop :=
| id_stli : forall Q (a : formula),
    seq_calc_stli ( ([::a] |- [::a]) :: Q)
(*structural*)
| eex_stli : forall Q P S1 S2,
    seq_calc_stli (S1 ++ P ++ Q ++ S2) ->
    seq_calc_stli (S1 ++ Q ++ P ++ S2)
| ew_stli : forall Q P,
    seq_calc_stli Q ->
    seq_calc_stli (Q ++ P)
| ec_stli : forall Q P,
    seq_calc_stli (Q ++ P ++ P) ->
    seq_calc_stli (Q ++ P)
| comm_hyper_stli : forall Q A1 A2 B1 B2 C D,
    seq_calc_stli (((A1 ++ B1) |- C) :: Q) ->
    seq_calc_stli (((A2 ++ B2) |- D) :: Q) ->
    seq_calc_stli ( ((A1 ++ A2) |- C) :: ((B1 ++ B2) |- D) :: Q)
| comm_stli : forall Q A B C,
    seq_calc_stli (((A ++ B ++ B) |- C) :: Q) ->
    seq_calc_stli (((A ++ B) |- C) :: Q)
| weak_stli : forall Q A B C,
    seq_calc_stli ((A |- C) :: Q ) ->
    seq_calc_stli (((A ++ B) |- C) :: Q )
| exL_stli : forall Q A B C X Y,
    seq_calc_stli (((X ++ A ++ B ++ Y) |- C) :: Q) ->
    seq_calc_stli (((X ++ B ++ A ++ Y) |- C) :: Q)
| exR_stli : forall Q A B C X Y,
    seq_calc_stli ((C |- (X ++ A ++ B ++ Y)) :: Q) ->
    seq_calc_stli ((C |- (X ++ B ++ A ++ Y)) :: Q)
(*logical*)
| bot_stli : forall Q A B,
    seq_calc_stli (((ldl_bool _ _ _ _ false :: A) |- B) :: Q)
| top_stli : forall Q A B,
    seq_calc_stli ((A |- (ldl_bool _ _ _ _ true) :: B) :: Q )
| andL_stli : forall Q A B (a b : formula),
    seq_calc_stli (((a :: B) |- A) :: ((b :: B) |- A):: Q ) ->
    seq_calc_stli ((((a `/\ b) :: B) |- A) :: Q)
| andR_stli : forall Q A B (a b : formula),
    seq_calc_stli ( (A |- a :: B) :: Q ) ->
    seq_calc_stli ( (A |- b :: B) :: Q) ->
    seq_calc_stli ((A |- (a `/\ b) :: B) :: Q )
| orL_stli : forall  Q A B (a b : formula),
    seq_calc_stli ( ((b :: B) |- A) :: Q) ->
    seq_calc_stli ( ((a :: B) |- A) :: Q) ->
    seq_calc_stli (((a `\/ b) :: B |- A) :: Q)
| orR_stli : forall Q A B (a b : formula),
    seq_calc_stli ((A |- a :: B ) :: ( A |- b :: B) :: Q ) ->
    seq_calc_stli ((A |- (a `\/ b) :: B ) :: Q)
| negR_stli : forall Q A (a : formula),
    seq_calc_stli ((a :: A |- [::(ldl_bool _ _ _ _ false)]) :: Q) ->
    seq_calc_stli ((A |- [:: (`~ a)]) :: Q)
| negL_stli : forall Q A B (a : formula),
    seq_calc_stli ((A |- a :: B) :: Q) ->
    seq_calc_stli (((`~ a) :: A |- B) :: Q)
| implR_stli : forall Q A B (a b : formula),
    seq_calc_stli ((a :: A |- b :: B) :: Q) ->
    seq_calc_stli ((A |- (a `=> b) :: B) :: Q)
| implL_stli : forall Q A1 A2 B (a b: formula),
    seq_calc_stli ((A1 |- [:: a]) :: Q) ->
    seq_calc_stli ((b :: A2 |- B) :: Q) ->
    seq_calc_stli (( (a `=> b) :: A1 ++ A2 |- B) :: Q).



Lemma big_min_cat A B :
  \big[mine/+oo]_(j <- A ++ B) [[j]]_stli =
  mine (\big[mine/+oo]_(j <- A) [[j]]_stli) (\big[mine/+oo]_(j <- B) [[j]]_stli).
Proof.
elim: A => [|x xs IH].
- rewrite /= big_nil//= {2}/mine; case: ifP; intros; rewrite//=.
  case: B i. rewrite big_nil//=. 
  move => a l IH. rewrite ltNge leey in IH; rewrite//=. 
- simpl; rewrite !big_cons -minA; f_equal.
  by exact: IH.
Qed.

Lemma big_max_cat A B:
  \big[maxe/-oo]_(j <- A ++ B) [[j]]_stli =
  maxe (\big[maxe/-oo]_(j <- A) [[j]]_stli) (\big[maxe/-oo]_(j <- B) [[j]]_stli).
Proof.
elim: A => [|x xs IH].
- rewrite /= big_nil//= {2}/maxe; case: ifP; intros; rewrite//=. 
  case: B n. rewrite big_nil//=. 
  move => a l /negP/negP IH. rewrite ltNye negbK in IH. move/eqP in IH; rewrite//=.
- simpl; rewrite !big_cons -maxA; f_equal.
  by exact IH.
Qed.

Lemma mine_gexy (a b c : \bar R):
  a <= b -> mine a c <= mine b c.
Proof.
move => H. rewrite /mine. repeat case: ifPn; rewrite//=.
-  move => _ /ltW h2; by [].
- move => /ltW h1 h2. 
  rewrite  ltNge Bool.negb_involutive in h2.
  by rewrite (le_trans h2 H).
Qed. 

Lemma maxe_gexy (a b c : \bar R):
  a <= b -> maxe a c <= maxe b c.
Proof.
move => H. rewrite /maxe. repeat case: ifPn; rewrite//=.
- move => h1 /ltW h2. by rewrite ltNge Bool.negb_involutive in h1.
- move => /ltW h1 _. 
  by rewrite (le_trans H h1).
Qed. 

Lemma sound_stli Q:
  seq_calc_stli Q ->
  exists2 q : seq formula * seq formula, q \in Q &
(\big[mine/+oo]_(i <- (map stl_infty_translation (fst q))) i  <=
   \big[maxe/-oo]_(i <- (map stl_infty_translation (snd q))) i).
Proof.
intros; rewrite//=. dependent induction H.
- exists ([:: a] |- [:: a]); first by rewrite //= mem_head.
  by rewrite !big_cons !big_nil miney maxeNy. 
- case: IHseq_calc_stli => [M].
  rewrite !mem_cat => IH1 IH2.
  exists M => //.
  rewrite !mem_cat.
  move/orP: IH1 => [->// |/orP].
  case => [-> |]; first by rewrite !orbT.
  by move/orP => [|] ->; rewrite ?(orTb,orbT).
- case: IHseq_calc_stli => [q IH1 IH2].
  by exists q => //; rewrite mem_cat IH1 orTb.
- case IHseq_calc_stli => [M + IH2].
  rewrite !mem_cat => /orP [h |/orP [h | h]]; exists M => //;
            by rewrite mem_cat h ?orbT; split; rewrite//=.
- case IHseq_calc_stli1 => [q1].
  case IHseq_calc_stli2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + subst.
    rewrite //= !big_map !big_min_cat in IH12 IH22.
    rewrite //=. 
    (*have := le_total_ereal (\big[mine/+oo]_(j <- A2) [[j ]]_stli) (\big[mine/+oo]_(j <- B1) [[j ]]_stli).*)
    (*rewrite {1}/mine in IH12; move: IH12; case: ifP => h1 h2;
    rewrite {1}/mine in IH22; move: IH22; case: ifP => h3 h4.*) (*need a smarter solution to this, 
Godel brute forced it with lra*)

    (*move => /orP [HAB | HAB].
    * exists (A1 ++ A2 |- C); subst; first by rewrite in_cons eq_refl orTb.
      rewrite//= !big_map !big_min_cat. 
      apply (leeD2l (\big[mine/+oo]_(j <- A1) [[j ]]_stli)) in HAB.*) (*no, need minimums.*)
 admit.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite in_cons => /predU1P[ | IH1].
  + exists (A ++ B |- C); subst; first by rewrite in_cons eq_refl orTb. 
    move: IH2.
    rewrite //= /minR !big_map.
    suff : \big[mine/+oo]_(j <- A ++ B ++ B) [[j]]_stli =
           \big[mine/+oo]_(j <- A ++ B) [[j]]_stli by move=> ->.
    rewrite !big_min_cat {1}/mine {2}/mine {7}/mine {11}/mine; repeat case: ifP; rewrite//=.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (A ++ B |- C); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= !big_map.
    rewrite //= !big_map in IH2.
    have := le_total_ereal (\big[mine/+oo]_(j <- A) [[j ]]_stli) (\big[mine/+oo]_(j <- B) [[j ]]_stli).
    move => /orP [h|h]; rewrite !big_min_cat {1}/mine; case: ifPn; rewrite//=.
    -  rewrite ltNge. move => /negPn h'. by rewrite (le_trans h' IH2).
    -  rewrite ltNge. move => /negPn h'. by rewrite (le_trans h' IH2).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (X ++ B ++ A ++ Y |- C); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= !big_map !big_min_cat.
    rewrite //= !big_map !big_min_cat in IH2.
    rewrite (mineA (\big[mine/+oo]_(j <- A) [[j ]]_stli)) in IH2.
    rewrite (mineC (\big[mine/+oo]_(j <- A) [[j ]]_stli)) in IH2.
    by rewrite (mineA (\big[mine/+oo]_(j <- B) [[j ]]_stli))//=.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (C |- X ++ B ++ A ++ Y); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= !big_map !big_max_cat.
    rewrite //= !big_map !big_max_cat in IH2.
    rewrite (maxA (\big[maxe/-oo]_(j <- A) [[j ]]_stli)) in IH2.
    rewrite (maxC (\big[maxe/-oo]_(j <- A) [[j ]]_stli)) in IH2.
    by rewrite (maxA (\big[maxe/-oo]_(j <- B) [[j ]]_stli))//=.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- exists (ldl_bool _ _ _ _ false :: A |- B); first by rewrite in_cons eq_refl orTb.
  by rewrite /minR/maxR//= !big_cons !big_map ge_min leNye orTb.
- exists (A |- ldl_bool neg_def impl_def m_def l_def true :: B); first by rewrite in_cons eq_refl orTb.
  by rewrite //= !big_cons !big_map maxye leey. 
- move: IHseq_calc_stli => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + exists ((a `/\ b) :: B |- A); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= !big_cons big_nil !big_map miney.
    rewrite //= !big_cons !big_map in IH2.
    rewrite {2}/mine; case: ifP; rewrite//=.
    move => /negP/negP h. rewrite  ltNge Bool.negb_involutive in h. 
    apply (mine_gexy  (\big[mine/+oo]_(j <- B) [[j ]]_stli)) in h.
    by rewrite (le_trans h IH2).
  + move/predU1P : IH1 => [|IH1].
    exists ((a `/\ b) :: B |- A); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= !big_cons big_nil !big_map miney.
    rewrite //= !big_cons !big_map in IH2.
    rewrite {2}/mine; case: ifP; rewrite//=.
    move => /ltW h.
     apply (mine_gexy (\big[mine/+oo]_(j <- B) [[j ]]_stli)) in h.
    by rewrite (le_trans h IH2).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- case IHseq_calc_stli1 => [q1].
  case IHseq_calc_stli2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + subst.
    exists (A |- (a `/\ b) :: B); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //=!big_map big_cons in IH12.
    rewrite //= !big_map big_cons in IH22.
    rewrite //=!big_map !big_cons big_nil miney.
    rewrite {2}/mine. case: ifP; rewrite//=.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case IHseq_calc_stli1 => [q1].
  case IHseq_calc_stli2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + subst.
    exists ((a `\/ b) :: B |- A); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //=!big_map big_cons in IH12.
    rewrite //= !big_map big_cons in IH22.
    rewrite //=!big_map !big_cons big_nil maxeNy.
    rewrite {1}/maxe. case: ifP; rewrite//=.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + exists (A |- (a `\/ b) :: B); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //=!big_map big_cons in IH2.
    rewrite //=!big_map !big_cons big_nil maxeNy.
    rewrite {2}/maxe. case: ifP; rewrite//=.
    move => /ltW h. 
    apply (maxe_gexy (\big[maxe/-oo]_(j <- [seq [[i ]]_stli | i <- B]) j)) in h.
    by rewrite (le_trans IH2 h).
  + move/predU1P : IH1 => [|IH1].
    exists (A |- (a `\/ b) :: B); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //=!big_map big_cons in IH2.
    rewrite //=!big_map !big_cons big_nil maxeNy.
    rewrite {2}/maxe. case: ifP; rewrite//=.
    move => /negP/negP h. rewrite  ltNge Bool.negb_involutive in h.
    apply (maxe_gexy (\big[maxe/-oo]_(j <- [seq [[i ]]_stli | i <- B]) j)) in h.
    by rewrite (le_trans IH2 h).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + exists (A |- [:: (`~ a)]); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= !big_cons big_nil maxNye in IH2.
    rewrite leeNy_eq {1}/mine in IH2; move/eqP in IH2.
    rewrite //=!big_map !big_cons big_nil maxeNy. 
    move: IH2.
   (* repeat case: ifP; rewrite !big_map //=.
     move => h ha. rewrite ha in h. 
      rewrite ltNye in h. move/eqP in IH; rewrite//=.
      (*rewrite leeNr.*)
    * move => /ltW h1 /ltW h2 h3. 
      admit. (*the mult by -1*)
    * move => /negP/negP h1 /ltW h2 h3.
      rewrite !ltNge !Bool.negb_involutive//= in h1.
    admit. admit.
  + by exists q => //; rewrite !in_cons IH1 !orbT.*) (*rule wrong theoretically, go back*) admit. admit.
- move: IHseq_calc_stli => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + subst.
    exists ((`~ a) :: A |- B); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //=!big_map !big_cons {1}/maxe in IH2.
    rewrite //=!big_map !big_cons {1}/mine. move: IH2.
    repeat case: ifP; rewrite !big_map//=.
    * move => /ltW h1 /ltW h2 h3. 
      by rewrite (le_trans h1 h3).
    * move => /ltW h1 /negP/negP h2 h3. 
      rewrite !ltNge !Bool.negb_involutive//= in h2.
      rewrite leeNl. (*no, also rethink this rule on paper*)
      admit. (*need to multiply both sides by -1)*)
    * move => /negP/negP h1 /negP/negP h2 h3.
      rewrite !ltNge !Bool.negb_involutive//= in h1 h2.
      admit. (*but provable*)
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + exists (A |- (a `=> b) :: B); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //= !big_cons in IH2.
    rewrite //=!big_map !big_cons; repeat case: ifP.
    * (*move => /andP [ha hb]. 
      rewrite {1}/maxe; case: ifPn.
      + move => h1. rewrite {1}/mine {1}/maxe in IH2. move: IH2.
        repeat case: ifPn; rewrite//=.*)
(*actual case, come back *) admit.
    * by rewrite maxye leey.
    * admit. (*doable, midlly painful*)
    * by rewrite maxye leey.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- case IHseq_calc_stli1 => [q1].
  case IHseq_calc_stli2 => [q2].
  rewrite !in_cons //= => /orP [/eqP h2 | h2] IH12 /orP[/eqP h1 | h1] IH22.
  + subst.
    exists ((a `=> b) :: A1 ++ A2 |- B); subst; first by rewrite in_cons eq_refl orTb.
    rewrite //=!big_map big_cons in IH12.
    rewrite //= !big_map big_cons big_nil maxeNy in IH22.
    rewrite //=!big_map !big_cons.
    case: ifP; rewrite//=.
    admit. admit. admit. admit. (*double check on paper*)
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
Admitted.

End stl_hypersequent_calc.

