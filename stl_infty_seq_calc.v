From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder finmap multiset.
Require Import mathcomp_extra analysis_extra dl stl_infty.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory Order.TTheory.
Import numFieldTopology.Exports.

(**md**************************************************************************)
(* # Hypersequent calculi for STLinfty - a version of STL where               *)
(*     nu tends to infinity - using ereals                                    *)
(*                                                                            *)
(*                                                                            *)
(* - seq_calc_stli == hypersequent calculus STLinfty                          *)
(* - sound_stli == soundness of seq_calc_stli                                 *)
(*                                                                            *)
(******************************************************************************)

Section stl_hypersequent_calc.
Local Open Scope ereal_scope.
Local Open Scope dl_scope.
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
    seq_calc_stli ((dl_bool _ _ _ _ false :: A |- B) :: Q)
| top_stli : forall Q A B,
    seq_calc_stli ((A |- dl_bool _ _ _ _ true :: B) :: Q )
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
    seq_calc_stli ((a :: A |- [:: dl_bool _ _ _ _ false]) :: Q) ->
    seq_calc_stli ((A |- [:: (`~ a)]) :: Q)
| negL_stli : forall Q A B (a : formula),
    seq_calc_stli ((A |- [:: a]) :: Q) ->
    seq_calc_stli ((A |- B) :: Q) ->
    seq_calc_stli (((`~ a) :: A |- B) :: Q)
(*| negL_stli : forall Q A B (a : formula),
    seq_calc_stli ((A |- a :: B) :: Q) ->
    seq_calc_stli (((`~ a) :: A |- B) :: Q)*)
| implR_stli : forall Q A (a b : formula),
    seq_calc_stli ((a :: A |- [:: b] ) :: Q) ->
    seq_calc_stli ((A |- [:: (a `=> b)]) :: Q)
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
  rewrite -leNgt in h2.
  by rewrite (le_trans h2 H).
Qed. 

Lemma maxe_gexy (a b c : \bar R):
  a <= b -> maxe a c <= maxe b c.
Proof.
move => H. rewrite /maxe. repeat case: ifPn; rewrite//=.
- move => h1 /ltW h2. by rewrite -leNgt in h1.
- move => /ltW h1 _. 
  by rewrite (le_trans H h1).
Qed. 

Lemma neg_swap_ineq (e1 e2 : \bar R) : (- e1 <= - e2)%E = (e2 <= e1)%E.
Proof.
rewrite leeNr oppeK//=.
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
  rewrite !in_cons //= => /predU1P[h2 | h2] IH12 /predU1P[h1 | h1] IH22.
  + subst.
    rewrite /= !big_map !big_min_cat in IH12 IH22.
    have := le_total_ereal (\big[mine/+oo]_(j <- A2) [[j ]]_stli) (\big[mine/+oo]_(j <- B1) [[j ]]_stli).
    move => /orP [h | h].
    * apply (mine_gexy (\big[mine/+oo]_(j <- A1) [[j ]]_stli)) in h.
      rewrite (mineC (\big[mine/+oo]_(j <- A2) [[j ]]_stli)) (mineC (\big[mine/+oo]_(j <- B1) [[j ]]_stli))
        in h.
      exists (A1 ++ A2 |- C); subst; first by rewrite mem_head.
      rewrite//= !big_map big_min_cat.
      by rewrite (le_trans h IH22).
    * apply (mine_gexy (\big[mine/+oo]_(j <- B2) [[j ]]_stli)) in h.
      exists (B1 ++ B2 |- D); subst; first by rewrite !in_cons eq_refl orTb orbT.
      rewrite//= !big_map big_min_cat.
      by rewrite (le_trans h IH12).
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite in_cons => /predU1P[ | IH1].
  + exists (A ++ B |- C); subst; first by rewrite mem_head.
    move: IH2.
    rewrite //= /minR !big_map.
    suff : \big[mine/+oo]_(j <- A ++ B ++ B) [[j]]_stli =
           \big[mine/+oo]_(j <- A ++ B) [[j]]_stli by move=> ->.
    rewrite !big_min_cat {1}/mine {2}/mine {7}/mine {11}/mine; repeat case: ifP; rewrite//=.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (A ++ B |- C); subst; first by rewrite mem_head.
    rewrite //= !big_map.
    rewrite //= !big_map in IH2.
    have := le_total_ereal (\big[mine/+oo]_(j <- A) [[j ]]_stli) (\big[mine/+oo]_(j <- B) [[j ]]_stli).
    move => /orP [h|h]; rewrite !big_min_cat {1}/mine; case: ifPn; rewrite//=.
    -  rewrite ltNge. move => /negPn h'. by rewrite (le_trans h' IH2).
    -  rewrite ltNge. move => /negPn h'. by rewrite (le_trans h' IH2).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (X ++ B ++ A ++ Y |- C); subst; first by rewrite mem_head.
    rewrite //= !big_map !big_min_cat.
    rewrite //= !big_map !big_min_cat in IH2.
    rewrite (mineA (\big[mine/+oo]_(j <- A) [[j ]]_stli)) in IH2.
    rewrite (mineC (\big[mine/+oo]_(j <- A) [[j ]]_stli)) in IH2.
    by rewrite (mineA (\big[mine/+oo]_(j <- B) [[j ]]_stli))//=.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite in_cons => /predU1P[|IH1].
  + exists (C |- X ++ B ++ A ++ Y); subst; first by rewrite mem_head.
    rewrite //= !big_map !big_max_cat.
    rewrite //= !big_map !big_max_cat in IH2.
    rewrite (maxA (\big[maxe/-oo]_(j <- A) [[j ]]_stli)) in IH2.
    rewrite (maxC (\big[maxe/-oo]_(j <- A) [[j ]]_stli)) in IH2.
    by rewrite (maxA (\big[maxe/-oo]_(j <- B) [[j ]]_stli))//=.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- exists (dl_bool _ _ _ _ false :: A |- B); first by rewrite mem_head.
  by rewrite /minR/maxR//= !big_cons !big_map ge_min leNye orTb.
- exists (A |- dl_bool neg_def impl_def m_def l_def true :: B); first by rewrite mem_head.
  by rewrite /= !big_cons !big_map maxye leey.
- move: IHseq_calc_stli => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + exists ((a `/\ b) :: B |- A); subst; first by rewrite mem_head.
    rewrite //= !big_ord_recl big_ord0 !tnthS !tnth0 big_cons !big_map miney.
    rewrite //= !big_cons !big_map in IH2.
    rewrite {2}/mine; case: ifP; rewrite//=.
    move => /negP/negP h. rewrite -leNgt in h.
    apply (mine_gexy  (\big[mine/+oo]_(j <- B) [[j ]]_stli)) in h.
    by rewrite (le_trans h IH2).
  + move/predU1P : IH1 => [|IH1].
    exists ((a `/\ b) :: B |- A); subst; first by rewrite mem_head.
    rewrite //= !big_ord_recl big_ord0 !tnthS !tnth0 big_cons !big_map miney.
    rewrite //= !big_cons !big_map in IH2.
    rewrite {2}/mine; case: ifP; rewrite//=.
    move => /ltW h.
     apply (mine_gexy (\big[mine/+oo]_(j <- B) [[j ]]_stli)) in h.
    by rewrite (le_trans h IH2).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- case IHseq_calc_stli1 => [q1].
  case IHseq_calc_stli2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH12 /predU1P[h1 | h1] IH22.
  + subst.
    exists (A |- (a `/\ b) :: B); subst; first by rewrite mem_head.
    rewrite //=!big_map big_cons !big_map in IH12.
    rewrite //= !big_map big_cons !big_map in IH22.
    rewrite //= !big_ord_recl big_ord0 !tnthS !tnth0 big_cons !big_map miney.
    rewrite {2}/mine. case: ifP; rewrite//=.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- case IHseq_calc_stli1 => [q1].
  case IHseq_calc_stli2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH12 /predU1P[h1 | h1] IH22.
  + subst.
    exists ((a `\/ b) :: B |- A); subst; first by rewrite mem_head.
    rewrite //= big_cons !big_map in IH12.
    rewrite //= big_cons !big_map in IH22.
    rewrite //= !big_ord_recl big_ord0 !tnthS !tnth0 big_cons !big_map maxeNy.
    rewrite {1}/maxe. case: ifP; rewrite//=.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + exists (A |- (a `\/ b) :: B); subst; first by rewrite mem_head.
    rewrite //= big_cons !big_map in IH2.
    rewrite //= !big_ord_recl big_ord0 !tnthS !tnth0 big_cons !big_map maxeNy.
    rewrite {2}/maxe. case: ifP; rewrite//=.
    move => /ltW h.
    apply (maxe_gexy (\big[maxe/-oo]_(j <- B) [[j ]]_stli)) in h.
    by rewrite (le_trans IH2 h).
  + move/predU1P : IH1 => [|IH1].
    exists (A |- (a `\/ b) :: B); subst; first by rewrite mem_head.
    rewrite //= big_cons !big_map in IH2.
    rewrite //= !big_ord_recl big_ord0 !tnthS !tnth0 big_cons !big_map maxeNy.
    rewrite {2}/maxe. case: ifP; rewrite//=.
    move => /negP/negP h. rewrite -leNgt in h.
    apply (maxe_gexy (\big[maxe/-oo]_(j <- B) [[j ]]_stli)) in h.
    by rewrite (le_trans IH2 h).
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + exists (A |- [:: (`~ a)]); subst; first by rewrite mem_head.
    rewrite //= !big_cons big_nil maxNye in IH2.
    rewrite leeNy_eq {1}/mine in IH2; move/eqP in IH2.
    rewrite //=!big_map !big_cons big_nil maxeNy.
    move: IH2. case: ifP.
    * move => _ h. rewrite h.
      have h_inf : - -oo = +oo. move => t; have hh := eqe_oppLRP (-oo) (+oo); by [].
      by rewrite h_inf leey.
    * by rewrite big_map => _ h; by rewrite h leNye.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- case IHseq_calc_stli1 => [q1].
  case IHseq_calc_stli2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH12 /predU1P[h1 | h1] IH22.
  + subst.
    exists ((`~ a) :: A |- B); subst; first by rewrite mem_head.
    rewrite //=!big_map !big_cons ?big_nil ?maxeNy ?minNye in IH12 IH22.
    rewrite //=!big_map !big_cons {1}/mine; case: ifP; rewrite !big_map//=.
    by move => /ltW h; rewrite (le_trans h IH12).
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
- move: IHseq_calc_stli => [q + IH2].
  rewrite !in_cons => /predU1P[|IH1].
  + exists (A |- [:: (a `=> b)]); subst; first by rewrite mem_head.
    rewrite //= !big_cons big_nil maxeNy in IH2.
    rewrite //=!big_map !big_cons big_nil maxeNy; repeat case: ifP.
    - by rewrite leey.
    - move => /negP h.
      rewrite {1}/mine big_map in IH2. move: IH2. case: ifPn; rewrite//=.
  + by exists q => //; rewrite !in_cons IH1 !orbT.
- case IHseq_calc_stli1 => [q1].
  case IHseq_calc_stli2 => [q2].
  rewrite !in_cons //= => /predU1P[h2 | h2] IH12 /predU1P[h1 | h1] IH22.
  + subst.
    exists ((a `=> b) :: A1 ++ A2 |- B); subst; first by rewrite mem_head.
    rewrite //=!big_map big_cons {1}/mine in IH12.
    rewrite //= !big_map big_cons big_nil maxeNy in IH22.
    rewrite //=!big_map !big_cons. move: IH12.
    repeat case: ifP; rewrite ?minye !big_map ?big_min_cat//=; move => h1 h2 h3;
    rewrite {1}/mine; case: ifP; rewrite//= => h4.
    * move /ltW in h2. have h5 := le_trans IH22 h1.
      by rewrite (le_trans h5).
    * move/negbT in h4; rewrite -leNgt in h4.
      by rewrite (le_trans (le_trans (le_trans h4 IH22) h1)).
    * rewrite {1}/mine; case: ifP; move: h4; rewrite {1}/mine; case: ifP; rewrite//=;
      move => _ /negbT h5 _; rewrite -leNgt in h5;
      by rewrite (le_trans h5).
    * by move /ltW in h4; rewrite (le_trans h4).
    * move: h4; rewrite {1}/mine; case: ifP; rewrite//= =>  h4 /ltW h5.
      - move /ltW in h4. by rewrite (le_trans (le_trans h5 h4) h3).
      - by rewrite (le_trans h5).
    * rewrite {1}/mine; case: ifP; rewrite//= => /ltW h5.
      by rewrite (le_trans h5).
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
  + by exists q2 => //; rewrite !in_cons h2 !orbT.
  + by exists q1 => //; rewrite !in_cons h1 !orbT.
Qed.

Lemma stli_cat1C Q a : seq_calc_stli (a :: Q) = seq_calc_stli ([::a] ++ Q).
Proof. by []. Qed.

Lemma eex_nil Q P : seq_calc_stli (P ++ Q) <-> seq_calc_stli (Q ++ P).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
rewrite (hxy _  Q P). split => ih.
- apply eex_stli; by rewrite cats0//=.
- apply eex_stli in ih. by rewrite cats0//= in ih.
Qed.

Lemma exL_nil Q A B C :
    seq_calc_stli (((A ++ B) |- C) :: Q) <->
    seq_calc_stli (((B ++ A) |- C) :: Q).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
split; rewrite (hxy _  A B) (hxy _  B A);
exact/exL_stli.
Qed.

Lemma exR_nil Q A B C :
    seq_calc_stli ((C |- (A ++ B)) :: Q) <->
    seq_calc_stli ((C |- (B ++ A)) :: Q).
Proof.
intros.
have hxy M L : M ++ L = [::] ++ M ++ L ++ [::] by rewrite /= cats0.
split; rewrite (hxy _  A B) (hxy _  B A);
exact/exR_stli.
Qed.

Lemma cat_cons_xyz_xy (I L M N : (seq formula * seq formula)):
 [:: I; L; M; N] = [:: I; L] ++ [::M; N] .
Proof. by rewrite //=. Qed.

Lemma cat_cons_xyz_xyz (I L M N : (seq formula * seq formula)):
 [:: I; L; M; N] = [:: I; L; M] ++ [:: N] .
Proof. by rewrite //=. Qed.

Lemma comm_xy (a c : formula):
  [:: [:: c] |- [:: a]] ++ [:: [:: a] |- [:: c]] =
                   [:: [::] ++ [:: c] |- [:: a], [:: a] ++ [::] |- [:: c] & [::]].
Proof. by []. Qed.

Lemma comm_hyper_xy (a b : formula):
  seq_calc_stli [:: [:: b] |- [:: a]; [:: a] |- [:: b]].
Proof.
rewrite stli_cat1C. rewrite -(cat0s [:: b]) -{2}((cat0s [:: a])).
rewrite comm_xy.
apply comm_hyper_stli; rewrite ?cat0s ?cats0; by apply id_stli.
Qed.

Lemma stli_prelinearity (a b : formula) :
  seq_calc_stli ([:: ([::] |- [:: ((a `=> b) `\/ (b `=> a))])]).
Proof.
apply orR_stli.
apply implR_stli.
have cat_cons : [:: [:: a] |- [:: b]; [::] |- [:: b `=> a]] =
                  [:: [:: a] |- [:: b]] ++ [:: [::] |- [:: b `=> a]] by [].
rewrite cat_cons eex_nil.
apply implR_stli.
exact: comm_hyper_xy.
Qed.

Lemma cat_cons4 (I L M N : seq formula * seq formula):
 [:: I; L; M; N] = [:: I]++ [:: L] ++ [:: M] ++ [:: N].
Proof. by []. Qed.

Lemma stli_seq_distributivity (a b c : formula) :
  seq_calc_stli ([:: ([::] |- [:: ((a `/\ (b `\/ c)) `=> ((a `/\ b) `\/ (a `/\ c)))])]).
Proof.
apply implR_stli. apply andL_stli. apply orR_stli.
apply andR_stli; first by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
rewrite stli_cat1C; apply eex_nil.
apply andR_stli; first by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
rewrite stli_cat1C; apply eex_nil.
apply orR_stli; apply andR_stli; apply orL_stli; last  by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
- rewrite stli_cat1C; apply eex_nil.
  apply orL_stli; apply andR_stli.
  * rewrite cat_cons_xyz_xy; apply eex_nil; apply ew_stli; apply comm_hyper_xy.
  * rewrite stli_cat1C; apply ew_stli; exact: id_stli.
  * rewrite cat_cons_xyz_xy; apply ew_stli; apply comm_hyper_xy.
  * rewrite cat_cons_xyz_xy; apply eex_nil; apply ew_stli; apply comm_hyper_xy.
- rewrite stli_cat1C; apply eex_nil.
  apply orL_stli; apply andR_stli.
  * rewrite cat_cons4.
    apply eex_stli. rewrite//= cat_cons_xyz_xy; apply ew_stli; apply comm_hyper_xy.
  * rewrite stli_cat1C; apply ew_stli; exact: id_stli.
  * rewrite//= cat_cons_xyz_xy; apply ew_stli; apply comm_hyper_xy.
  * rewrite cat_cons4; apply eex_stli; rewrite//= cat_cons_xyz_xy;
      apply eex_nil; apply ew_stli; apply comm_hyper_xy.
- rewrite stli_cat1C; apply eex_nil.
  apply orL_stli; apply andR_stli.
  * rewrite cat_cons4; apply eex_stli; rewrite//= cat_cons_xyz_xy; apply ew_stli; apply comm_hyper_xy.
  * rewrite cat_cons4; apply eex_stli; apply ew_stli; exact: id_stli.
  * rewrite//= cat_cons_xyz_xy; apply ew_stli; apply comm_hyper_xy.
  * rewrite stli_cat1C; apply eex_nil; rewrite//= cat_cons_xyz_xy; apply eex_nil;
      apply ew_stli; apply comm_hyper_xy.
Qed.

Lemma stl_seq_andC (a b : formula) :
  seq_calc_stli [:: ([:: a `/\ b] |- [:: b`/\ a])].
Proof.
apply andR_stli; apply andL_stli.
- by rewrite stli_cat1C; apply eex_nil; apply ew_stli; exact: id_stli.
- by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
Qed.

Lemma stli_seq_orC (a b : formula) :
  seq_calc_stli [:: ([:: a `\/ b] |- [:: b`\/ a])].
Proof.
apply orL_stli; apply orR_stli.
- by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
- by rewrite stli_cat1C; apply eex_nil; apply ew_stli; exact: id_stli.
Qed.

Lemma stli_seq_andA1 (a b c : formula) :
  seq_calc_stli [:: ([:: a `/\ (b `/\ c)] |- [:: (a `/\ b) `/\ c])].
Proof.
apply andR_stli; apply andL_stli.
- apply andR_stli; first by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
  rewrite stli_cat1C; apply eex_nil.
  apply andR_stli; apply andL_stli; last by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
  rewrite stli_cat1C; apply eex_nil; rewrite stli_cat1C; apply eex_nil; apply ew_stli.
  exact: comm_hyper_xy.
- rewrite stli_cat1C; apply eex_nil.
  apply andL_stli.
  by rewrite stli_cat1C; apply eex_nil; apply ew_stli; exact: id_stli.
Qed.

Lemma stli_seq_andA2 (a b c : formula) :
  seq_calc_stli [:: ([:: (a `/\ b) `/\ c] |- [:: a `/\ (b `/\ c)])].
Proof.
apply andR_stli; apply andL_stli.
- apply andL_stli; by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
- apply andR_stli; apply andL_stli; first by rewrite stli_cat1C; apply eex_nil; apply ew_stli; exact: id_stli.
  rewrite stli_cat1C; apply eex_nil. rewrite stli_cat1C; apply eex_nil.
  apply andR_stli; last by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
  rewrite stli_cat1C; apply eex_nil; rewrite stli_cat1C; apply eex_nil; apply ew_stli.
  exact: comm_hyper_xy.
Qed.

Lemma stli_seq_orA1 (a b c : formula) :
  seq_calc_stli [:: ([:: a `\/ (b `\/ c)] |- [:: (a `\/ b) `\/ c])].
Proof.
apply orL_stli; apply orR_stli.
- apply orL_stli; apply orR_stli; last by rewrite stli_cat1C; apply eex_nil; apply ew_stli; exact: id_stli.
  rewrite stli_cat1C; apply eex_nil; rewrite stli_cat1C; apply eex_nil.
  apply orL_stli; first by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
  rewrite stli_cat1C; apply eex_nil; rewrite stli_cat1C; apply eex_nil; apply ew_stli.
  exact: comm_hyper_xy.
- apply orR_stli.
  by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
Qed.

Lemma stli_seq_orA2 (a b c : formula) :
  seq_calc_stli [:: ([:: (a `\/ b) `\/ c] |- [:: a `\/ (b `\/ c)])].
Proof.
apply orL_stli; apply orR_stli.
- rewrite stli_cat1C; apply eex_nil. apply orR_stli.
  by rewrite stli_cat1C; apply eex_nil; apply ew_stli; exact: id_stli.
- apply orL_stli; last by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
  rewrite stli_cat1C; apply eex_nil; apply orL_stli; apply orR_stli;
    first by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
  rewrite stli_cat1C; apply eex_nil; rewrite stli_cat1C; apply eex_nil; apply ew_stli.
  exact: comm_hyper_xy.
Qed.

Lemma stli_seq_and1 (a b : formula) :
  seq_calc_stli [:: ([:: a `/\ (a `\/ b)] |- [:: a])].
Proof.
apply andL_stli; by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
Qed.

Lemma stli_seq_and2 (a b : formula) :
  seq_calc_stli [:: ([:: a] |- [:: a `/\ (a `\/ b)])].
Proof.
apply andR_stli; first by exact: id_stli. 
apply orR_stli; first by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
Qed.

Lemma stli_seq_or1 (a b : formula) :
  seq_calc_stli [:: ([:: a `\/ (a `/\ b)] |- [:: a])].
Proof.
apply orL_stli; last by exact: id_stli.
apply andL_stli; by rewrite stli_cat1C; apply ew_stli; exact: id_stli.
Qed.

Lemma stli_seq_or2 (a b : formula) :
  seq_calc_stli [:: ([:: a] |- [:: a `\/ (a `/\ b)])].
Proof.
apply orR_stli;  by exact: id_stli.
Qed.

Lemma stli_seq_unit_el1 (a : formula) :
  seq_calc_stli [:: ([:: a `/\ dl_bool _ _ _ _ true] |- [:: a ])].
Proof.
apply andL_stli.
have h : [:: [:: a] |- [:: a]; [:: dl_bool neg_def impl_def m_def l_def true] |- [:: a]] =
           [:: [:: a] |- [:: a]] ++ [:: [:: dl_bool neg_def impl_def m_def l_def true] |- [:: a]].
  by [].
rewrite h.
apply ew_stli.
apply id_stli.
Qed.

Lemma stli_seq_unit_el2 (a : formula) :
  seq_calc_stli [:: ([:: a ] |- [:: a `/\ dl_bool _ _ _ _ true ])].
Proof.
rewrite -(cats0 [:: a]) stli_cat1C.
rewrite -(cats0 [:: dl_and (tnth [:: a; dl_bool neg_def impl_def m_def l_def true])]).
rewrite -(cats0 [:: dl_and (tnth [:: a; dl_bool neg_def impl_def m_def l_def true])]).
apply andR_stli.
- exact: id_stli.
- exact: top_stli.
Qed.

End stl_hypersequent_calc.
