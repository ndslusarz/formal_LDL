From HB Require Import structures.
Require Import Stdlib.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra dl.

(**md**************************************************************************)
(* # Properties of stl_infty                                                  *)
(*                                                                            *)
(* first we prove equivalence of mand/and and mor/or                          *)
(*   as a consequence we need only prove properties for one set of connectives*)
(* - stl_infty_mand_and_eq = proof that mand and and are equivalent           *)
(* - stl_infty_mand_and_eq = proof that mand and and are equivalent           *)
(*                                                                            *)
(* mand == monoidal conjucntion                                               *)
(* mor == monoidal disjunction                                                *)
(*                                                                            *)
(* ## Structural properties                                                   *)
(* - stl_infty_mandI == commutativity of mand                                 *)
(* - stl_infty_mandC == commutativity of mand                                 *)
(* - stl_infty_mandA == associativity of mand                                 *)
(* - stl_infty_morI == commutativity of mor                                   *)
(* - stl_infty_morC == commutativity of mor                                   *)
(* - stl_infty_morA == associativity of mor                                   *)
(* - stl_infty_prelinearity == preliniearity property                         *)
(* - stl_infty_residuation == residuation                                     *)
(* - stl_infty_distr == distributivity                                        *)
(* - stl_infty_demorgan_mand == deMorgan 1                                    *)
(* - stl_infty_demorgan_mand == deMorgan 1                                    *)
(* - stl_infty_involution == involution of negation                           *)
(* - stl_infty_mand_unit = unit element of mand                               *)
(* - stl_infty_mor_unit = unit element of mor                                 *)
(* - stl_infty_and_abs = absorption property for and                          *)
(* - stl_infty_or_abs = absorption property for or                            *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

HB.instance Definition _ (R : realType) x y z v :=
  @gen_eqMixin (@expr R (boolT x y z v)).

Section stl_infty_lemmas.
Local Open Scope dl_scope.
Local Open Scope ereal_scope.
Context {R : realType}.

Local Notation "[[ e ]]_stli" := (@stl_infty_translation R _ e).

Definition is_stl b (x : \bar R) := if b then x >= 0 else x < 0.

(*because of their equivalence, lemmas are only proven for mand/mor*)
Lemma stl_infty_mand_and_eq f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[e1 `** e2]]_stli = [[e1 `/\ e2]]_stli.
Proof. by rewrite//=. Qed.

Lemma stl_infty_mor_or_eq f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[e1 `++ e2]]_stli = [[e1 `\/ e2]]_stli.
Proof. by rewrite//=. Qed.

Lemma stl_infty_mandI f1 f2 (e : expr (boolT_def f1 m_def f2)) :
  [[ e `** e ]]_stli = [[ e ]]_stli.
Proof.
rewrite //= !big_ord_recl !big_ord0 !tnthS !tnth0.
set t1 := _ e.
rewrite /= /mine; repeat case: ifP => //=.
by move/negbT; rewrite -leNgt leye_eq => /eqP.
Qed.

Lemma stl_infty_morI f1 f2 (e : expr (boolT_def f1 m_def f2)) :
  [[ e `++ e ]]_stli = [[ e ]]_stli.
Proof.
rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0 /maxe.
by rewrite lteNy ltxx.
Qed.

Lemma stl_infty_mandC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `** e2 ]]_stli = [[ e2 `** e1 ]]_stli.
Proof.
rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0!miney.
rewrite /=/mine; repeat case: ifP => //=.
- by move=>/ltW h1 /ltW h2; apply/le_anti/andP; split.
- by rewrite !ltNge=> /negbFE h1 /negbFE h2; apply/le_anti/andP; split.
Qed.

Lemma stl_infty_morC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_stli = [[ e2 `++ e1 ]]_stli.
Proof.
rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0 !maxeNy.
rewrite /=/maxe; repeat case: ifP => //=.
- by move=> /ltW h1 /ltW h2; apply/le_anti/andP; split.
- by rewrite !ltNge => /negbFE h1 /negbFE h2; apply/le_anti/andP; split.
Qed.

Lemma stl_infty_morA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) :
  [[ (e1 `++ (e2 `++ e3)) ]]_stli = [[ ((e1 `++ e2) `++ e3) ]]_stli.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0 !tnthS !tnth0/= !big_ord_recl !big_ord0 !tnthS !tnth0.
rewrite !maxeNy /= /maxe; repeat case: ifP => //=; try by move=> _ ->.
- by move=> h1 h2; rewrite (lt_trans h1 h2).
- rewrite ltNge => /negbFE h1 /ltW h2; rewrite ltNge => /negbFE h3 _.
  by have h4 := le_trans h3 h1; apply/le_anti/andP; split.
Qed.

Lemma stl_infty_mandA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `** (e2 `** e3) ]]_stli = [[ (e1 `** e2) `** e3 ]]_stli.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0 /= !big_ord_recl !big_ord0 !tnthS !tnth0 !miney.
rewrite /= /mine; repeat case: ifP => //=; try by move=> _ ->.
- by move=> h1 h2 h3; rewrite (lt_trans h1) in h2.
- rewrite !ltNge => /negbFE h1 /negbFE h2 /negbFE h3.
  by rewrite (le_trans h3).
Qed.

Lemma stl_infty_involution (e : expr boolT_fuzzy) :
  [[`~ (`~e)]]_stli = [[ e ]]_stli.
Proof. by rewrite /= oppeK. Qed.

Theorem stl_infty_mand_unit f1 f2 (e : expr (boolT_def f1 m_def f2)) :
  [[ e `** dl_bool _ _ _ _ true ]]_stli = [[ e ]]_stli.
Proof.
rewrite /=!big_ord_recl big_ord0 !tnthS !tnth0 /mine.
by rewrite ltey; case: ifPn => //; rewrite negbK => /eqP.
Qed.

Theorem stl_infty_mor_unit f1 f2 (e : expr (boolT_def f1 m_def f2)) :
  [[ e `++ dl_bool _ _ _ _ false ]]_stli = [[ e ]]_stli.
Proof.
by rewrite /=!big_ord_recl !big_ord0 !tnthS !tnth0 /maxe; case: ifPn; rewrite ltNge leNye.
Qed.

Lemma stl_infty_residuation (e1 e2 e3 : expr boolT_stli) :
  [[e1 `** e2]]_stli <= [[ e3 ]]_stli <-> [[ e2 ]]_stli <= [[e1 `=> e3]]_stli.
Proof.
split; rewrite /= /minR !big_ord_recl !big_ord0 !tnthS !tnth0 !miney /mine; repeat case: ifPn; rewrite ?leey//=.
- by move => h1 h2 _; by rewrite (le_trans _ h2)// leNgt.
- by move => /ltW h1 _; exact: le_trans.
Qed.

Lemma stl_infty_demorgan_mand f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[`~ (e1 `** e2)]]_stli = [[(`~ e1) `++ (`~ e2)]]_stli.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0 !tnthS !tnth0 !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2. move/ltW in h1.
- rewrite leeN2 in h1; apply ltW in h2.
  have Heq : [[e1]]_stli = [[e2]]_stli by apply le_anti; rewrite h1 h2.
  by rewrite eqe_oppP Heq.
- move/negP/negP in h1. move/negP/negP in h2.
  rewrite -leNgt leeN2 in h1.
  rewrite -leNgt in h2.
  have Heq : [[e1]]_stli = [[e2]]_stli by apply le_anti; rewrite h1 h2.
  by rewrite eqe_oppP Heq.
Qed.

Lemma stl_infty_demorgan_mor f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[`~ (e1 `++ e2)]]_stli = [[(`~ e1) `** (`~ e2)]]_stli.
rewrite /= /maxR !big_ord_recl !big_ord0 !tnthS !tnth0 !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite //= => h1 h2. move/ltW in h1.
- rewrite leeN2 in h1. apply ltW in h2.
  have Heq : [[e1]]_stli = [[e2]]_stli by apply le_anti; rewrite h1 h2.
  by rewrite eqe_oppP Heq.
- move/negP/negP in h1. move/negP/negP in h2.
  rewrite -leNgt leeN2 in h1.
  rewrite -leNgt in h2.
  have Heq : [[e1]]_stli = [[e2]]_stli by apply le_anti; rewrite h1 h2.
  by rewrite eqe_oppP Heq.
Qed.

Lemma stl_infty_distr f1 (e1 e2 e3 : expr (boolT_def f1 m_def l_def)) :
  [[ e1 `/\ (e2 `\/ e3)]]_stli = [[ (e1 `/\ e2) `\/ (e1 `/\ e3)]]_stli.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0 /= !big_ord_recl !big_ord0 !tnthS !tnth0 !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2 h3 h4 h5.
- rewrite ltNge in h2; move/negbFE in h2.
  rewrite ltNge in h3; move/negbFE in h3.
  apply: le_anti. by apply/andP; split.
- rewrite ltNge in h1; move/negbFE in h1.
  apply ltW in h3.
  apply: le_anti. by apply/andP; split.
- rewrite ltNge in h1; move/negbFE in h1.
  apply ltW in h2. apply ltW in h4.
  have H := le_trans h2 h4.
  apply: le_anti. by apply/andP; split.
- rewrite ltNge in h3; move/negbFE in h3.
  apply ltW in h4.
  apply: le_anti. by apply/andP; split.
- rewrite ltNge in h2; move/negbFE in h2.
  rewrite ltNge in h4; move/negbFE in h4.
  apply ltW in h3. apply ltW in h1.
  have H := le_trans h1 h4.
  apply: le_anti. by apply/andP; split.
- rewrite ltNge in h4; move/negbFE in h4.
  apply ltW in h3.
  apply: le_anti. by apply/andP; split.
Qed.

Lemma stl_infty_and_abs f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[ e1 `/\ (e1 `\/ e2)]]_stli = [[ e1 ]]_stli.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0 /= !big_ord_recl !big_ord0 !tnthS !tnth0 !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2.
- apply ltW in h1.
  rewrite  ltNge in h2. move/negbFE in h2.
  apply: le_anti. by apply/andP; split.
Qed.

Lemma dl2_or_abs f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[ e1 `\/ (e1 `/\ e2)]]_stli = [[ e1 ]]_stli.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0 /= !big_ord_recl !big_ord0 !tnthS !tnth0 !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2.
- apply ltW in h2.
  rewrite ltNge in h1. move/negbFE in h1.
  apply: le_anti. by apply/andP; split.
Qed.

Lemma stl_infty_prelinearity (e1 e2 e3 : @expr R (boolT_def impl_def m_def l_def)) :
  is_stl true ([[(e1 `=> e2) `\/ (e2 `=> e1)]]_stli).
Proof.
rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0 !maxeNy /maxe.
repeat case: ifPn => //=.
- by move => _ _; rewrite ltye.
- by move => /negP h1 _ /ltW h3.
- move => h1 h2 /negP/negP.
  by rewrite -leNgt leye_eq => /eqP ->.
- by move => _ /negP h2 /negP/negP; rewrite -leNgt.
Qed.

End stl_infty_lemmas.
