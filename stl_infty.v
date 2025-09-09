From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra ldl.

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
Local Open Scope ldl_scope.
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

Lemma stl_infty_mandI f1 f2 (e : expr (boolT_def f1 m_def f2)) : [[ e `** e ]]_stli = [[ e ]]_stli.
Proof.
rewrite //= ?big_cons ?big_nil.
set t1 := _ e.
rewrite /=/mine; repeat case: ifP => //=. 
move => _ h. apply negbT in h. rewrite ltey in h. 
move /negPn /eqP in h. by [].
Qed.

Lemma stl_infty_morI f1 f2 (e : expr (boolT_def f1 m_def f2)) : [[ e `++ e ]]_stli = [[ e ]]_stli.
Proof.
rewrite /= !big_cons big_nil /maxe.
repeat case: ifP => //=. 
move => _ h. rewrite ltNge leNye in h; by [].
Qed.

Lemma stl_infty_mandC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `** e2 ]]_stli = [[ e2 `** e1 ]]_stli.
Proof.
rewrite /= ?big_cons ?big_nil !miney.
rewrite /=/mine; repeat case: ifP => //=; move => h1 h2.
- apply ltW in h1. apply ltW in h2.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h1. move/negbFE in h1.
  rewrite  ltNge in h2. move/negbFE in h2.
  apply: le_anti. by apply/andP; split.
Qed.

Lemma stl_infty_morC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_stli = [[ e2 `++ e1 ]]_stli.
Proof.
rewrite /=  /maxR !big_cons !big_nil !maxeNy.
 rewrite /= /maxe; repeat case: ifP => //=; move => h1 h2 . 
- apply ltW in h1. apply ltW in h2.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h1. move/negbFE in h1.
  rewrite  ltNge in h2. move/negbFE in h2.
  apply: le_anti. by apply/andP; split.
Qed.

Lemma stl_infty_morA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) :
  [[ (e1 `++ (e2 `++ e3)) ]]_stli = [[ ((e1 `++ e2) `++ e3) ]]_stli.
Proof.
rewrite /= /maxR !big_cons !big_nil.
rewrite !maxeNy /= /maxe; repeat case: ifP; rewrite//= => h1 h2 h3 h4.
- rewrite  ltNge in h2. move/negbFE in h2.
  apply ltW in h3.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h2. move/negbFE in h2.
  apply ltW in h4.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h3. move/negbFE in h3.
  apply ltW in h2.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h4. move/negbFE in h4.
  have h5:=  lt_trans h1 h2. apply ltW in h5.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h4. move/negbFE in h4.
  apply ltW in h2.
  apply: le_anti. by apply/andP; split.
- apply ltW in h1. apply ltW in h3.  
  rewrite  ltNge in h2; move/negbFE in h2.
  rewrite  ltNge in h4; move/negbFE in h4.
  have h5 : [[e2 ]]_stli = [[e3 ]]_stli. by apply: le_anti; apply/andP; split.
  rewrite  -h5 in h4.
  by apply: le_anti; apply/andP; split.
- rewrite  ltNge in h1; move/negbFE in h1.
  rewrite  ltNge in h3; move/negbFE in h3.
  have h5 := le_trans h3 h1.
  rewrite  ltNge in h2. exfalso. 
  move/negbTE: h2; rewrite h5//=.
Qed.

Lemma stl_infty_mandA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `** (e2 `** e3) ]]_stli = [[ (e1 `** e2) `** e3 ]]_stli.
Proof.
rewrite /= /maxR !big_cons !big_nil !miney.
rewrite /= /mine; repeat case: ifP; rewrite//= => h1 h2 h3 h4.
- have h5 := lt_trans h1 h3.
  rewrite  ltNge in h2. move/negbFE in h2.
  apply ltW in h5.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h1; move/negbFE in h1.
  rewrite  ltNge in h3; move/negbFE in h3.
  have h5 := le_trans h3 h1.
  apply ltW in h2.
  have h6 : [[e2 ]]_stli = [[e3 ]]_stli. by apply: le_anti; apply/andP; split.
  rewrite -h6 in h4. apply ltW in h4.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h2; move/negbFE in h2.
  apply ltW in h4.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h1; move/negbFE in h1.
  rewrite  ltNge in h3; move/negbFE in h3.
  have h5 := le_trans h3 h1.
  apply ltW in h4.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h2; move/negbFE in h2.
  apply ltW in h3.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h4; move/negbFE in h4.
  apply ltW in h2.
  apply: le_anti. by apply/andP; split.
- rewrite  ltNge in h3; move/negbFE in h3.
  apply ltW in h2.
  apply: le_anti. by apply/andP; split. 
Qed.

Lemma stl_infty_involution (e : expr boolT_fuzzy) :
  [[`~ (`~e)]]_stli = [[ e ]]_stli.
Proof. by rewrite //= oppeK. Qed.


Theorem stl_infty_mand_unit f1 f2 (e :  (expr (boolT_def f1 m_def f2))) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_stli = [[ e ]]_stli.
Proof.
rewrite//= /minR !big_cons big_nil.
rewrite /= /mine; case: ifPn; rewrite//=. 
move => h. 
rewrite ltey in h.
by move/negbTE/eqP in h.
Qed.

Theorem stl_infty_mor_unit f1 f2 (e :  (expr (boolT_def f1 m_def f2))) :
  [[ e `++ (ldl_bool _ _ _ _ false) ]]_stli = [[ e ]]_stli.
Proof.
rewrite//= !big_cons big_nil/= /maxe; case: ifPn; rewrite//=. 
move => h. 
rewrite ltNge leNye in h; by [].
Qed.

Lemma stl_infty_residuation (e1 e2 e3 : expr boolT_stli) :
  [[e1 `** e2]]_stli <= [[ e3 ]]_stli <-> [[ e2 ]]_stli <= [[e1 `=> e3]]_stli.
Proof.
split; rewrite//= /minR !big_cons big_nil !miney /mine; repeat case: ifPn; rewrite ?leey//=. 
- move => h1 h2 _.
  rewrite ltNge Bool.negb_involutive in h1.
  by rewrite (le_trans h1 h2).
- move => /ltW h1 _ h3.
  by rewrite (le_trans h1 h3).
Qed.

Lemma neg_swap_ineq (e1 e2 : \bar R) : (- e1 <= - e2)%E = (e2 <= e1)%E.
Proof.
rewrite leeNr oppeK//=.
Qed.

Lemma stl_infty_demorgan_mand f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[`~ (e1 `** e2)]]_stli = [[(`~ e1) `++ (`~ e2)]]_stli.
Proof.
rewrite /= /maxR !big_cons !big_nil !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2. move/ltW in h1.
- rewrite neg_swap_ineq in h1. apply ltW in h2. 
  have Heq : [[e1]]_stli = [[e2]]_stli.  apply le_anti; by rewrite h1 h2//=.
  by rewrite eqe_oppP Heq.
- move/negP/negP in h1. move/negP/negP in h2.
  rewrite ltNge Bool.negb_involutive neg_swap_ineq in h1.
  rewrite ltNge Bool.negb_involutive in h2.
  have Heq : [[e1]]_stli = [[e2]]_stli.  apply le_anti; by rewrite h1 h2//=.
  by rewrite eqe_oppP Heq.
Qed.

Lemma stl_infty_demorgan_mor f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[`~ (e1 `++ e2)]]_stli = [[(`~ e1) `** (`~ e2)]]_stli.
rewrite /= /maxR !big_cons !big_nil !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2. move/ltW in h1.
- rewrite neg_swap_ineq in h1. apply ltW in h2. 
  have Heq : [[e1]]_stli = [[e2]]_stli.  apply le_anti; by rewrite h1 h2//=.
  by rewrite eqe_oppP Heq.
- move/negP/negP in h1. move/negP/negP in h2.
  rewrite ltNge Bool.negb_involutive neg_swap_ineq in h1.
  rewrite ltNge Bool.negb_involutive in h2.
  have Heq : [[e1]]_stli = [[e2]]_stli.  apply le_anti; by rewrite h1 h2//=.
  by rewrite eqe_oppP Heq.
Qed.

Lemma stl_infty_distr f1 (e1 e2 e3 :  (expr (boolT_def f1 m_def l_def))) :
  [[ e1 `/\ (e2 `\/ e3)]]_stli = [[ (e1 `/\ e2) `\/ (e1 `/\ e3)]]_stli.
Proof.
rewrite /= /maxR !big_cons !big_nil !miney !maxeNy.
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

Lemma stl_infty_and_abs f1 (e1 e2 : (expr (boolT_def f1 m_def l_def))) :
  [[ e1 `/\ (e1 `\/ e2)]]_stli = [[ e1 ]]_stli.
Proof.
rewrite /= /maxR !big_cons !big_nil !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2.
- apply ltW in h1. 
  rewrite  ltNge in h2. move/negbFE in h2.
  apply: le_anti. by apply/andP; split.
Qed.

Lemma dl2_or_abs f1 (e1 e2 : (expr (boolT_def f1 m_def l_def))) :
  [[ e1 `\/ (e1 `/\ e2)]]_stli = [[ e1 ]]_stli.
Proof.
rewrite /= /maxR !big_cons !big_nil !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2.
- apply ltW in h2. 
  rewrite  ltNge in h1. move/negbFE in h1.
  apply: le_anti. by apply/andP; split.
Qed.

Lemma stl_infty_prelinearity (e1 e2 e3 : @expr R (boolT_def impl_def m_def l_def)) :
  is_stl true ([[(e1 `=> e2) `\/ (e2 `=> e1)]]_stli).
Proof.
rewrite /= !big_cons !big_nil !maxeNy /maxe.
repeat case: ifP; rewrite//=.
- move => _ _  h3.
  by rewrite ltNge leey in h3.
- move => /negP h1 _ /ltW h3. by [].
- move => h1 h2 /negP/negP h. 
  rewrite ltNge Bool.negb_involutive leye_eq in h. move /eqP in h.
  by rewrite h le0y.
- move => _ /negP h2 /negP/negP h3. 
  rewrite ltNge Bool.negb_involutive in h3. rewrite//=.
Qed.



End stl_infty_lemmas.
