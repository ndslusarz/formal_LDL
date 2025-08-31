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
(* ## Structural properties                                                   *)
(* - stl_infty_mandI == commutativity of monoidal conjunction                 *)
(* - stl_infty_mandC == commutativity of monoidal conjunction                 *)
(* - stl_infty_mandA == associativity of monoidal conjunction                 *)
(* - stl_infty_morI == commutativity of monoidal disjunction                  *)
(* - stl_infty_morC == commutativity of monoidal disjunction                  *)
(* - stl_infty_morA == associativity of monoidal disjunction                  *)
(* - stl_infty_andI == commutativity of conjunction                           *)
(* - stl_infty_andC == commutativity of conjunction                           *)
(* - stl_infty_andA == associativity of conjunction                           *)
(* - stl_infty_orI == commutativity of disjunction                            *)
(* - stl_infty_orC == commutativity of disjunction                            *)
(* - stl_infty_orA == associativity of disjunction                            *)
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
split; rewrite//= /minR !big_cons big_nil !miney /mine; case: ifPn => //= h1 h2.
- case: (ltP ([[e2]]_stli) 0) => Hsign.
- 
-
-
- 
Admitted.

Lemma neg_swap_ineq (e1 e2 : \bar R) : (- e1 < - e2)%E = (e2 < e1)%E.
Proof.
Admitted.

Lemma stl_infty_demorgan_mand f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[`~ (e1 `** e2)]]_stli = [[(`~ e1) `++ (`~ e2)]]_stli.
Proof.
rewrite /= /maxR !big_cons !big_nil !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2.
- rewrite neg_swap_ineq in h1. rewrite ltNge in h1. move /negP in h1.
  apply ltW in h2. by [].
- move/negP in h1. move/negP in h2.
  rewrite neg_swap_ineq in h1. rewrite ltNge in h1. move /negP in h1.
  move/negPn in h1. move/negP in h2.
  rewrite -leNgt in h2. 

Admitted.

Lemma stl_infty_demorgan_mor f1 (e1 e2 : expr (boolT_def f1 m_def l_def)) :
  [[`~ (e1 `++ e2)]]_stli = [[(`~ e1) `** (`~ e2)]]_stli.
rewrite /= /maxR !big_cons !big_nil !miney !maxeNy.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//= => h1 h2.
- rewrite neg_swap_ineq in h1. rewrite ltNge in h1. move /negP in h1.
  apply ltW in h2. by [].
- (*same as above*)
Admitted.

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

(*Lemma swap_lt_implies_ge0 (e1 e2 : \bar R):
  e2 \is a fin_num ->
  (e2 - e1 < e1 - e2)%E -> (0 <= e1 - e2)%E.
Proof.
move=> h.
have /ltW : (0 < (e1 - e2) - (e2 - e1))%E by rewrite sube_gt0//=.
rewrite oppeB//=.
rewrite -addrA. addNr addr0 -mul2e => /mulr_ge0_le ?.
Qed.*)

Lemma stl_infty_prelinearity (e1 e2 e3 : @expr R (boolT_def impl_def m_def l_def)) :
  is_stl true ([[(e1 `=> e2) `\/ (e2 `=> e1)]]_stli).
Proof.
rewrite /= /maxR !big_cons !big_nil !maxeNy.
have Hle : ([[e1 ]]_stli - [[e2 ]]_stli <= +oo)%E by apply: leey. 
rewrite leNgt in Hle. move /negP in Hle.
have Hge : (-oo <=[[e2 ]]_stli - [[e1 ]]_stli )%E by apply: leey. 
rewrite leNgt in Hge. move /negP in Hge.
rewrite /= /mine /maxe; repeat case: ifP; rewrite//=.
- move => /andP [h1 h2] _ h.
  rewrite -(lteD2rE _ _ h1) -(lteD2rE _ _ h2) in h.
  apply ltW in h. move: h.
  set x := [[e1 ]]_stli. set y := [[e2 ]]_stli.

admit. (*actual case*)
- move => /andP [+ h2] H _ _.
  rewrite fin_numE => /andP [/negP /eqP h h']. 
  by move: h; rewrite H eq_refl.
- move => _ /andP [h1 h2]. (*actual case*)
  admit.
- move => /eqP H _ /andP [_ +].
  rewrite fin_numE => /andP [/negP /eqP h h']. 
  by move: h; rewrite H eq_refl.
- move => /eqP H _ _ /andP [+ _].
  rewrite fin_numE => /andP [/negP /eqP h h']. 
  by move: h; rewrite H eq_refl.
- move => _ _ _ _ /negP H. 
  move/negP : H; rewrite ltey; move /negPn/eqP ->.
  by rewrite le0y//=.
- move => /andP [+ h2] H _ _.
  rewrite fin_numE => /andP [/negP /eqP h h']. 
  by move: h; rewrite H eq_refl.
Admitted.

End stl_infty_lemmas.vrewrite leNgt in Hle.
