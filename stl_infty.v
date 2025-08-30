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
(* # Properties of stl_infty                                                        *)
(*                                                                            *)
(* ## Structural properties                                                   *)
(* - stl_infty_mandC_nary == n-ary commutativity of conjunction                     *)
(* - stl_infty_mandC == commutativity of conjunction                                *)
(* - stl_infty_mandA == associativity of conjunction                                *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

HB.instance Definition _ (R : realType) x y z v :=
  @gen_eqMixin (@expr R (Bool_T x y z v)).

Section stl_infty_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_stli" := (@stl_infty_translation R _ e).

Lemma stl_infty_mandI f1 f2 (e : expr (Bool_T_def f1 m_def f2)) : [[ e `** e ]]_stli = [[ e ]]_stli.
Proof.
rewrite /=/minR ?big_cons ?big_nil.
set t1 := _ e.
rewrite /=/minr; repeat case: ifP; lra.
Qed.

Lemma stl_infty_morI f1 f2 (e : expr (Bool_T_def f1 m_def f2)) : [[ e `++ e ]]_stli = [[ e ]]_stli.
Proof.
rewrite /= /maxR !big_cons big_nil /maxr.
repeat case: ifP; lra.
Qed.

Lemma stl_infty_mandC f1 f2 (e1 e2 : expr (Bool_T_def f1 m_def f2)) :
  [[ e1 `** e2 ]]_stli = [[ e2 `** e1 ]]_stli.
Proof.
rewrite /=/minR ?big_cons ?big_nil.
by rewrite /=/minr; repeat case: ifP; lra.
Qed.

Lemma stl_infty_morC f1 f2 (e1 e2 : expr (Bool_T_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_stli = [[ e2 `++ e1 ]]_stli.
Proof.
rewrite /=  /maxR !big_cons !big_nil.
by rewrite /= /maxr; repeat case: ifP; lra.
Qed.

Lemma stl_infty_morA f1 f2 (e1 e2 e3 : expr (Bool_T_def f1 m_def f2)) :
  [[ (e1 `++ (e2 `++ e3)) ]]_stli = [[ ((e1 `++ e2) `++ e3) ]]_stli.
Proof.
rewrite /= /maxR !big_cons !big_nil.
rewrite /maxr.
by repeat case: ifPn => //; lra.
Qed.

(*not true unless we use ereal, thinking*)
(*Theorem stl_infty_mand_unit f1 f2 (e :  (expr (Bool_T_def f1 m_def f2))) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_stli = [[ e ]]_stli.
Proof.
rewrite//= /minR !big_cons big_nil.
rewrite /minr; repeat case: ifP; intros; try lra.
Qed.

Theorem stl_infty_mor_unit f1 f2 (e :  (expr (Bool_T_def f1 m_def f2))) :
  [[ e `++ (ldl_bool _ _ _ _ false) ]]_stli = [[ e ]]_stli.
Proof.
have := translate_Bool_T_01 p p1 Godel _ _ _ e.
rewrite//= /maxR !big_cons big_nil.
rewrite /maxr; repeat case: ifP; intros; try lra.
Qed.*)

(*add implication and then try*)
(*Lemma stl_infty_prelinearity (e1 e2 e3 : expr Bool_T_fuzzy) :
  [[e1 `** e2]]_stli <= [[ e3 ]]_stli <-> [[ e2 ]]_stli <= [[e1 `=> e3]]_stli.
Proof.
split; rewrite//=/minR; rewrite !big_cons big_nil /minr; repeat case: ifP; intros; try lra.
Qed.*)

Lemma stl_infty_demorgan_mand  (e1 e2 : expr Bool_T_fuzzy) :
  [[`~ (e1 `** e2)]]_stli = [[(`~ e1) `++ (`~ e2)]]_stli.
Proof.
by rewrite//= /minR /maxR !big_cons !big_nil /maxr /minr; repeat case: ifP; intros; lra.
Qed.

Lemma stl_infty_demorgan_mor  (e1 e2 : expr Bool_T_fuzzy) :
  [[`~ (e1 `++ e2)]]_stli = [[(`~ e1) `** (`~ e2)]]_stli.
Proof.
by rewrite//= /minR /maxR !big_cons !big_nil /maxr /minr; repeat case: ifP; intros; lra.
Qed.

End stl_infty_lemmas.
