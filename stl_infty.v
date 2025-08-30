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
rewrite /= ?big_cons ?big_nil.
rewrite /=/mine; repeat case: ifP => //=; move => h1 h2 h3 h4. 

Admitted.

Lemma stl_infty_morC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_stli = [[ e2 `++ e1 ]]_stli.
Proof.
rewrite /=  /maxR !big_cons !big_nil.
 rewrite /= /maxe; repeat case: ifP => //. 
Admitted.

Lemma stl_infty_morA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) :
  [[ (e1 `++ (e2 `++ e3)) ]]_stli = [[ ((e1 `++ e2) `++ e3) ]]_stli.
Proof.
rewrite /= /maxR !big_cons !big_nil.
 rewrite /= /maxe; repeat case: ifP; move => h1 h2 h3 h4 h5 h6 h7; rewrite//=. 
(*some smarter unfolding here, lots of cases are the same case*)
Admitted.

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

(*add implication and then try*)
(*Lemma stl_infty_residuation (e1 e2 e3 : expr Bool_T_fuzzy) :
  [[e1 `** e2]]_stli <= [[ e3 ]]_stli <-> [[ e2 ]]_stli <= [[e1 `=> e3]]_stli.
Proof.
split; rewrite//=/minR; rewrite !big_cons big_nil /minr; repeat case: ifP; intros; try lra.
Qed.*)


(*add  distrib, prelinear*)

End stl_infty_lemmas.
