From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra ldl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

(**md**************************************************************************)
(* # Examples                                                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*      ldl_norm_infty == infinity norm                                       *)
(*         lbl_vec_sub == vector subtraction                                  *)
(*    eps_delta_robust == example from the ITP paper                          *)
(*        ldl_add_real == real addition                                       *)
(*        ldl_sub_real == real subtraction                                    *)
(*   group_similiarity == TODO                                                *)
(* ```                                                                        *)
(******************************************************************************)

Section example_robust.
Local Open Scope ldl_scope.
Context {R : realType}.

Local Notation expr := (@expr R).

Let ldl_norm_infty n : expr (Fun_T n.+1 1) := ldl_fun
  (fun t : R ^ n.+1 => [ffun x : 'I_1 => \big[maxr/t 0]_(i < n.+1) t i ])%R.
Let idx0 := @ldl_idx R 1 ord0.
Local Notation "'`|' v '|'" := ((ldl_norm_infty _ `@ v) `! idx0).

Let ldl_vec_sub n :=
  ldl_fun2 (fun (x y : R ^ n) => [ffun i => x i - y i]%R).
Local Notation "x `- y" := (ldl_vec_sub _ `@2 (x, y)) (at level 42).

Lemma ldl_vec_sub0 n (e : expr (Vector_T n)) :
  [[ (ldl_vec_sub n) `@2 (e, ldl_vec [ffun x => 0%R]) ]]_B = [[ e ]]_B.
Proof.
by dependent induction e => /=; apply/ffunP => i; rewrite !ffunE/= subr0.
Qed.

Context {n m : nat} (eps delta : expr Real_T) (f : expr (Fun_T n.+1 m.+1))
  (v : expr (Vector_T n.+1)) (x : expr (Vector_T n.+1)).

Definition eps_delta_robust fn fm fl : expr (Bool_T fn impl_def fm fl) :=
  `| x `- v | `<= eps `=> `| (f `@ x) `- (f `@ v) | `<= delta.

End example_robust.

Section example_hierarchical.
Local Open Scope ldl_scope.
Context {R : realType}.

Definition group_confidence n m x y z eps
    (f : expr (Fun_T n.+1 m.+1)) (v : expr (Vector_T n.+1))
    (idxs : seq (expr (Index_T m.+1))) :=
  @ldl_and R x y z
    [seq (((ldl_app f v) `! idx) `<= ldl_real eps) `/\
           ((ldl_real (1-eps)) `<= (ldl_app f v) `! idx)
    | idx <- idxs].

End example_hierarchical.
