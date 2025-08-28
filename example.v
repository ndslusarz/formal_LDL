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
  (fun t : n.+1.-tuple R => [tuple \big[maxr/[tnth t 0] ]_(i <- t) i ])%R.

Program Definition ldl_vec_sub n :=
  ldl_fun2 (fun (x y : n.-tuple R) => [tuple tnth x i - tnth y i | i < n]%R).

Lemma ldl_vec_sub0 n (e : expr (Vector_T n)) :
  [[ ldl_app2 (ldl_vec_sub n) e (ldl_vec [tuple of nseq n 0%R]) ]]_B = [[ e ]]_B.
Proof.
by dependent induction e => /=; apply/eq_from_tnth => i; rewrite tnth_mktuple tnth_nseq subr0.
Qed.

Context {n m : nat} (eps delta : expr Real_T) (f : expr (Fun_T n.+1 m.+1))
  (v : expr (Vector_T n.+1)) (x : expr (Vector_T n.+1)).

Definition eps_delta_robust fn fm fl : expr (Bool_T fn impl_def fm fl) :=
  ldl_impl
    (ldl_lookup (ldl_app (ldl_norm_infty n) (ldl_app2 (ldl_vec_sub _) x v))
                (ldl_idx ord0) `<= eps)
    (ldl_lookup (ldl_app (ldl_norm_infty m) (ldl_app2 (ldl_vec_sub _) (ldl_app f x) (ldl_app f v)))
                (ldl_idx ord0) `<= delta).

End example_robust.

Section example_hierarchical.
Local Open Scope ldl_scope.
Context {R : realType}.

Definition group_confidence n m eps a b c
    (f : expr (Fun_T n.+1 m.+1))
    (x : expr (Vector_T n.+1))
    (gs : seq (expr (Index_T m.+1))) :=
  @ldl_and R a b c
    (map
       (fun idx =>
          (((ldl_app f x) `! idx) `<= ldl_real eps) `/\
            ((ldl_real (1-eps)) `<= (ldl_app f x) `! idx)) gs).

End example_hierarchical.
