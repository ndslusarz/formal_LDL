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

Local Notation expr := (@expr R).

Definition ldl_add n :=
  ldl_fun2 (fun (x y : n.-tuple R) => [tuple tnth x i + tnth y i | i < n]%R).

Definition ldl_sub n :=
  ldl_fun2 (fun (x y : n.-tuple R) => [tuple tnth x i - tnth y i | i < n]%R).

(*Notes:
- does not say groups need to cover ALL indices*)

Definition ldl_sum_vec n :=
  ldl_fun (fun x : n.-tuple R => (mktuple (fun => foldr GRing.add 0 x)) : 1.-tuple R)%R.

(* Fixpoint ldl_sum_vec (x : seq (expr Real_T)) := *)
(*   match x with *)
(*   | nil => ldl_real 0 *)
(*   | a::l => ldl_real_add a (ldl_sum_vec l) *)
(* end. *)

Definition prob_group n m
    (f : expr (Fun_T n.+1 m.+1))
    (x : expr (Vector_T n.+1))
    (gs : seq (expr (Index_T m.+1))) :=
  ldl_sum_vec (map (ldl_lookup (ldl_app f x)) gs).

Context {n m : nat} (eps : expr Real_T) (f : expr (Fun_T n.+1 m.+1))
  (x : expr (Vector_T n.+1)) (Gs : seq (seq (expr (Index_T m.+1))))
  (fn : flag_neg) (fi : flag_impl) (fm : flag_monoid).

Let fancy_or (eps p : expr Real_T) :=
 (ldl_cmp fn fi fm l_def cmp_le p eps) `\/
 (ldl_cmp fn fi fm l_def cmp_le (ldl_real_sub (ldl_real 1) p) eps).

Definition group_similiarity :=
  ldl_and (map (fancy_or eps) (map (prob_group f x) Gs)).

End example_hierarchical.
