From HB Require Import structures.
Require Import Stdlib.Program.Equality.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra dl.

(**md**************************************************************************)
(* # Examples                                                                 *)
(*                                                                            *)
(* ```                                                                        *)
(*       dl_norm_infty == infinity norm                                       *)
(*         lbl_vec_sub == vector subtraction                                  *)
(*    eps_delta_robust == example from the ITP paper                          *)
(*         dl_add_real == real addition                                       *)
(*         dl_sub_real == real subtraction                                    *)
(*    group_similarity == TODO                                                *)
(* ```                                                                        *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Section example_robust.
Local Open Scope dl_scope.
Context {R : realType}.
Local Notation expr := (@expr R).

Let dl_norm_infty' n : R ^ n.+1 -> R ^ 1 :=
  (fun f => [ffun _ => \big[maxr/f 0]_(i < n.+1) `|f i|])%R.
Let dl_norm_infty n : expr (funT n.+1 1) := dl_fun (@dl_norm_infty' n).
Let idx0 := @dl_idx R 1 ord0.
Local Notation "'`|' v '|'" := ((dl_norm_infty _ `@ v) `! idx0).

Let dl_vec_sub' n : R ^ n -> R ^ n -> R ^ n :=
  fun x y : R ^ n => [ffun i => x i - y i]%R.
Let dl_vec_sub n : expr (fun2T n n n) := dl_fun2 (@dl_vec_sub' n).
Local Notation "x `- y" := (dl_vec_sub _ `@2 (x, y)) (at level 42).

Lemma dl_vec_sub0 n (e : expr (vectorT n)) :
  [[ (dl_vec_sub n) `@2 (e, dl_vec [ffun x => 0%R]) ]]_B = [[ e ]]_B.
Proof.
by dependent induction e => /=; apply/ffunP => i; rewrite !ffunE/= subr0.
Qed.

Context {n m : nat} (eps delta : expr realT) (f : expr (funT n.+1 m.+1))
  (x v : expr (vectorT n.+1)).

Definition eps_delta_robust fn fm fl : expr (boolT fn impl_def fm fl) :=
  `| x `- v | `<= eps `=> `| (f `@ x) `- (f `@ v) | `<= delta.

Let eps_delta_robust_dl2 := ([[ eps_delta_robust neg_undef m_undef l_undef ]]_dl2).
Compute eps_delta_robust_dl2.

End example_robust.

Section example_hierarchical.
Local Open Scope dl_scope.
Context {R : realType}.

Definition group_confidence n m x y z eps
    (f : expr (funT n.+1 m.+1)) (v : expr (vectorT n.+1))
    (idx_ : (expr (indexT m.+1)) ^ n) :=
  @dl_and R x y z _
    (fun i => (((dl_app f v) `! (idx_ i)) `<= dl_real eps) `/\
           ((dl_real (1-eps)) `<= (dl_app f v) `! (idx_ i))).

End example_hierarchical.
