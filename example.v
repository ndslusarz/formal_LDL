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

Definition ldl_vec_sub n : expr (Vector_T n) -> expr (Vector_T n) ->
  expr (Vector_T n).
Proof.
elim => {n}.
- move=> _; exact.
- move=> fn fi fm fl _; exact.
- move=> n i; exact.
- move=> n t.
  elim.
  + move=> _; exact: (ldl_real 0).
  + move=> fn fi fm fl; exact: ldl_bool.
  + move=> k; exact: ldl_idx.
  + move=> l t2; exact: (ldl_vec [tuple nth 0 t i - nth 0 t2 i | i < l])%R.
  + move=> fn fi fm _; exact: ldl_bool true.
  + move=> fn fi fm _; exact: ldl_bool true.
  + move=> fi fm fl e1 e2. exact: e1.
  + move=> fn fm fl _ e2 _ _; exact: e2.
  + move=> fn fi fl _; exact: ldl_bool true.
  + move=> fn fi fl _; exact: ldl_bool true.
  + move=> fn fi fm fl _ _ _ _ _; exact: ldl_bool true.
  + move=> l k; exact: ldl_fun.
  + move=> l k _ _ _ _; exact: (ldl_vec [tuple 0 | i < k])%R.
  + move=> l _ _ _ _; exact: (ldl_real 0).
- move=> fn fi fm _; exact.
- move=> fn fi fm _; exact.
- move=> fn fi fm _ _; exact.
- move=> fn fi fm _ _ _ _ e1; exact: e1.
- move=> fn fi fl _ e2; exact: e2.
- move=> fn fi fl _; exact.
- move=> fn fi fm fl _ _ _ _ _; exact.
- move=> k m _ e; exact: e.
- move=> n m e1 f1 e2 f2 e3; exact: (ldl_app e1 e2).
- move=> _ _ _ _ _; exact.
Defined.

Lemma ldl_vec_sub0 n (e : expr (Vector_T n)) :
  ldl_vec_sub e (ldl_vec [tuple of nseq n 0%R]) = e.
Proof.
dependent induction e.
- rewrite /ldl_vec_sub/=.
  congr ldl_vec.
  apply/eq_from_tnth => i.
  rewrite tnth_mktuple nth_nseq ltn_ord subr0.
  by apply: set_nth_default; rewrite size_tuple.
- by [].
Qed.

Context {n m : nat} (eps delta : expr Real_T) (f : expr (Fun_T n.+1 m.+1))
  (v : expr (Vector_T n.+1)) (x : expr (Vector_T n.+1)).

Definition eps_delta_robust fn fm fl : expr (Bool_T fn impl_def fm fl) :=
  ldl_impl
    (ldl_lookup (ldl_app (ldl_norm_infty n) (ldl_vec_sub x v))
                (ldl_idx ord0) `<= eps)
    (ldl_lookup (ldl_app (ldl_norm_infty m) (ldl_vec_sub (ldl_app f x) (ldl_app f v)))
                (ldl_idx ord0) `<= delta).

End example_robust.

Section example_hierarchical.
Local Open Scope ldl_scope.
Context {R : realType}.

Local Notation expr := (@expr R).

Definition ldl_real_add : expr Real_T -> expr Real_T -> expr Real_T.
Proof.
elim.
- move=> r _; exact: (ldl_real r).
- move=> fn fi fm fl _; exact.
- move=> m i; exact.
- move=> m t1.
  elim.
  + move=> r; exact: (ldl_real r).
  + move=> fn fi fm fl; exact: ldl_bool.
  + move=> k; exact: ldl_idx.
  + move=> l t2; exact: (ldl_vec [tuple nth 0 t1 i - nth 0 t2 i | i < l])%R.
  + move=> fn fi fm _; exact: ldl_bool true.
  + move=> fn fi fm _; exact: ldl_bool true.
  + move=> fi fm fl e1 e2. exact: e1.
  + move=> fn fm fl _ e2 _ _; exact: e2.
  + move=> fn fi fl _; exact: ldl_bool true.
  + move=> fn fi fl _; exact: ldl_bool true.
  + move=> fn fi fm fl _ _ _ _ _; exact: ldl_bool true.
  + move=> l k; exact: ldl_fun.
  + move=> l k _ _ _ _; exact: (ldl_vec [tuple 0 | i < k])%R.
  + move=> l _ _ _ _; exact: (ldl_real 0).
- move=> fn fi fm _; exact.
- move=> fn fi fm _; exact.
- move=> fn fi fm _ _; exact.
- move=> fn fi fm _ _ _ _ e1; exact: e1.
- move=> fn fi fl _ e2; exact: e2.
- move=> fn fi fl _; exact.
- move=> fn fi fm fl _ _ _ _ _; exact.
- move=> k m _ e; exact: e.
- move=> _ m _ _ _ _; exact.
- move=> n e1 f1 e2 f2 r; exact: ldl_lookup e1 e2.
Defined.

Lemma ldl_real0 (e : expr Real_T) : ldl_real_add e (ldl_real 0) = e.
Proof.
dependent induction e.
- by [].
- by [].
Qed.

Definition ldl_real_sub : expr Real_T -> expr Real_T -> expr Real_T.
Proof.
elim.
- move=> _; exact.
- move=> fn fi fm fl _; exact.
- move=> m i; exact.
- move=> m t1.
  elim.
  + move=> _; exact: (ldl_real 0).
  + move=> fn fi fm fl; exact: ldl_bool.
  + move=> k; exact: ldl_idx.
  + move=> l t2; exact: (ldl_vec [tuple nth 0 t1 i - nth 0 t2 i | i < l])%R.
  + move=> fn fi fm _; exact: ldl_bool true.
  + move=> fn fi fm _; exact: ldl_bool true.
  + move=> fi fm fl e1 e2. exact: e1.
  + move=> fn fm fl _ e2 _ _; exact: e2.
  + move=> fn fi fl _; exact: ldl_bool true.
  + move=> fn fi fl _; exact: ldl_bool true.
  + move=> fn fi fm fl _ _ _ _ _; exact: ldl_bool true.
  + move=> l k; exact: ldl_fun.
  + move=> l k _ _ _ _; exact: (ldl_vec [tuple 0 | i < k])%R.
  + move=> l _ _ _ _; exact: (ldl_real 0).
- move=> fn fi fm _; exact.
- move=> fn fi fm _; exact.
- move=> fn fi fm _ _; exact.
- move=> fn fi fm _ _ _ _ e1; exact: e1.
- move=> fn fi fl _ e2; exact: e2.
- move=> fn fi fl _; exact.
- move=> fn fi fm fl _ _ _ _ _; exact.
- move=> k m _ e; exact: e.
- move=> _ m _ _ _ _; exact.
- move=> _ _ _ _ _; exact.
Defined.

(*Notes:
- does not say groups need to cover ALL indices*)

Fixpoint ldl_sum_vec (x : seq (expr Real_T)) :=
  match x with
  | nil => ldl_real 0
  | a::l => ldl_real_add a (ldl_sum_vec l)
end.

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
