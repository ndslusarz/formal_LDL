From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Require Import ldl.

Section example.
Local Open Scope ldl_scope.
Context {R : realType}.

Let ldl_norm_infty (n : nat) : @expr R (Fun_T n.+1 1) := ldl_fun (fun (t : (n.+1).-tuple R) =>
   [tuple \big[maxr/[tnth t 0] ]_(i <- t) i ])%R.

Let ldl_vec_sub (n : nat) : @expr R (Vector_T n) -> @expr R (Vector_T n) -> @expr R (Vector_T n).
Proof.
elim.
- move=> r. apply.
- move=> p b. apply.
- move=> m i. apply.
- move=> m t1.
  elim.
  + move=> r. exact: (ldl_real 0).
  + move=> p b. exact: (ldl_bool _ true).
  + move=> l i. exact: (ldl_idx i).
  + move=> l t2. exact: (ldl_vec [tuple nth 0 t1 i - nth 0 t2 i | i < l])%R.
  + move=> p s. exact: (ldl_bool _ true).
  + move=> p s. exact: (ldl_bool _ true).
  + move=> e1 e2. exact: e1.
  + move=> p c e1 e2 e3 e4. exact: (ldl_bool _ true).
  + move=> l k f. exact: ldl_fun f.
  + move=> l k e1 e2 v1 v2. exact: (ldl_vec [tuple 0 | i < k])%R.
  + move=> l v1 v2 i1 i2. exact: (ldl_real 0).
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p c e f1 e1 f2 e2. exact: e2.
- move=> m l f e. exact: e.
- move=> m l e1 f1 e2 f2. exact.
- move=> m e1 f1 e2 f2. exact.
Defined.

Context (n m : nat) (eps delta : @expr R Real_T) (f : @expr R (Fun_T (n.+1) (m.+1)))
  (v : @expr R (Vector_T (n.+1))) (x : @expr R (Vector_T (n.+1))).

Definition eps_delta_robust :=
    (((ldl_lookup (ldl_app (ldl_norm_infty n) (ldl_vec_sub x v)) (ldl_idx ord0)) `<= eps)
       `=> ((ldl_lookup (ldl_app (ldl_norm_infty m) (ldl_vec_sub (ldl_app f x) (ldl_app f v))) (ldl_idx ord0))
       `<= delta)).

End example.

Section example2.
Local Open Scope ldl_scope.
Context {R : realType}.

Let ldl_sum_real : @expr R Real_T -> @expr R Real_T -> @expr R Real_T.
Proof.
elim.
- move=> r. apply.
- move=> p b. apply.
- move=> m i. apply.
- move=> m t1.
  elim.
  + move=> r. exact: (ldl_real 0).
  + move=> p b. exact: (ldl_bool _ true).
  + move=> l i. exact: (ldl_idx i).
  + move=> l t2. exact: (ldl_vec [tuple nth 0 t1 i - nth 0 t2 i | i < l])%R.
  + move=> p s. exact: (ldl_bool _ true).
  + move=> p s. exact: (ldl_bool _ true).
  + move=> e1 e2. exact: e1.
  + move=> p c e1 e2 e3 e4. exact: (ldl_bool _ true).
  + move=> l k f. exact: ldl_fun f.
  + move=> l k e1 e2 v1 v2. exact: (ldl_vec [tuple 0 | i < k])%R.
  + move=> l v1 v2 i1 i2. exact: (ldl_real 0).
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p c e f1 e1 f2 e2. exact: e2.
- move=> m l f e. exact: e.
- move=> m l e1 f1 e2 f2. exact.
- move=> m e1 f1 e2 f2. exact.
Defined.

Let ldl_real_sub : @expr R Real_T -> @expr R Real_T -> @expr R Real_T.
Proof.
elim.
- move=> r. apply.
- move=> p b. apply.
- move=> m i. apply.
- move=> m t1.
  elim.
  + move=> r. exact: (ldl_real 0).
  + move=> p b. exact: (ldl_bool _ true).
  + move=> l i. exact: (ldl_idx i).
  + move=> l t2. exact: (ldl_vec [tuple nth 0 t1 i - nth 0 t2 i | i < l])%R.
  + move=> p s. exact: (ldl_bool _ true).
  + move=> p s. exact: (ldl_bool _ true).
  + move=> e1 e2. exact: e1.
  + move=> p c e1 e2 e3 e4. exact: (ldl_bool _ true).
  + move=> l k f. exact: ldl_fun f.
  + move=> l k e1 e2 v1 v2. exact: (ldl_vec [tuple 0 | i < k])%R.
  + move=> l v1 v2 i1 i2. exact: (ldl_real 0).
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p c e f1 e1 f2 e2. exact: e2.
- move=> m l f e. exact: e.
- move=> m l e1 f1 e2 f2. exact.
- move=> m e1 f1 e2 f2. exact.
Defined.

(*Notes:
- does not say groups need to cover ALL indices*)

Fixpoint ldl_sum_vec (x : seq (@expr R Real_T)) :=
  match x with
  | nil => ldl_real 0
  | a::l => ldl_sum_real a (ldl_sum_vec l)
end.

Definition prob_group (n m : nat)
  (f : @expr R (Fun_T (n.+1) (m.+1)))
  (x : @expr R (Vector_T (n.+1)))
  (gs : seq (@expr R (Index_T (m.+1)))) :=
  ldl_sum_vec (map (ldl_lookup (ldl_app f x)) gs).

Context (n m : nat) (eps : @expr R Real_T) (f : @expr R (Fun_T (n.+1) (m.+1)))
  (x : @expr R (Vector_T (n.+1))) (Gs : seq (seq (@expr R (Index_T (m.+1)))))
  (r : flag).

Let fancy_or (r : @flag) (eps p: @expr R Real_T) :=
 (ldl_cmp r cmp_le p eps) `\/ (ldl_cmp r cmp_le (ldl_real_sub (ldl_real 1%R) p) eps).

(*could not get the notation to work
 - could not resolve implicit argument of type flag
unsure how to solve that
*)
(* (p `<= eps) `\/ ((ldl_real_sub (ldl_real 1%R) p) `<= eps).*)

Definition group_similiarity :=
  ldl_and (map (fancy_or r eps) (map (prob_group f x) Gs)).


End example2.
