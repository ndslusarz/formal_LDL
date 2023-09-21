From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import sequences.

Import Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive simple_type : Type :=
| Bool_T : simple_type
| Index_T : nat -> simple_type
| Real_T : simple_type
| Vector_T : nat -> simple_type
(* | Network_T : nat -> nat -> simple_type *).

Inductive comparisons : Type :=
| leq_E : comparisons
| le_E : comparisons
| geq_E : comparisons
| ge_E : comparisons
| eq_E : comparisons
| neq_E : comparisons.

Inductive binary_logical : Type :=
| and_E : binary_logical
| or_E : binary_logical
| impl_E : binary_logical.

Print Grammar constr. (* to check precedence levels *)

Inductive net_context : Type :=
  | network : nat -> nat -> net_context.

Variable R : realFieldType.

Section expr.
Inductive expr : simple_type -> Type :=
  | Real : R -> expr Real_T
  | Bool : bool -> expr Bool_T
  | Index : forall n : nat, 'I_n -> expr (Index_T n)
  | Vector : forall n : nat, n.-tuple R -> expr (Vector_T n)

  (*logical connectives*)
  | binary_logical_E : binary_logical -> expr Bool_T -> expr Bool_T -> expr Bool_T
  | not_E : expr Bool_T -> expr Bool_T

  (*arithmetic operations*)
  | add_E : expr Real_T -> expr Real_T -> expr Real_T
  | mult_E : expr Real_T -> expr Real_T -> expr Real_T
  | minus_E : expr Real_T -> expr Real_T

  (*quantifiers - left for later consideration*)
  (*)| forall_E: forall t, expr t -> expr (Simple_T Bool_T)
  | exists_E: forall t, expr t -> expr (Simple_T Bool_T)*)

  | app_net n : net_context -> expr (Vector_T n) -> expr Real_T

  (*comparisons*)
  | comparisons_E : comparisons -> expr Real_T -> expr Real_T -> expr Bool_T
  (* | lookup_E v i: expr (Simple_T Vector_T) -> expr (Simple_T Index_T) -> expr (Simple_T Real_T) 
  I had this one before probably need to add this again, why did it get deleted?*)

  (*other - needed for DL translations*)
  | identity_E : expr Real_T -> expr Real_T -> expr Real_T.


End expr.


(*currently for Łukasiewicz*)

Definition type_translation (t: simple_type) : Type:=
  match t with
  | Bool_T => R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => (*R ^nat*) (*to do*) 'I_n
end.

Compute (type_translation Real_T).
Compute R.
Section defintion_of_the_translation.
(*Variable net : net_context.*)

Import GRing.Theory Num.Def.
Local Open Scope ring_scope.

Definition identity (x y : R) : R :=
  if x == y then 1 else 0.

Fixpoint translation t (e: expr t) : type_translation t :=
    match e in expr t return type_translation t with
    | Bool true => (1%R : type_translation Bool_T) 
    | Bool false => (0%R : type_translation Bool_T)
    | Real r => r%R
    | Index n i => i(*again, in progress because the type_translation for this is in progress*)
    | Vector n t => t (*need to figure it out in type_translation*)

    | binary_logical_E and_E E1 E2 =>
        maxr (translation E1 + translation E2 - 1)%R 0
    | binary_logical_E or_E E1 E2 =>
        minr (translation E1 + translation E2)%R 1
    | binary_logical_E impl_E E1 E2 =>
        minr (1 - translation E1 + translation E2) 1
    | not_E E1 =>
        1 - translation E1

    (*simple airthmetic*)
    | add_E E1 E2 => translation E1 + translation E2
    | mult_E E1 E2 => translation E1 * translation E2
    | minus_E E1 => - translation E1

    (*comparisons*)
    | comparisons_E eq_E E1 E2 => 1 - `|(translation E1 - translation E2) / (translation E1 + translation E2)|
    | comparisons_E leq_E E1 E2 => 1 - maxr ((translation E1 - translation E2) / (translation E1 + translation E2)) 0
    | comparisons_E neq_E E1 E2 => 1 - identity (translation E1) (translation E2)
    | comparisons_E geq_E E1 E2 => 1 - maxr ((translation E2 - translation E1) / (translation E2 + translation E1)) 0
    | comparisons_E le_E E1 E2 => maxr 
      ((1 - maxr ((translation E1 - translation E2) / (translation E1 + translation E2)) 0)
        + (1 - identity (translation E1) (translation E2)) - 1)
      0 
    | comparisons_E ge_E E1 E2 => maxr (
      (1 - maxr ((translation E2 - translation E1) / (translation E2 + translation E1)) 0)
        + (1 - identity (translation E1) (translation E2)) - 1
      )
      0
    | identity_E E1 E2 => identity (translation E1) (translation E2)

  (*network application - in progress, I should be able to get the size from the network_context somehow...*)
  (*also need to think how to get a value here*)
    | app_net size et v => 0
    end.

Definition and_E' (e1 e2 : expr Bool_T) : expr Bool_T :=
    binary_logical_E and_E e1 e2.
Definition or_E' (e1 e2 : expr Bool_T) : expr Bool_T :=
    binary_logical_E or_E e1 e2.
Definition impl_E' (e1 e2 : expr Bool_T) : expr Bool_T :=
    binary_logical_E impl_E e1 e2.


(* Lemma lt_and_eq_0 : forall x : R,
  0 < x -> (0 = x) = False.
Proof.
intros. Search lt. Search (_ < _ -> _ != _).
rewrite lt0r_neq0.  *)

Theorem commutativity_and (B1 B2 : expr Bool_T) :
  translation (and_E' B1 B2) = translation (and_E' B2 B1).
Proof.
rewrite /=.
by rewrite (addrC (_ B1)).
Qed.
(*simpl.
intros. simpl.
Search maxr.
case: lerP.
intros H1.
symmetry.
Print ltrP.
Search (maxr). 
case: real_ltgt0P.
case: ltrP. elim. reflexivity. auto.
(* case: lerP.
elim. reflexivity.
Search (_ < _ -> _ != _).
Search (_ = _ -> _ != _).
intros H2.
Search (_ = _ -> _). *)
(* rewrite -> lt0r_neq0. *)
Admitted.*)

(*Lemma translate_Bool_T_01 t (e : expr t) :
  0 <= (translation e : R) <= 1.
Proof.*)

Require Import Coq.Program.Equality.

Lemma translate_Bool_T_01 (e : expr Bool_T) :
  0 <= (translation e : R) <= 1.
Proof.
dependent induction e => //=.
- by case: ifPn => //; lra.
- set t1 := _ e1.
  set t2 := _ e2.
  case: b.
  + have [t1t2|t1t2] := lerP (t1 + t2 - 1) 0.
      lra.
    have := IHe1 e1 erefl JMeq_refl.
    rewrite -/t1 => ?.
    have := IHe2 e2 erefl JMeq_refl.
    rewrite -/t2 => ?.
    lra.
  + admit.
  + admit.
- admit.
- case: c => //.
Admitted.

Lemma translate_Real_T_01 (e : expr Real_T) :
  0 <= (translation e : R) <= 1.
Proof.
dependent induction e => //=.
Admitted.

Theorem associativity_and (B1 B2 B3: expr Bool_T) :
  translation (and_E' (and_E' B1 B2) B3) = translation (and_E' B1 (and_E' B2 B3)).
Proof.
rewrite /=.
set t1 := _ B1.
set t2 := _ B2.
set t3 := _ B3.
simpl in *.
have t101 : 0 <= t1 <= 1 := translate_Bool_T_01 B1.
have t201 : 0 <= t2 <= 1 := translate_Bool_T_01 B2.
have t301 : 0 <= t3 <= 1 := translate_Bool_T_01 B3.
have [t1t2|t1t2] := lerP (t1 + t2 - 1) 0.
  rewrite add0r.
  have [t31|t31] := lerP (t3 - 1) 0.
    have [t2t3|t2t3] := lerP (t2 + t3 - 1) 0.
      rewrite addr0.
      by have [t10|t10] := lerP (t1 - 1) 0; lra.
    rewrite !addrA.
    by have [t1t2t3|t1t2t3] := lerP (t1 + t2 + t3 - 1 - 1) 0; lra.
  have [t2t3|t2t3] := lerP (t2 + t3 - 1) 0.
    rewrite addr0.
    by have [t10|t10] := lerP (t1 - 1) 0; lra.
  rewrite !addrA.
  by have [t1t2t3|t1t2t3] := lerP (t1 + t2 + t3 - 1 - 1) 0; lra.
admit.
Admitted.

(*intros. simpl.
case: lerP.
intros H1.
case: lerP.*)

(* Search (?n:R + ?m:R = ?m:R + ?n:R). *)
(* Search ( 0 < ?m -> 0 != ?m). *)





(* Lemma commutativity_add : forall E1 E2,
  add_E' E1 E2 = add_E' E2 E1.
Admitted.

Lemma associativity_add : forall E1 E2 E3,
  add_E' (add_E' E1 E2) E3 = add_E' E1 (add_E' E2 E3).
Admitted.

Theorem commutativity_and : forall (E1 E2 : Expr (Simple_T Bool_T))  (B1 B2 : Expr (Simple_T Real_T)),
  (and_E' E1 E2 ===> B1) -> 
  (and_E' E2 E1 ===> B2) ->
  B1 = B2.
Proof.
  intros. inversion H. inversion H0. subst. dependent inversion H3. (*tbc after redoing into functional*)
  
Qed. *)
