From mathcomp Require Import all_ssreflect all_algebra ssralg ssrint ssrnum sequences.
Require Import Coq.Arith.Plus.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive simple_type : Type :=
| Bool_T : simple_type
| Index_T : nat -> simple_type
| Real_T : simple_type
| Vector_T : nat -> simple_type
(* | Network_T : nat -> nat -> simple_type *).

(* Inductive type : Type :=
| Simple_T : simple_type -> type
| Arrow_T : simple_type -> type -> type. *)

(* 
Infix "-->" := Arrow_T (right associativity, at level 60). *)

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

(* Inductive net_context (n m : nat) : Type :=
  | network : net_context n m. *)

Inductive net_context : Type :=
  | network : nat -> nat -> net_context.


Variable R : realFieldType.

Section expr.
Inductive expr : simple_type -> Type :=
  | Real : R -> expr Real_T
  | Bool : bool -> expr Bool_T
  | Index : forall n : nat, 'I_n -> expr (Index_T n)
  | Vector : forall n : nat, n.-tuple R -> expr (Vector_T n)

  (*| : nat -> nat -> expr (Simple_Twork_T)*)

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

(*  | app_net n: expr (Vector_T n) -> expr Real_T*)

  (*comparisons*)
  | comparisons_E : comparisons -> expr Real_T -> expr Real_T -> expr Bool_T
  (* | lookup_E v i: expr (Simple_T Vector_T) -> expr (Simple_T Index_T) -> expr (Simple_T Real_T) 
  I had this one before probably need to add this again, why did it get deleted?*)

  (*other - needed for DL translations*)
  | abs_E : expr Real_T -> expr Real_T
  | max_E : expr Real_T -> expr Real_T -> expr Real_T
  | min_E : expr Real_T -> expr Real_T -> expr Real_T
  | identity_E : expr Real_T -> expr Real_T -> expr Real_T
  | division_E : expr Real_T -> expr Real_T -> expr Real_T.

End expr.


(*currently for Łukasiewicz*)

Definition type_translation (t: simple_type) : Type:=
  match t with
  | Bool_T => R
  | Real_T => R
  | Vector_T n => n.-tuple R
(*R ^nat *) (*both of these need to be wrapped in something record type, then get *)
(*some proof added on that they are of length n*)
  | Index_T n => (*R ^nat*) (*to do*) 'I_n
  (* | Network_T n m => R ^nat *) (* -> R ^nat *)(*delete completely if network in context*)
end.

Compute (type_translation Real_T).
Compute R.
Section defintion_of_the_translation.
Variable net : net_context.

Import GRing.Theory Num.Def.
Local Open Scope ring_scope.

Fixpoint translation t (e: expr t) : type_translation t :=
    match e in expr t return type_translation t with
    | Bool true => (1%R : type_translation Bool_T) (* (1%(type_translation Bool_T)) *)
    | Bool false => 0%R
    | Real r => r%R
    | Index n i => i(*again, in progress because the type_translation for this is in progress*)
    | Vector n t => t (*need to figure it out in type_translation*)

(*anything below to be corrected and rewritten after:

- the type of this function is settled
- the problem of using R, which is a variable and does not compile to Type is settled

but should primarily be non-problematic, inductive on above base cases*)
    | binary_logical_E and_E E1 E2 =>
        maxr (translation E1 + translation E2 - 1)%R 0
    | binary_logical_E or_E E1 E2 =>
        minr (translation E1 + translation E2)%R 1
    | binary_logical_E impl_E' E1 E2 =>
        minr (1 - translation E1 + translation E2) 1
    | not_E E1 =>
        1 - translation E1

    (*simple airthmetic*)
    | add_E E1 E2 => translation E1 + translation E2
    | mult_E E1 E2 => translation E1 * translation E2
    | minus_E E1 => - translation E1

    (*comparisons*)
    | comparisons_E leq_E E1 E2 => 1 - `|(translation E1 - translation E2) / (translation E1 + translation E2)|
    | comparisons_E eq_E E1 E2 => 1 - maxr ((translation E1 - translation E2) / (translation E1 + translation E2)) 0
    | comparisons_E neq_E E1 E2 => (*add_E (R 1) (minus_E (identity_E E1 E2))*) 0
    | comparisons_E geq_E E1 E2 => (*add_E (R 1) (minus_E (abs_E (division_E (add_E E2 (minus_E E1))
    (add_E E2 E1))))*) 0
    | comparisons_E le_E E1 E2 => (*max_E (add_E (add_E (R 1) (minus_E (abs_E (division_E (add_E E1 (minus_E E2))
    (add_E E1 E2))))) (add_E (add_E (R 1) (minus_E (identity_E E1 E2))) (minus_E (R 1))))
     (R 0)*) 0
    | comparisons_E ge_E E1 E2 => (*max_E (add_E (add_E (R 1) (minus_E (abs_E (division_E (add_E E2 (minus_E E1))
      (add_E E2 E1)))))
      (add_E (add_E (R 1) (minus_E (abs_E (division_E (add_E E2 (minus_E E1))
      (add_E E2 E1))))) (minus_E (R 1))))
      (R 0)*) 0
    | abs_E _ => 0
    | max_E _ _ => 0
    | min_E _ _ => 0
    | division_E _ _ => 0
    | identity_E _ _ => 0
    end.

(* 
  (*Example*)

Lemma commutativity_add : forall E1 E2,
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
  
Qed.

 *)


