From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_ssreflect all_algebra ssralg ssrint ssrnum.
Require Import Coq.Arith.Plus.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive simple_type : Type :=
| Bool_T : simple_type
| Index_T : simple_type
| Real_T : simple_type
| Vector_T : nat -> simple_type
| Network_T : nat -> nat -> simple_type.

Inductive type : Type :=
| Simple_T : simple_type -> type
| Arrow_T : simple_type -> type -> type.


Infix "-->" := Arrow_T (right associativity, at level 60).

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

Section expr.

  Inductive expr : type -> Type :=
  | R : nat -> expr (Simple_T Real_T) 
  | I : nat -> expr (Simple_T Index_T)
  | B : bool -> expr (Simple_T Bool_T)

  (*| Net : nat -> nat -> expr (Simple_T Network_T)*)

  (*logical connectives*)
  | binary_logical_E : binary_logical -> expr (Simple_T Bool_T) -> expr (Simple_T Bool_T) -> expr (Simple_T Bool_T)
  | not_E : expr (Simple_T Bool_T) -> expr (Simple_T Bool_T)

  (*arithmetic operations*)
  | add_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | mult_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | minus_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T)

  (*quantifiers - left for later consideration*)
  (*)| forall_E: forall t, expr t -> expr (Simple_T Bool_T)
  | exists_E: forall t, expr t -> expr (Simple_T Bool_T)*)

  (*comparisons*)
  | comparisons_E : comparisons -> expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Bool_T)

  | app_E : forall t1 t2, expr (t1 --> t2) -> expr (Simple_T t1) -> expr t2

  (*other - needed for DL translations*)
  | abs_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | max_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | min_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | identity_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | division_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T).

End expr.




Definition Expr t := expr t.

(*making some notation easier - basic*)
Definition R' (n : nat) : Expr (Simple_T Real_T) :=
  R n.
Definition I' (n : nat) : Expr (Simple_T Index_T) :=
I n.
Definition B' (n : bool) : Expr (Simple_T Bool_T) :=
B n.
(*minor tests*)
Example zeroR := R' 0.
Example zero := I' 0.
Example tr := B' true.

(*making some notation easier - arithmetic and logical*)
Definition add_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T) :=
  add_E e1 e2 .
Definition mult_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T ):=
  mult_E e1 e2.
Definition minus_E' (e1 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T) :=
  minus_E e1.


Definition leq_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Bool_T) :=
  comparisons_E leq_E e1 e2.
Definition le_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Bool_T) :=
  comparisons_E le_E e1 e2.
Definition geq_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Bool_T) :=
  comparisons_E geq_E e1 e2.
Definition ge_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Bool_T) :=
  comparisons_E ge_E e1 e2.
Definition eq_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Bool_T) :=
  comparisons_E eq_E e1 e2.
Definition neq_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Bool_T) :=
  comparisons_E neq_E e1 e2.

Definition binary_logical_E' op (e1 e2 : Expr (Simple_T Bool_T)) : Expr (Simple_T Bool_T) :=
    binary_logical_E op e1 e2.

Definition and_E' (e1 e2 : Expr (Simple_T Bool_T)) : Expr (Simple_T Bool_T) :=
    binary_logical_E and_E e1 e2.
Definition or_E' (e1 e2 : Expr (Simple_T Bool_T)) : Expr (Simple_T Bool_T) :=
    binary_logical_E or_E e1 e2.
Definition impl_E' (e1 e2 : Expr (Simple_T Bool_T)) : Expr (Simple_T Bool_T) :=
    binary_logical_E impl_E e1 e2.
Definition not_E' (e: Expr (Simple_T Bool_T)) : Expr (Simple_T Bool_T) :=
    not_E e.

    (*making notation easier - application*)
Definition app_E' t1 t2 (F : Expr (t1 --> t2)) (X : Expr (Simple_T t1)) : Expr t2 :=
    app_E F X.

Definition abs_E' (e1 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T ):=
  abs_E e1.
Definition max_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T) :=
  max_E e1 e2.
Definition min_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T) :=
  min_E e1 e2.
Definition identity_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T) :=
  identity_E e1 e2.
Definition division_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T) :=
  division_E e1 e2.


(*currently for Łukasiewicz*)

Definition simple_type_translation (t: simple_type) : simple_type :=
  match t with
  | Bool_T => Real_T
  | Index_T => Index_T
  | Real_T => Real_T
  | Vector_T => Vector_T
  | Network_T => Network_T.

Definition type_translation (t:type) : type :=
  match t with
  | Simple_T => simple_type_translation t
  | Arrow_T => Arrow_T.

Fixpoint translation t (e: Expr t) : t :=
    match e with
    | R => type_translation t
    | I t => type_translation t (*need to actually work out indexing*)
    | B t => type_translation t (*need to figure out mapping of bool to real*)

    | binary_logical_E and_E E1 E2 =>
        max_E (add_E (translation E1) (add_E (translation E2) (minus_E (R 1)))) (R 0)
    | binary_logical_E or_E E1 E2 =>
        min_E (add_E (translation E1) (translation E2)) (R 1)
    | binary_logical_E impl_E' E1 E2 =>
        min_E (add_E (R 1) (add_E (minus_E (translation E1)) (translation E2))) (R' 1)
    | not_E E1 =>
        add_E (R 1) (minus_E (translation E1))

    (*simple airthmetic*)
    | add_E E1 E2 => add_E (translation E1) (translation E2)
    | mult_E E1 E2 => mult_E (translation E1) (translation E2)
    | minus_E E1 => minus_E (translation E1)

    (*comparisons*)
    | comparisons_E leq_E E1 E2 => add_E (R 1) (minus_E (abs_E (division_E (add_E E1 (minus_E E2))
    (add_E E1 E2))))
    | comparisons_E eq_E E1 E2 => add_E (R 1) (minus_E (max_E (division_E (add_E E1 (minus_E E2))
    (add_E E1 E2)) (R 0)))
    | comparisons_E neq_E E1 E2 => add_E (R 1) (minus_E (identity_E E1 E2))
    | comparisons_E geq_E E1 E2 => add_E (R 1) (minus_E (abs_E (division_E (add_E E2 (minus_E E1))
    (add_E E2 E1))))
    | comparisons_E le_E E1 E2 => max_E (add_E (add_E (R 1) (minus_E (abs_E (division_E (add_E E1 (minus_E E2))
    (add_E E1 E2))))) (add_E (add_E (R 1) (minus_E (identity_E E1 E2))) (minus_E (R 1))))
     (R 0)
    | comparisons_E ge_E E1 E2 => max_E (add_E (add_E (R 1) (minus_E (abs_E (division_E (add_E E2 (minus_E E1))
      (add_E E2 E1)))))
      (add_E (add_E (R 1) (minus_E (abs_E (division_E (add_E E2 (minus_E E1))
      (add_E E2 E1))))) (minus_E (R 1)))) 
      (R 0)
    | app_E t1 t2 E1 E2 => app_E (translation E1) (translation E2)
    end.


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




