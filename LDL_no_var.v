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
| Network_T : simple_type.

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
  | R : nat -> expr (Simple_T Real_T) (*temporary, couldn't get real to typecheck*)
  | I : nat -> expr (Simple_T Index_T)
  | B : bool -> expr (Simple_T Bool_T)

  | Net : nat -> nat -> expr (Simple_T Network_T)

  (*logical connectives*)
  | binary_logical_E : binary_logical -> expr (Simple_T Bool_T) -> expr (Simple_T Bool_T) -> expr (Simple_T Bool_T)
  | not_E : expr (Simple_T Bool_T) -> expr (Simple_T Bool_T)

  (*arithmetic operations*)
  | add_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | mult_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | minus_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T)

  (*quantifiers*)
  | forall_E: forall t, expr t -> expr (Simple_T Bool_T)
  | exists_E: forall t, expr t -> expr (Simple_T Bool_T)

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

(*Declare Custom Entry ldl.
Notation "S -> T" := (Arrow_T S T) (in custom ldl at level 50, right associativity).
Notation "x + y" := (add_E' x y) (in custom ldl at level 50, right associativity).
Notation "x * y" := (mult_E' x y) (in custom ldl at level 50, right associativity).

(*small tests*)
Example zero_add :=  zeroR + zeroR.
Example true_and := and_E' tr tr.
Example eq_zero := eq_E' zeroR zeroR.
*)
(*-------------------------------------------------------------------------------
SEMANTICS*)

Reserved Notation "E1 ===> E2" (no associativity, at level 90).

(*currently for Łukasiewicz*)
Inductive translation : forall t t', Expr t -> Expr t' -> Prop :=
| R_T : forall r,
  R' r ===> R' r
| I_T : forall i,
  I' i ===> I' i
| B_T : forall b,
  I' b ===> R' b

| and_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  and_E' E1 E2 ===> max_E' (add_E' E1' (add_E' E2' (minus_E' (R' 1)))) (R' 0)
| or_T : forall E1 E2 E1' E2',
  E1 ===> E1' ->
  E2 ===> E2' ->
  or_E' E1 E2 ===> min_E' (add_E' E1' E2') (R' 1)
| impl_T : forall E1 E2 E1' E2',
  E1 ===> E1' ->
  E2 ===> E2' ->
  impl_E' E1 E2 ===> min_E' (add_E' (R' 1) (add_E' (minus_E' E1') E2')) (R' 1)

  (*arithmetic operations*)
| add_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  add_E' E1 E2 ===> add_E' E1' E2'
| mult_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  mult_E' E1 E2 ===> mult_E' E1' E2'
| minus_T : forall E1 E1' ,
  E1 ===> E1' ->
  minus_E' E1 ===> minus_E' E1'

(*comparisons*)
| leq_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  leq_E' E1 E2 ===> add_E' (R' 1) (minus_E' (abs_E' (division_E' (add_E' E1' (minus_E' E2'))
   (add_E' E1' E2'))))
| eq_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  leq_E' E1 E2 ===> add_E' (R' 1) (minus_E' (max_E' (division_E' (add_E' E1' (minus_E' E2'))
  (add_E' E1' E2')) (R' 0)))
| neq_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  neq_E' E1 E2 ===> add_E' (R' 1) (minus_E' (identity_E' E1' E2'))
| geq_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  geq_E' E1 E2 ===> add_E' (R' 1) (minus_E' (abs_E' (division_E' (add_E' E2' (minus_E' E1'))
  (add_E' E2' E1'))))
| le_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  le_E' E1 E2 ===> max_E' (add_E' (add_E' (R' 1) (minus_E' (abs_E' (division_E' (add_E' E1' (minus_E' E2'))
  (add_E' E1' E2'))))) (add_E' (add_E' (R' 1) (minus_E' (identity_E' E1' E2'))) (minus_E' (R' 1))))
   (R' 0)
| ge_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  ge_E' E1 E2 ===> max_E' (add_E' (add_E' (R' 1) (minus_E' (abs_E' (division_E' (add_E' E2' (minus_E' E1'))
  (add_E' E2' E1')))))
   (add_E' (add_E' (R' 1) (minus_E' (abs_E' (division_E' (add_E' E2' (minus_E' E1'))
   (add_E' E2' E1'))))) (minus_E' (R' 1)))) 
  (R' 0)
| app_T : forall dom ran dom' ran' (E1 : Expr (dom --> ran)) E2 (E1' : Expr (dom' --> ran')) E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  app_E' E1 E2 ===> app_E' E1' E2'

  where "E1  ===> E2" := (translation E1 E2).

  (*Example*)

Lemma commutativity_add : forall E1 E2,
  add_E' E1 E2 = add_E' E2 E1.
Admitted.

Lemma associativity_add : forall E1 E2 E3,
  add_E' (add_E' E1 E2) E3 = add_E' E1 (add_E' E2 E3).
Admitted.

Print or_T.
Theorem commutativity_and : forall (E1 E2 : Expr (Simple_T Bool_T))  (B1 B2 : Expr (Simple_T Real_T)),
  (and_E' E1 E2 ===> B1) -> 
  (and_E' E2 E1 ===> B2) ->
  B1 = B2.
Proof.
  intros. inversion H. inversion H0. subst. dependent inversion H3.
  


Theorem commutativity_and : forall E1 E2 E1' E2', 
  
  (max_E' (add_E' E1' (add_E' E2' (minus_E' (R' 1)))) (R' 0)) = 
  (max_E' (add_E' E2' (add_E' E1' (minus_E' (R' 1)))) (R' 0)).
Proof.
  intros. 
  rewrite (commutativity_add E1' (add_E' E2' (minus_E' (R' 1)))). 
  rewrite (associativity_add E2' (minus_E' (R' 1))).
  rewrite <- (commutativity_add (minus_E' (R' 1)) E1').
  reflexivity.
Qed.

Theorem associativity_and : forall E1 E2 E3, 
  and_E' (and_E' E1 E2) E3 ===> and_E' E1 (and_E' E2 E3).
Proof.
  intros. 
  Admitted.





(*this one will need to be updated to add distance between vectors of some kind*)
Definition distance x1 x2 : Expr (Simple_T Real_T) :=
    add_E' x1 (minus_E' x2).

Definition bounded x1 x2 epsilon : Expr (Simple_T Bool_T) :=
    leq_E' (distance x1 x2 ) epsilon.

Definition robustness epsilon delta  x y f : Expr (Simple_T Bool_T) :=
    impl_E' (bounded x y epsilon) (bounded (app_E' f x) (app_E' f y) delta).



