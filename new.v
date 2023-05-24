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
| Vector_T : simple_type
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
| neq : comparisons.

Section expr.
  Variable var : type -> Type.
  Variable net : type -> Type.

  Inductive expr : type -> Type :=
  | R : nat -> expr (Simple_T Real_T) (*temporary, couldn't get real to typecheck*)
  | I : nat -> expr (Simple_T Index_T)
  | B : bool -> expr (Simple_T Bool_T)

  | Var : forall t, var t -> expr t
  | Net : nat -> nat -> expr (Simple_T Network_T)

  (*logical connectives*)
  | and_E : expr (Simple_T Bool_T) -> expr (Simple_T Bool_T) -> expr (Simple_T Bool_T)
  | or_E : expr (Simple_T Bool_T) -> expr (Simple_T Bool_T) -> expr (Simple_T Bool_T)
  | impl_E : expr (Simple_T Bool_T) -> expr (Simple_T Bool_T) -> expr (Simple_T Bool_T)
  | not_E : expr (Simple_T Bool_T) -> expr (Simple_T Bool_T)

  (*arithmetic operations*)
  | add_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | mult_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | minus_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T)

  (*quantifiers*)
  | forall_E: forall t, expr t -> expr (Simple_T Bool_T)(*is there a way to exclue arrow type?*)
  | exists_E: forall t, expr t -> expr (Simple_T Bool_T)

  (*comparisons*)
  | comparisons_E : comparisons -> expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Bool_T)
  
  | app_E : forall t1 t2, expr (t1 --> t2) -> expr (Simple_T t1) -> expr t2
  | lam_E : forall (t1 : simple_type) t2, (var (Simple_T t1) -> expr t2) -> expr (t1 --> t2)
  | let_E : forall (t1 : simple_type) t2, (expr (Simple_T t1)) -> expr (t1 --> t2) -> expr t2
  | lookup_E : expr (Simple_T Vector_T) -> expr (Simple_T Index_T) -> expr (Simple_T Real_T)

  (*other - needed for DL translations*)
  | abs_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | max_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | min_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T)
  | identity_E : expr (Simple_T Real_T) -> expr (Simple_T Real_T) -> expr (Simple_T Real_T).

End expr.


(*Declare Custom Entry ldl.
Notation "S -> T" := (Arrow_T S T) (in custom ldl at level 50, right associativity).
Notation "x y" := (app x y) (in custom ldl at level 1, left associativity).
Notation "x + y" := (add_E x y) (in custom ldl at level 50, right associativity).
Notation "x * y" := (mult_E x y) (in custom ldl at level 50, right associativity).*)

(*adding implicit arguments*)
Arguments Var [var t].
Arguments R [var].
Arguments I [var].
Arguments B [var].
Arguments add_E [var].
Arguments mult_E [var].
Arguments minus_E [var].
Arguments and_E [var].
Arguments or_E [var].
Arguments impl_E [var].
Arguments not_E [var].
Arguments comparisons_E [var].
Arguments app_E [var t1 t2].
Arguments lam_E [var t1 t2].
Arguments let_E [var t1 t2].
Arguments abs_E [var].
Arguments max_E [var].
Arguments min_E [var].
Arguments identity_E [var].

Definition Expr t := forall var, expr var t.

(*making some notation easier - basic*)
Definition R' (n : nat) : Expr (Simple_T Real_T) :=
  fun _ => R n.
Definition I' (n : nat) : Expr (Simple_T Index_T) :=
fun _ => I n.
Definition B' (n : bool) : Expr (Simple_T Bool_T) :=
fun _ => B n.
(*minor tests*)
Example zeroR := R' 0.
Example zero := I' 0.
Example tr := B' true.

(*making some notation easier - arithmetic and logical*)
Definition add_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T) :=
  fun _ => add_E (e1 _) (e2 _).
Definition mult_E' (e1 e2 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T ):=
  fun _ => mult_E (e1 _) (e2 _).
Definition minus_E' (e1 : Expr (Simple_T Real_T)) : Expr (Simple_T Real_T) :=
  fun _ => minus_E (e1 _).


Definition leq_E' (e1 e2 : Expr Real_T) : Expr Bool_T :=
  fun _ => leq_E (e1 _) (e2 _).
Definition le_E' (e1 e2 : Expr Real_T) : Expr Bool_T :=
  fun _ => le_E (e1 _) (e2 _).
Definition geq_E' (e1 e2 : Expr Real_T) : Expr Bool_T :=
  fun _ => geq_E (e1 _) (e2 _).
Definition ge_E' (e1 e2 : Expr Real_T) : Expr Bool_T :=
  fun _ => ge_E (e1 _) (e2 _).
Definition eq_E' (e1 e2 : Expr Real_T) : Expr Bool_T :=
  fun _ => eq_E (e1 _) (e2 _).
Definition neq_E' (e1 e2 : Expr Real_T) : Expr Bool_T :=
  fun _ => neq_E (e1 _) (e2 _).

Definition and_E' (e1 e2 : Expr Bool_T) : Expr Bool_T :=
    fun _ => and_E (e1 _) (e2 _).
Definition or_E' (e1 e2 : Expr Bool_T) : Expr Bool_T :=
    fun _ => or_E (e1 _) (e2 _).
Definition impl_E' (e1 e2 : Expr Bool_T) : Expr Bool_T :=
    fun _ => impl_E (e1 _) (e2 _).
Definition not_E' (e : Expr Bool_T) : Expr Bool_T :=
    fun _ => not_E (e _).

Definition abs_E' (e1 : Expr Real_T) : Expr Real_T :=
    fun _ => abs_E (e1 _).
Definition max_E' (e1 e2 : Expr Real_T) : Expr Real_T :=
  fun _ => max_E (e1 _) (e2 _).
Definition min_E' (e1 e2 : Expr Real_T) : Expr Real_T :=
  fun _ => min_E (e1 _) (e2 _).
Definition identity_E' (e1 e2 : Expr Real_T) : Expr Real_T :=
    fun _ => identity_E (e1 _) (e2 _).

(*small tests*)
Example zero_add :=  add_E' zeroR zeroR.
Example true_and := and_E' tr tr.
Example eq_zero := eq_E' zeroR zeroR.

(*making notation easier - application*)
Definition app_E' t1 t2 (F : Expr (t1 --> t2)) (X : Expr t1) : Expr t2 :=
  fun _ => app_E (F _) (X _).


(*making notation easier - lambdas*)
Definition Expr1 t1 t2 := forall var, var t1 -> expr var t2.
Definition lam_E' t1 t2 (B : Expr1 t1 t2) : Expr (t1 --> t2) :=
  fun _ => lam_E (B _).

(*making notation easier - let*)
Definition Expr2 t1 t2 := forall var, expr var (t1 --> t2).
Definition let_E' t1 t2 (A: Expr t1) (B : Expr2 t1 t2) : Expr t2 :=
  fun _ => let_E (A _) (B _).

(*-------------------------------------------------------------------------------
SEMANTICS*)

(*DLs - add more later*)
Inductive DL : Type :=
| DL2 : DL
| Godel : DL.

Inductive semantic_type : Type :=
| Index_T' : semantic_type
| Real_T' : semantic_type
| Vector_T' : semantic_type
| Network_T' : semantic_type
| Arrow_T' : semantic_type -> semantic_type -> semantic_type.

Fixpoint translation_type (t : type) : type :=
  match t with
    | Index_T => Index_T
    | Bool_T => Real_T
    | Vector_T => Vector_T
    | Network_T => Network_T
    | Arrow_T t1 t2 => Arrow_T (translation_type t1) (translation_type t2)
    | Real_T => Real_T
  end.

Reserved Notation "E1 ===> E2" (no associativity, at level 90).

(*currently for DL2*)
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
  and_E' E1 E2 ===> 
  (*and_E' E1 E2 ===> add_E' E1' E2'*)
| or_T : forall E1 E2 E1' E2',
  E1 ===> E1' ->
  E2 ===> E2' ->
  and_E' E1 E2 ===> minus_E' (mult_E' E1' E2')

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
  leq_E' E1 E2 ===> minus_E' (max_E' (add_E' E1' (minus_E' E2')) (R' 0))
| eq_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  leq_E' E1 E2 ===> minus_E' (abs_E' (add_E' E1' (minus_E' E2')))
| neq_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  neq_E' E1 E2 ===> identity_E' E1' E2'
| geq_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  geq_E' E1 E2 ===> minus_E' (max_E' (add_E' E2' (minus_E' E1')) (R' 0))
| le_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  le_E' E1 E2 ===> add_E' (minus_E' (max_E' (add_E' E1' (minus_E' E2')) (R' 0))) (identity_E' E1' E2')
| ge_T : forall E1 E2 E1' E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  ge_E' E1 E2 ===> add_E' (minus_E' (max_E' (add_E' E2' (minus_E' E1')) (R' 0))) (identity_E' E1' E2')

| app_T : forall dom ran dom' ran' (E1 : Expr (dom --> ran)) E2 (E1' : Expr (dom' --> ran')) E2' ,
  E1 ===> E1' ->
  E2 ===> E2' ->
  app_E' E1 E2 ===> app_E' E1' E2'
| let_T : forall dom ran dom' ran' E1 (E2: Expr (dom --> ran)) E1' (E2': Expr (dom' --> ran')),
  E1 ===> E1' ->
  E2 ===> E2' ->
  let_E' E1 E2 ===> let_E' E1' E2'
| lam_T : forall dom ran dom' ran' (E1 : Expr1 dom ran)
 (E1' : Expr1 dom' ran'),
  lam_E' E1 ===> lam_E' E1' 
  

  where "E1  ===> E2" := (translation E1 E2).


  (*

  | Var : forall t, var t -> expr t
  | Net : nat -> nat -> expr Network_T

  (*quantifiers*)
  | forall_E: forall t, expr t -> expr Bool_T(*is there a way to exclue arrow type?*)
  | exists_E: forall t, expr t -> expr Bool_T

  
  | lam_E : forall t1 t2, (var t1 -> expr t2) -> expr (t1 --> t2)
  | lookup_E : expr Vector_T -> expr Index_T -> expr Real_T.*)

