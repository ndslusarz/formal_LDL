From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import sequences.

Import Num.Def Num.Theory GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive simple_type : Type :=
| Bool_T : simple_type
| Index_T : nat -> simple_type
| Real_T : simple_type
| Vector_T : nat -> simple_type
| Network_T : nat -> nat -> simple_type.

Inductive comparisons : Type :=
| le_E : comparisons
| lt_E : comparisons
| eq_E : comparisons
| neq_E : comparisons.

Inductive binary_logical : Type :=
| and_E : binary_logical
| or_E : binary_logical
| impl_E : binary_logical.

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

  (* networks and applications *)
  | net : forall n m : nat, (n.-tuple R -> m.-tuple R) -> expr (Network_T n m)
  | app_net : forall n m : nat, expr (Network_T n m) -> expr (Vector_T n) -> expr (Vector_T m)

  (*comparisons*)
  | comparisons_E : comparisons -> expr Real_T -> expr Real_T -> expr Bool_T
  (* | lookup_E v i: expr (Simple_T Vector_T) -> expr (Simple_T Index_T) -> expr (Simple_T Real_T) 
  I had this one before probably need to add this again, why did it get deleted?*)

  (*other - needed for DL translations*)
  | identity_E : expr Real_T -> expr Real_T -> expr Real_T.
End expr.

Notation "a /\ b" := (binary_logical_E and_E a b).
Notation "a \/ b" := (binary_logical_E or_E a b).
Notation "a `=> b" := (binary_logical_E impl_E a b) (at level 10).
Notation "`~ a" := (not_E a) (at level 10).
Notation "a `+ b" := (add_E a b) (at level 10).
Notation "a `* b" := (mult_E a b) (at level 10).
Notation "`- a" := (minus_E a) (at level 10).

Notation "a `<= b" := (comparisons_E le_E a b) (at level 10).
Notation "a `< b" := (comparisons_E lt_E a b) (at level 10).
Notation "a `>= b" := (comparisons_E le_E b a) (at level 10).
Notation "a `> b" := (comparisons_E lt_E b a) (at level 10).
Notation "a `== b" := (comparisons_E eq_E a b) (at level 10).
Notation "a `!= b" := (comparisons_E neq_E a b) (at level 10). (* TODO: fix levels *)

(*currently for Łukasiewicz*)

Definition type_translation (t: simple_type) : Type:=
  match t with
  | Bool_T => R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => (*R ^nat*) (*to do*) 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

Section defintion_of_the_translation.
Local Open Scope ring_scope.

Inductive LDL := Luk | God.

Parameter (l : LDL).

Reserved Notation "[[ e ]]".
Fixpoint translation t (e: expr t) : type_translation t :=
    match e in expr t return type_translation t with
    | Bool true => (1%R : type_translation Bool_T) 
    | Bool false => (0%R : type_translation Bool_T)
    | Real r => r%R
    | Index n i => i
    | Vector n t => t

    | E1 /\ E2 => maxr ([[ E1 ]] + [[ E2 ]] - 1)%R 0
    | E1 \/ E2 => minr ([[ E1 ]] + [[ E2 ]])%R 1
    | E1 `=> E2 => minr (1 - [[ E1 ]] + [[ E2 ]]) 1
    | `~ E1 => 1 - [[ E1 ]]

    (*simple arithmetic*)
    | E1 `+ E2 => [[ E1 ]] + [[ E2 ]]
    | E1 `* E2 => [[ E1 ]] * [[ E2 ]]
    | `- E1 => - [[ E1 ]]

    (*comparisons*)
    | E1 `== E2 => 1 - `|([[ E1 ]] - [[ E2 ]]) / ([[ E1 ]] + [[ E2 ]])|
    | E1 `<= E2 => 1 - maxr (([[ E1 ]] - [[ E2 ]]) / ([[ E1 ]] + [[ E2 ]])) 0
    | E1 `!= E2 => 1 - ([[ E1 ]] == [[ E2 ]])%:R
    | E1 `< E2 => maxr 
      ((1 - maxr (([[ E1 ]] - [[ E2 ]]) / ([[ E1 ]] + [[ E2 ]])) 0)
        + ([[ E1 ]] != [[ E2 ]])%:R - 1)
      0 
    | identity_E E1 E2 => ([[ E1 ]] == [[ E2 ]])%:R (* ale: where is this arising from? *)

    | net n m f => f
    | app_net n m f v => [[ f ]] [[ v ]]
    end
where "[[ e ]]" := (translation e).
End defintion_of_the_translation.

Notation "[[ e ]]_Luk" := (translation e) (at level 0).

(* Lemma lt_and_eq_0 : forall x : R,
  0 < x -> (0 = x) = False.
Proof.
intros. Search lt. Search (_ < _ -> _ != _).
rewrite lt0r_neq0.  *)

Section translation_lemmas.
Local Open Scope ring_scope.

Theorem commutativity_and (B1 B2 : expr Bool_T) :
  translation (B1 /\ B2) = translation (B2 /\ B1).
Proof.
by rewrite /= (addrC (_ B1)).
Qed.

(*Lemma translate_Bool_T_01 t (e : expr t) :
  0 <= (translation e : R) <= 1.
Proof.*)

Require Import Coq.Program.Equality.

Lemma translate_Bool_T_01 (e : expr Bool_T) :
  0 <= [[ e ]]_Luk <= 1.
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
