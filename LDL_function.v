From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import order.
From mathcomp Require Import sequences reals exp.


Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.

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

Variable R : realType.

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
Notation "a `=> b" := (binary_logical_E impl_E a b) (at level 55).
Notation "`~ a" := (not_E a) (at level 75).
Notation "a `+ b" := (add_E a b) (at level 50).
Notation "a `* b" := (mult_E a b) (at level 40).
Notation "`- a" := (minus_E a) (at level 45).

Notation "a `<= b" := (comparisons_E le_E a b) (at level 70).
Notation "a `< b" := (comparisons_E lt_E a b) (at level 70).
Notation "a `>= b" := (comparisons_E le_E b a) (at level 70).
Notation "a `> b" := (comparisons_E lt_E b a) (at level 70).
Notation "a `== b" := (comparisons_E eq_E a b) (at level 70).
Notation "a `!= b" := (comparisons_E neq_E a b) (at level 70).
Notation "a `=== b" := (identity_E a b) (at level 70).

Section translation_def.
Local Open Scope ring_scope.


Definition type_translation (t: simple_type) : Type:=
  match t with
  | Bool_T => R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

Inductive DL := Lukasiewicz | Yager | Godel.
Variable (l : DL).
Parameter (p : R).
Parameter (p1 : 1 <= p).

Definition translation_binop op a1 a2 :=
  match l with
  | Lukasiewicz =>
      match op with
      | and_E => maxr (a1 + a2 - 1) 0
      | or_E => minr (a1 + a2) 1
      | impl_E => minr (1 - a1 + a2) 1
      end
  | Yager =>
      match op with
      | and_E => maxr (1 - ((1 - a1) `^ p + (1 - a2) `^ p) `^ (p^-1)) 0
      | or_E => minr ((a1 `^ p + a2 `^ p) `^ (p^-1)) 1
      | impl_E => minr (((1 - a1) `^ p + a2 `^ p) `^ (p^-1)) 1
      end
  | Godel =>
      match op with
      | and_E => minr a1 a2
      | or_E => maxr a1 a2
      | impl_E => maxr (1 - a1) a2
      end
  end.

Reserved Notation "[[ e ]]".
Fixpoint translation t (e: expr t) : type_translation t :=
    match e in expr t return type_translation t with
    | Bool true => (1%R : type_translation Bool_T)
    | Bool false => (0%R : type_translation Bool_T)
    | Real r => r%R
    | Index n i => i
    | Vector n t => t

    | binary_logical_E op E1 E2 => translation_binop op [[ E1 ]] [[ E2 ]]

    | `~ E1 => 1 - [[ E1 ]]

    (*simple arithmetic*)
    | E1 `+ E2 => [[ E1 ]] + [[ E2 ]]
    | E1 `* E2 => [[ E1 ]] * [[ E2 ]]
    | `- E1 => - [[ E1 ]]

    (*comparisons*)
    | E1 `== E2 => ([[ E1 ]] == [[ E2 ]])%:R(* 1 - `|([[ E1 ]] - [[ E2 ]]) / ([[ E1 ]] + [[ E2 ]])| *)
    | E1 `<= E2 => maxr (1 - maxr (([[ E1 ]] - [[ E2 ]]) / ([[ E1 ]] + [[ E2 ]])) 0) 0
    | E1 `!= E2 => 1 - ([[ E1 ]] == [[ E2 ]])%:R
    | E1 `< E2 => maxr 
      (maxr ((1 - maxr (([[ E1 ]] - [[ E2 ]]) / ([[ E1 ]] + [[ E2 ]])) 0)
        + ([[ E1 ]] != [[ E2 ]])%:R - 1) 0)
      0 
    | identity_E E1 E2 => ([[ E1 ]] == [[ E2 ]])%:R

    | net n m f => f
    | app_net n m f v => [[ f ]] [[ v ]]
    end
where "[[ e ]]" := (translation e).

End translation_def.

Notation "[[ e ]]_ l" := (translation l e) (at level 10).


Section translation_lemmas.
Local Open Scope ring_scope.

Lemma andC l e1 e2 :
  [[ e1 /\ e2 ]]_l = [[ e2 /\ e1 ]]_l.
Proof.
case: l.
- by rewrite /= (addrC (_ e1)).
- by rewrite /= (addrC (_ `^ _)).
- by rewrite /=/minr; repeat case: ifP; lra.
Qed.

Lemma orC l e1 e2 :
  [[ e1 \/ e2 ]]_l = [[ e2 \/ e1 ]]_l.
Proof.
case: l.
- by rewrite /= (addrC (_ e1)).
- by rewrite /= (addrC (_ `^ _)).
- by rewrite /=/maxr; repeat case: ifP; lra.
Qed.
Require Import Coq.Program.Equality.

Local Open Scope order_scope.
Lemma translate_Bool_T_01 l (e : expr Bool_T) :
  0 <= [[ e ]]_l <= 1.
Proof.
case: l.
dependent induction e => //=.
- by case: ifPn => //; lra.
- have := IHe1 e1 erefl JMeq_refl.
  have := IHe2 e2 erefl JMeq_refl.
  set t1 := _ e1.
  set t2 := _ e2.
  by rewrite /= /minr/maxr; case: b; case: ifP; lra.
- have := IHe e erefl JMeq_refl.
  set t := _ e.
  by lra.
- set t1 := _ e1.
  set t2 := _ e2.
  by case: c; rewrite /maxr; repeat case: ifP; try case: eqP; lra.
dependent induction e => //=.
- by case: ifPn => //; lra.
- have := IHe1 e1 erefl JMeq_refl.
  have := IHe2 e2 erefl JMeq_refl.
  set t1 := _ e1.
  set t2 := _ e2.
  by rewrite /= /minr/maxr; case: b; case: ifP; rewrite ?cprD ?oppr_le0 ?powR_ge0; lra.
- have := IHe e erefl JMeq_refl.
  set t := _ e.
  by lra.
- set t1 := _ e1.
  set t2 := _ e2.
  by case: c; rewrite /maxr; repeat case: ifP; try case: eqP; lra.
dependent induction e => //=.
- by case: ifPn => //; lra.
- have := IHe1 e1 erefl JMeq_refl.
  have := IHe2 e2 erefl JMeq_refl.
  set t1 := _ e1.
  set t2 := _ e2.
  by case: b; rewrite /minr/maxr; try case: ifP; try lra.
- have := IHe e erefl JMeq_refl.
  set t := _ e.
  by lra.
- set t1 := _ e1.
  set t2 := _ e2.
  by case: c; rewrite /maxr; repeat case: ifP; try case: eqP; lra.
Qed.

Lemma orA l e1 e2 e3 : (0 < p) -> 
  [[ (e1 \/ (e2 \/ e3)) ]]_l = [[ ((e1 \/ e2) \/ e3) ]]_l.
Proof.
move => p0.
have ? : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 l e1.
have := translate_Bool_T_01 l e2.
have := translate_Bool_T_01 l e3.
case: l => /=.
- set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  rewrite /minr.
  by repeat case: ifP; lra.
- set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  move => ht3 ht2 ht1.
  rewrite {2}/minr.
  case: ifPn => h1.
  {
    rewrite -powRrM mulVf ?p0 ?powRr1 ?addr_ge0 ?powR_ge0//.
    rewrite {1}/minr.
    case: ifPn => h2.
    {
      rewrite {2}/minr.
      case: ifPn => h3.
      {
        rewrite {1}/minr.
        case: ifPn => h4.
        by rewrite -{1}powRrM mulVf ?powRr1 ?addr_ge0 ?powR_ge0 ?addrA.
        rewrite addrA; move: h2; rewrite addrA; move: h4;
        rewrite -{1}powRrM mulVf ?powRr1 ?addr_ge0 ?powR_ge0//;
        lra.
      }
      {
        rewrite {1}/minr.
        - have: (t1 `^ p + (t2 `^ p + t3 `^ p)) `^ p^-1 >= (t1 `^ p + t2 `^ p) `^ p^-1.
          rewrite gt0_ler_powR//.
          + by rewrite invr_ge0 ltW.
          + by rewrite in_itv /= andbT addr_ge0// powR_ge0.
          + by rewrite in_itv /= andbT !addr_ge0// powR_ge0.
          + by rewrite lerD// lerDl powR_ge0.
            lra.
      }
    }
    {
      rewrite {2}/minr.
      case: ifPn => h3.
      {
        rewrite -{1}powRrM mulVf// powRr1 ?addr_ge0 ?powR_ge0//.
        rewrite {1}/minr.
        case: ifPn => // h4.
        move: h2. rewrite addrA. lra.
      }
      {
        rewrite {1}/minr.
        case: ifPn => //.
        have: (1 `^ p + t3 `^ p) `^ p^-1 >= 1.
        - have {1}->: 1 = 1 `^ p^-1 by rewrite powR1.
          rewrite gt0_ler_powR//.
          + by rewrite invr_ge0 ltW.
          + by rewrite in_itv /= andbT.
          + by rewrite in_itv /= addr_ge0// powR_ge0.
          by rewrite powR1 lerDl powR_ge0.
          set a := (1 `^ p + t3 `^ p) `^ p^-1.
          lra.
      }
    }
  }
  {
    rewrite {1}/minr.
    case: ifPn => // h2.
    {
      have: (t1 `^ p + 1 `^ p) `^ p^-1 >= 1.
      - have {1}->: 1 = 1`^p^-1 by rewrite powR1.
        rewrite gt0_ler_powR//.
        + by rewrite invr_ge0 ltW.
        + by rewrite in_itv /= andbT.
        + by rewrite in_itv /= addr_ge0// powR_ge0.
        by rewrite powR1 lerDr powR_ge0.
      move: h2.
      set a := (t1 `^ p + 1 `^ p) `^ p^-1.
      lra.
    }
    {
      rewrite {2}/minr.
      case: ifPn => h3.
      {
        rewrite {1}/minr.
        case: ifPn => //.
        rewrite -powRrM mulVf// powRr1.
        move=> h4.
        have h5: (t1 `^ p + t2 `^ p + t3 `^ p) `^ p^-1 >= (t2 `^ p + t3 `^ p) `^ p^-1.
        rewrite gt0_ler_powR//.
        + by rewrite invr_ge0 ltW.
        + by rewrite in_itv /= addr_ge0// powR_ge0.
        + by rewrite in_itv /= !addr_ge0// powR_ge0.
        by rewrite lerD// lerDr powR_ge0.
        lra.
        by rewrite addr_ge0 ?powR_ge0.
      }
      {
        rewrite {1}/minr.
        case: ifPn => //.
        have: (1 `^ p + t3 `^ p) `^ p^-1 >= 1.
        - have {1}->: 1 = 1`^p^-1 by rewrite powR1.
          rewrite gt0_ler_powR//.
          + by rewrite invr_ge0 ltW.
          + by rewrite in_itv /= andbT.
          + by rewrite in_itv /= addr_ge0// powR_ge0.
          by rewrite powR1 lerDl powR_ge0.
        set a := (1 `^ p + t3 `^ p) `^ p^-1.
        lra.
      }
    }
  }
- set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  rewrite /maxr.
  by repeat case: ifP; lra.
Qed.


Theorem andA l e1 e2 e3 : (0 < p) ->
  [[ (e1 /\ e2) /\ e3]]_l = [[ e1 /\ (e2 /\ e3) ]]_l.
Proof.
have := translate_Bool_T_01 l e1.
have := translate_Bool_T_01 l e2.
have := translate_Bool_T_01 l e3.
case: l => /=.
+ set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  rewrite /maxr.
  by repeat case: ifP; lra.
+ set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  rewrite {2}/maxr=> ht3 ht2 ht1.
  case: ifPn => [h1|].
  {
    rewrite subr0 {1}/maxr.
    case: ifPn => [h2|].
    {
      rewrite {2}/maxr.
      case: ifPn => [h3|].
      {
        rewrite subr0 {1}/maxr.
        case: ifPn => //.
        rewrite -leNgt subr_ge0 powR1.
        have {3}->: 1 = 1 `^ p^-1 by rewrite powR1.
        move=> h4.
        admit.
      }
      rewrite -leNgt => h3.
      {
        rewrite {1}/maxr.
        case: ifPn => //.
        rewrite -leNgt => h4.
        admit.
      }
    }
    rewrite -leNgt => h2.
    {
      rewrite {2}/maxr.
      case: ifPn => [h3|].
      {
        rewrite subr0 {1}/maxr.
        case: ifPn => [h4|].
        admit.
        rewrite -leNgt => h4.
        admit.
      }
      rewrite -leNgt => h3.
      {
        rewrite {1}/maxr.
        case: ifPn => [h4|].
        admit.
        rewrite -leNgt => h4.
        admit.
      }
    }
  }
  rewrite -leNgt => h1.
  {
    rewrite {1}/maxr.
    case: ifPn => [h2|].
    {
      rewrite {2}/maxr.
      case: ifPn => [h3|].
      rewrite subr0 powR1.
      {
        rewrite {1}/maxr.
        case: ifPn => //.
        rewrite -leNgt => h4.
        admit.
      }
      rewrite -leNgt => h3.
      {
        rewrite {1}/maxr.
        case: ifPn => //.
        rewrite -leNgt => h4.
        admit.
      }
    }
    rewrite -leNgt => h2.
    {
      rewrite {2}/maxr.
      case: ifPn => [h3|].
      {
        rewrite {1}/maxr.
        case: ifPn => [h4|].
        admit.
        rewrite -leNgt => h4.
        admit.
      }
      rewrite -leNgt => h3.
      {
        rewrite {1}/maxr.
        case: ifPn => [h4|].
        admit.
        rewrite -leNgt => h4.
        admit.
      }
    }
  }
+ set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  rewrite /minr.
  by repeat case: ifP; lra.
Admitted.

