From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_ssreflect all_algebra ssralg ssrint ssrnum.
From mathcomp.analysis Require Import reals.
Require Export Coq.Strings.String.

(*Placeholder in a way - I need these to relate to actual Coq types (
  preferably some of them mathcomp. Believe they had reals there in some way,
  need to find out (as rings??? maybe)
). Not sure
what to do with Reals.*)
Inductive ty : Type :=
  | Bool_T : ty
  | Index_T : ty
  | Real_T : ty
  | Vector_T : ty
  | Arrow_T : ty -> ty -> ty.

  (*Just some parts of syntax, will expand if this is the correct approach*)
Inductive expr : Type :=
  | var : string -> expr
  | f : expr
  | r : expr
  | i : expr
  | b : expr
  | app : expr -> expr -> expr
  | lam : expr -> expr (*?*)
  | let_E : expr (*?*)
  | and_E : expr -> expr -> expr.

(*Notation*)
Declare Custom Entry ldl.
Notation "<{ e }>" := e (e custom ldl at level 99).
Notation "( x )" := x (in custom ldl, x at level 99).
Notation "x" := x (in custom ldl at level 0, x constr at level 0).
Notation "S -> T" := (Arrow_T S T) (in custom ldl at level 50, right associativity).
Notation "x y" := (app x y) (in custom ldl at level 1, left associativity).
Notation "x and_E y" := (and_E x y) (in custom ldl at level 50, right associativity).
Notation "\ x : t , y" :=
  (lam x t y) (in custom ldl at level 90, x at level 99,
                     t custom ldl at level 99,
                     y custom ldl at level 99,
                     left associativity).
Coercion var : string >-> expr.

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Notation "'Bool'" := Bool_T (in custom ldl at level 0).

(*Setp aka reduction - semantics here??*)
Reserved Notation "t '-->' t'" (at level 40).

(*Inductive step : expr -> expr -> Prop :=
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).*)


(*Partial and total map implementation from software foundation 
(is there a built in one?) - to move to another file*)

Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.
  Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).
Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).
                              
(*Notation for context gamme - should add network context? possibly?*)
Definition context := partial_map ty.
Reserved Notation "Gamma '|--' t '\in' T"
            (at level 101,
             t custom ldl, T custom ldl at level 0).
Print Grammar constr.
(*Typing relation setup*)
Inductive has_type : context -> expr -> ty -> Prop :=
  | T_x : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_and_E : forall Gamma t1 t2,
      Gamma |-- t1 \in Bool_T ->
      Gamma |-- t2 \in Bool_T
  | T_app : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

(*Then I suppose proof of the typing relation?
*)

Example typing_example_x :
  empty |-- \x:Bool, x \in (Bool -> Bool).
Proof. eauto. Qed.

Example typing_example_and :
  empty |-- \x:Bool, \y:Bool, x and_E y \in (Bool -> Bool).
Proof. auto.  Qed.

  (*Here go semantics, likely something like:
  Inductive sem_step : expr -> ?Prop? :=*)




