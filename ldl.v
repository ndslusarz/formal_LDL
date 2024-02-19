From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import util.

(**md**************************************************************************)
(* # Logics                                                                   *)
(*                                                                            *)
(* ## Definitions                                                             *)
(* - err_vec i with i : 'I_n.+1                                               *)
(*   a vector $\delta_i$ with $1$ at index $i$ and $0$ elsewhere              *)
(* - ('d f '/d i) a with f : rV[R]_n.+1 -> R                                  *)
(*   $\lim_{h\to 0, h\neq 0} \frac{f(a + h\delta_i) - f(a)}{h}$               *)
(* - shadow_lifting f with f : rV[R]_n.+1 -> R                                *)
(*   $\forall p, p > 0 \to \forall i, \frac{d\,f}{d\,x_i} [p; \cdots; p] > 0$ *)
(* - product_and v with v : 'rV_n                                             *)
(*   $\Pi_{i < n} v_i$                                                        *)
(* - dl2_and v with v : 'rV_n                                                 *)
(*   $\sum_{i < n} v_i$                                                       *)
(*                                                                            *)
(* ## Properties                                                              *)
(* - satisfy shadow_lifting:                                                  *)
(*   + product_and                                                            *)
(*   + dl2_and                                                                *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Reserved Notation "{[ e ]}" (format "{[  e  ]}").
Reserved Notation "[[ e ]]b" (at level 10, format "[[  e  ]]b").
Reserved Notation "[[ e ]]_ l" (at level 10, format "[[ e ]]_ l").
Reserved Notation "nu .-[[ e ]]_stl" (at level 10, format "nu .-[[ e ]]_stl").
Reserved Notation "nu .-[[ e ]]_stl'" (at level 10, format "nu .-[[ e ]]_stl'").
Reserved Notation "[[ e ]]_dl2" (at level 10, format "[[ e ]]_dl2").
Reserved Notation "[[ e ]]_dl2'" (at level 10, format "[[ e ]]_dl2'").

Inductive simple_type :=
| Bool_T of bool
| Index_T of nat
| Real_T
| Vector_T of nat
| Network_T of nat & nat.

Definition Bool_P := Bool_T false.
Definition Bool_N := Bool_T true.

Inductive comparisons : Type :=
| le_E : comparisons
| eq_E : comparisons.

Section expr.
Context {R : realType}.

Inductive expr : simple_type -> Type :=
  | Real : R -> expr Real_T
  | Bool : forall x, bool -> expr (Bool_T x)
  | Index : forall n : nat, 'I_n -> expr (Index_T n)
  | Vector : forall n : nat, n.-tuple R -> expr (Vector_T n)

  (*logical connectives*)
  | and_E : forall x, seq (expr (Bool_T x)) -> expr (Bool_T x)
  | or_E : forall x, seq (expr (Bool_T x)) -> expr (Bool_T x)
  | not_E : expr (Bool_N) -> expr (Bool_N)

  (*arithmetic operations*)
  | add_E : expr Real_T -> expr Real_T -> expr Real_T
  | mult_E : expr Real_T -> expr Real_T -> expr Real_T
  | minus_E : expr Real_T -> expr Real_T

  (* networks and applications *)
  | net : forall n m : nat, (n.-tuple R -> m.-tuple R) -> expr (Network_T n m)
  | app_net : forall n m : nat, expr (Network_T n m) -> expr (Vector_T n) -> expr (Vector_T m)
  | lookup_E n: expr (Vector_T n) -> expr (Index_T n) -> expr Real_T

  (*comparisons*)
  | comparisons_E : forall x, comparisons -> expr Real_T -> expr Real_T -> expr (Bool_T x).

End expr.

HB.instance Definition _ (R : realType) b :=
  @gen_eqMixin (@expr R (Bool_T b)).

Declare Scope ldl_scope.

Notation "a `/\ b" := (and_E [:: a; b]) (at level 45).
Notation "a `\/ b" := (or_E [:: a; b]) (at level 45).
Notation "a `=> b" := (or_E [:: (not_E a); b]) (at level 55).
Notation "`~ a" := (not_E a) (at level 75).
Notation "a `+ b" := (add_E a b) (at level 50).
Notation "a `* b" := (mult_E a b) (at level 40).
Notation "`- a" := (minus_E a) (at level 45).

Local Open Scope ldl_scope.

Notation "a `<= b" := (comparisons_E _ le_E a b) (at level 70).
Notation "a `== b" := (comparisons_E _ eq_E a b) (at level 70).
Notation "a `!= b" := (`~ (a == b)) (at level 70).
Notation "a `< b" := (a `<= b /\ a `!= b) (at level 70).
Notation "a `>= b" := (b `<= a) (at level 70).
Notation "a `> b" := (b `< a) (at level 70).

Lemma expr_ind' (R : realType) :
  forall P : forall s : simple_type, expr s -> Prop,
       (forall s : R, P Real_T (Real s)) ->
       (forall (b x : bool), P (Bool_T x) (Bool x b)) ->
       (forall (n : nat) (o : 'I_n), P (Index_T n) (Index o)) ->
       (forall (n : nat) (t : n.-tuple R), P (Vector_T n) (Vector t)) ->
       (forall b (l : seq (expr (Bool_T b))), List.Forall (fun x => P (Bool_T b) x) l -> P (Bool_T b) (and_E l)) ->
       (forall b (l : seq (expr (Bool_T b))), List.Forall (fun x => P (Bool_T b) x) l -> P (Bool_T b) (or_E l)) ->
       (forall e : expr (Bool_T true), P (Bool_T true) e -> P (Bool_T true) (`~ e)) ->
       (forall e : expr Real_T,
        P Real_T e -> forall e0 : expr Real_T, P Real_T e0 -> P Real_T (e `+ e0)) ->
       (forall e : expr Real_T,
        P Real_T e -> forall e0 : expr Real_T, P Real_T e0 -> P Real_T (e `* e0)) ->
       (forall e : expr Real_T, P Real_T e -> P Real_T (`- e)) ->
       (forall (n m : nat) (t : n.-tuple R -> m.-tuple R), P (Network_T n m) (net t)) ->
       (forall (n m : nat) (e : expr (Network_T n m)),
        P (Network_T n m) e ->
        forall e0 : expr (Vector_T n), P (Vector_T n) e0 -> P (Vector_T m) (app_net e e0)) ->
       (forall (n : nat) (e : expr (Vector_T n)),
        P (Vector_T n) e ->
        forall e0 : expr (Index_T n), P (Index_T n) e0 -> P Real_T (lookup_E e e0)) ->
       (forall (c : comparisons) (e : expr Real_T) b,
        P Real_T e -> forall e0 : expr Real_T, P Real_T e0 -> P (Bool_T b) (comparisons_E b c e e0)) ->
       forall (s : simple_type) (e : expr s), P s e.
Proof.
move => P H H0 H1 H2 H3 H4 H7 H8 H9 H10 H11 H12 H13 H14 s e.
revert e.
revert s.
fix F1 2.
intros.
destruct e.
  * apply H.
  * apply H0.
  * apply H1.
  * apply H2.
  * apply H3.
    induction l.
    + apply List.Forall_nil.
    + apply List.Forall_cons_iff.
      split.
      - apply F1.
      - apply IHl.
  * apply H4.
    induction l.
    + apply List.Forall_nil.
    + apply List.Forall_cons_iff.
      split.
      - apply F1.
      - apply IHl.
  * apply H7; eauto.
  * apply H8; eauto.
  * apply H9; eauto.
  * apply H10; eauto.
  * apply H11.
  * apply H12; eauto.
  * apply H13; eauto.
  * apply H14; eauto.
Qed.

Local Close Scope ldl_scope.

Inductive DL := Lukasiewicz | Yager | Godel | product.

Section type_translation.
Context {R : realType}.

Definition type_translation (t : simple_type) : Type:=
  match t with
  | Bool_T x => R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

Definition bool_type_translation (t : simple_type) : Type:=
  match t with
  | Bool_T x => bool
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
  end.

Definition dl2_type_translation (t : simple_type) : Type :=
  match t with
  | Bool_T x => \bar R (* TODO: this should b [-oo,0] *)
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

Definition stl_type_translation (t : simple_type) : Type:=
  match t with
  | Bool_T x => \bar R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

End type_translation.

Section bool_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint bool_translation t (e : @expr R t) : bool_type_translation t :=
  match e in expr t return bool_type_translation t with
  | Bool b x => x
  | Real r => r%R
  | Index n i => i
  | Vector n t => t

  | and_E b Es => foldr andb true (map (@bool_translation (Bool_T b)) Es)
  | or_E b Es => foldr orb false (map (@bool_translation (Bool_T b)) Es)
  | `~ E1 => ~~ << E1 >>

  (* arith *)
  | E1 `+ E2 => << E1 >> + << E2 >>
  | E1 `* E2 => << E1 >> * << E2 >>
  | `- E1 => - << E1 >>

  (*comparisons*)
  | E1 `== E2 => << E1 >> == << E2 >>
  | E1 `<= E2 => << E1 >> <= << E2 >>
  | net n m f => f
  | app_net n m f v => << f >> << v >>
  | lookup_E n v i => tnth << v >> << i >>
  end
where "<< e >>" := (bool_translation e).

Lemma bool_translation_andE b (Es : seq (expr (Bool_T b))) :
  bool_translation (and_E Es) = \big[andb/true]_(x <- Es) bool_translation x.
Proof. by rewrite /= foldrE big_map. Qed.

End bool_translation.

Notation "[[ e ]]b" := (bool_translation e) : ldl_scope.

Section goedel_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (l : DL) (p : R).

Fixpoint translation t (e: @expr R t) {struct e} : type_translation t :=
    match e in expr t return type_translation t with
    | Bool _ true => (1%R : type_translation (Bool_T _))
    | Bool _ false => (0%R : type_translation (Bool_T _))
    | Real r => r%R
    | Index n i => i
    | Vector n t => t

    | and_E b Es =>
        match l with
        | Lukasiewicz => maxr (sumR (map (@translation _) Es)- (size Es)%:R+1) 0
        | Yager => maxr (1 - ((sumR (map (fun E => (1 - ({[ E ]}: type_translation (Bool_T _)))`^p)%R Es))`^p^-1)) 0
        | Godel => minR (map (@translation _) Es)
        | product => prodR (map (@translation _) Es)
        end
    | or_E b Es =>
        match l with
        | Lukasiewicz => minr (sumR (map (@translation _) Es)) 1
        | Yager => minr ((sumR (map (fun E => ({[ E ]} : type_translation (Bool_T _))`^p) Es))`^p^-1) 1
        | Godel => maxR (map (@translation _) Es)
        | product => product_dl_prodR (map (@translation _) Es)
        end

    | `~ E1 => 1 - {[ E1 ]}

    (*simple arithmetic*)
    | E1 `+ E2 => {[ E1 ]} + {[ E2 ]}
    | E1 `* E2 => {[ E1 ]} * {[ E2 ]}
    | `- E1 => - {[ E1 ]}

    (*comparisons*)
    | E1 `== E2 => if {[ E1 ]} == -{[ E2 ]} then ({[ E1 ]} == {[ E2 ]})%:R else maxr (1 - `|({[ E1 ]} - {[ E2 ]}) / ({[ E1 ]} + {[ E2 ]})|) 0
    | E1 `<= E2 => if {[ E1 ]} == -{[ E2 ]} then ({[ E1 ]} <= {[ E2 ]})%R%:R else maxr (1 - maxr (({[ E1 ]} - {[ E2 ]}) / `|{[ E1 ]} + {[ E2 ]}|) 0) 0

    | net n m f => f
    | app_net n m f v => (translation f) (translation v)
    | lookup_E n v i => tnth (translation v) (translation i)
    end
where "{[ e ]}" := (translation e).

End goedel_translation.

Section dl2_translation.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint dl2_translation t (e : @expr R t) {struct e} : dl2_type_translation t :=
    match e in expr t return dl2_type_translation t with
    | Bool _ true => 0
    | Bool _ false => -oo
    | Real r => r
    | Index n i => i
    | Vector n t => t

    | and_E _ Es => sumE (map (@dl2_translation _) Es)
    | or_E _ Es => ((- 1) ^+ (length Es).+1)%:E *
                 \big[*%E/1%E]_(i <- map (@dl2_translation _) Es) i
    | `~ E1 => (+oo)%E (* FIX: this case is not covered by DL2 *)

    (*simple arithmetic*)
    | E1 `+ E2 => ({[ E1 ]} + {[ E2 ]})%R
    | E1 `* E2 => ({[ E1 ]} * {[ E2 ]})%R
    | `- E1 => (- {[ E1 ]})%R

    (*comparisons*)
    | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
    | E1 `<= E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)%:E

    | net n m f => f
    | app_net n m f v => {[ f ]} {[ v ]}
    | lookup_E n v i => tnth {[ v ]} {[ i ]}
    end
where "{[ e ]}" := (dl2_translation e).

End dl2_translation.
Notation "[[ e ]]_dl2" := (dl2_translation e) : ldl_scope.

Section dl2_translation_alt.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint dl2_translation_alt t (e : @expr R t) {struct e} : type_translation t :=
    match e in expr t return type_translation t with
    | Bool _ true => 0
    | Bool _ false => -1
    | Real r => r
    | Index n i => i
    | Vector n t => t

    | and_E _ Es => sumR (map (@dl2_translation_alt _) Es)
    | or_E _ Es => ((- 1) ^+ (length Es).+1) *
                     prodR (map (@dl2_translation_alt _) Es)
    | `~ E1 => 0 (* FIX: this case is not covered by DL2 *)

    (*simple arithmetic*)
    | E1 `+ E2 => ({[ E1 ]} + {[ E2 ]})%R
    | E1 `* E2 => ({[ E1 ]} * {[ E2 ]})%R
    | `- E1 => (- {[ E1 ]})%R

    (*comparisons*)
    | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)
    | E1 `<= E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)

    | net n m f => f
    | app_net n m f v => {[ f ]} {[ v ]}
    | lookup_E n v i => tnth {[ v ]} {[ i ]}
    end
where "{[ e ]}" := (dl2_translation_alt e).

End dl2_translation_alt.
Notation "[[ e ]]_dl2'" := (dl2_translation_alt e) : ldl_scope.

Section stl_translation.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (p : R) (nu : R).
Hypothesis p1 : (1 <= p)%R.
Hypothesis nu0 : (0 < nu)%R.

Fixpoint stl_translation t (e: expr t) : stl_type_translation t :=
    match e in expr t return stl_type_translation t with
    | Bool _ true => +oo
    | Bool _ false => -oo
    | Real r => r
    | Index n i => i
    | Vector n t => t

    | and_E _ Es =>
        let A := map (@stl_translation _) Es in
        let a_min: \bar R := foldr mine (+oo) A in
        let a'_i (a_i: \bar R) := (a_i - a_min) * (fine a_min)^-1%:E in
        if a_min == -oo then -oo
        else if a_min == +oo then +oo
        else if a_min < 0 then
          sumE (map (fun a => a_min * expeR (a'_i a) * expeR (nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * a'_i a)) A)))^-1%:E
        else if a_min > 0 then
          sumE (map (fun a => a * expeR (-nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
             else 0
    | or_E _ Es => (* TODO: double check *)
        let A := map (@stl_translation _) Es in
        let a_max: \bar R := foldr maxe (-oo)%E A in
        let a'_i (a_i: \bar R) := (a_max - a_i) * (fine a_max)^-1%:E  in
        if a_max == -oo then -oo
        else if a_max == +oo then +oo
        else if a_max > 0 then
          sumE (map (fun a => a_max * expeR (a'_i a) * expeR (nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
        else if a_max < 0 then
          sumE (map (fun a => a * expeR (-nu%:E * (a'_i a))) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
             else 0
    | `~ E1 => (- {[ E1 ]})%E

    (*simple arithmetic*)
    | E1 `+ E2 => ({[ E1 ]} + {[ E2 ]})%R
    | E1 `* E2 => ({[ E1 ]} * {[ E2 ]})%R
    | `- E1 => (- {[ E1 ]})%R

    (*comparisons*)
    | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
    | E1 `<= E2 => ({[ E2 ]} - {[ E1 ]})%:E(* (- maxr ({[ E1 ]} - {[ E2 ]}) 0)%:E *)

    | net n m f => f
    | app_net n m f v => {[ f ]} {[ v ]}
    | lookup_E n v i => tnth {[ v ]} {[ i ]}
    end
where "{[ e ]}" := (stl_translation e).

End stl_translation.

Notation "nu .-[[ e ]]_stl" := (stl_translation nu e) : ldl_scope.


Section stl_translation_alt.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (p : R) (nu : R).
Hypothesis p1 : (1 <= p)%R.
Hypothesis nu0 : (0 < nu)%R.


Definition a'_min {R : realType} (x : R) (xs : seq R) : R :=
  (x - foldr minr x xs) * (foldr minr x xs)^-1.
(*  (x - \big[minr/(nth 0 xs 0)]_(i <- xs) i) * (\big[minr/(nth 0 xs 0)]_(i <- xs) i)^-1.  *)

Definition a'_max {R : realType} (x : R) (xs : seq R) : R :=
  (foldr maxr x xs - x ) * (foldr maxr x xs)^-1.
(*  (\big[maxr/(nth 0 xs 0)]_(i <- xs) i - x) * (\big[maxr/(nth 0 xs 0)]_(i <- xs) i)^-1.  *)

Definition stl_and_gt0 (v : seq R) :=
  sumR (map (fun a => a * expR (-nu * (a'_min a v))) (v)) *
     (sumR (map (fun a => expR (nu * a'_min a v)) (v)))^-1.

Definition stl_and_lt0 (v : seq R) :=
  sumR (map (fun a => (foldr minr a (v)) * expR (a'_min a (v)) * expR (nu * a'_min a (v))) (v)) *
    (sumR (map (fun a => expR (nu * a'_min a (v))) (v)))^-1.

Definition stl_or_gt0 (v : seq R) := 
  sumR (map (fun a => (foldr maxr a (v)) * expR (a'_max a (v)) * expR (nu * a'_max a (v))) (v)) *
    (sumR (map (fun a => expR (nu * a'_max a (v))) (v)))^-1.

Definition stl_or_lt0 (v : seq R) := 
  sumR (map (fun a => a * expR (-nu * (a'_max a v))) (v)) *
     (sumR (map (fun a => expR (nu * a'_max a (v))) (v)))^-1 .

Fixpoint stl_translation_alt t (e: expr t) : type_translation t :=
    match e in expr t return type_translation t with
    | Bool _ true => 1
    | Bool _ false => -1
    | Real r => r
    | Index n i => i
    | Vector n t => t

    | and_E _ [::] => 1
    | and_E _ (e0::Es) =>
        let A := map (@stl_translation_alt _) Es in
        let a0 := @stl_translation_alt _ e0 in
        let a_min: R := foldr minr a0 A in
        (* let a'_i (a_i: R) :=  (a_i - a_min) * a_min^-1  in  *)
        if a_min < 0 then
            stl_and_lt0 (a0::A)  
          (* sumR (map (fun a => a_min * expR (a'_i a) * expR (nu * a'_i a)) (a0::A)) *
          (sumR (map (fun a => expR (nu * a'_i a)) (a0::A)))^-1 *)
        else if a_min > 0 then
            stl_and_gt0 (a0::A)  
          (* sumR (map (fun a => a * expR (-nu * a'_i a)) (a0::A)) *
          (sumR (map (fun a => expR (nu * (a'_i a))) (a0::A)))^-1  *)  
             else 0
    | or_E _ [::] => -1
    | or_E _ (e0::Es) => (* TODO: double check *)
        let A := map (@stl_translation_alt _) Es in
        let a0 := @stl_translation_alt _ e0 in
        let a_max: R := foldr maxr a0 A in
        (* let a'_i (a_i: R) := (a_max - a_i) * a_max^-1 in *)
        if a_max > 0 then
          stl_or_gt0 (a0::A)
          (* sumR (map (fun a => a_max * expR (a'_i a) * expR (nu * a'_i a)) (a0::A)) *
          (sumR (map (fun a => expR (nu * (a'_i a))) (a0::A)))^-1 *)
        else if a_max < 0 then
          stl_or_lt0 (a0::A)
          (* sumR (map (fun a => a * expR (-nu * (a'_i a))) (a0::A)) *
          (sumR (map (fun a => expR (nu * (a'_i a))) (a0::A)))^-1 *)
             else 0
    | `~ E1 => - {[ E1 ]}

    (*simple arithmetic*)
    | E1 `+ E2 => ({[ E1 ]} + {[ E2 ]})%R
    | E1 `* E2 => ({[ E1 ]} * {[ E2 ]})%R
    | `- E1 => (- {[ E1 ]})%R

    (*comparisons*)
    | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)
    | E1 `<= E2 => ({[ E2 ]} - {[ E1 ]})

    | net n m f => f
    | app_net n m f v => {[ f ]} {[ v ]}
    | lookup_E n v i => tnth {[ v ]} {[ i ]}
    end
where "{[ e ]}" := (stl_translation_alt e).

End stl_translation_alt.

Notation "nu .-[[ e ]]_stl'" := (stl_translation_alt nu e) : ldl_scope.

 (* Ale: disabled for now *)


(* this is already in MCA master *)
#[global] Hint Extern 0 (Filter (nbhs _^'+)) =>
  (apply: at_right_proper_filter) : typeclass_instances.

#[global] Hint Extern 0 (Filter (nbhs _^'-)) =>
  (apply: at_left_proper_filter) : typeclass_instances.

Section shadow_lifting.
Local Open Scope ring_scope.

Definition shadow_lifting {R : realType} n (f : 'rV_n.+1 -> R) :=
  forall p, p > 0 -> forall i, ('d f '/d i) (const_mx p) > 0.

(*Definition shadow_lifting {R : realType} (f : forall n, 'rV_n.1 -> R) :=
  (* forall Es : seq R, forall i : 'I_(size Es),
    (* (forall i, nth 0 Es i != 0) -> *) *)
    forall Es : seq R, forall i : 'I_(size Es), forall e : R,
    e != 0 (* (0 < e <= 1)  *)->
    0 < nth 0 Es i <= 1 ->
    (forall j, j != i -> nth 0 Es j = e) ->
    partial (f (size Es)) i (row_of_seq Es) > 0.

Lemma all_0_product_partial {R : realType} (Es : seq R) (i : 'I_(size Es)) :
  partial 0 i (row_of_seq Es) = 0.
(*I'm not sure if I don't need an additional assumption here*)
Proof.
apply/cvg_lim; first exact: Rhausdorff.
rewrite [X in X @ _ --> _](_ : _ = 0); first exact: (@cvg_cst R).
by apply/funext => r/=; rewrite /GRing.zero/=(*NB: I shouldn't do that*) subrr mulr0.
Qed.
*)
(*
About realfun.left_right_continuousP. *)

Definition row_of_seq {R : numDomainType} (s : seq R) : 'rV[R]_(size s) :=
  (\row_(i < size s) tnth (in_tuple s) i).

Definition dotmul {R : ringType} n (u v : 'rV[R]_n) : R := (u *m v^T)``_0.
Reserved Notation "u *d w" (at level 40).
Local Notation "u *d w" := (dotmul u w).

(* NB(rei): WIP *)
Definition gradient {R : realType} (n : nat) (f : 'rV_n.+1 -> R) a :=
  \row_(i < n.+1) ('d f '/d i) a.

(* NB(rei): main property of gradients? https://en.wikipedia.org/wiki/Gradient *)
Lemma gradientP {R : realType} (n : nat) (f : 'rV[R]_n.+1 -> R^o) (v : 'rV[R]_n.+1) :
  forall x : 'rV[R]_n.+1, (gradient f x) *d v = 'D_v f x.
Proof.
move=> x.
rewrite /gradient.
Admitted.

Definition weakly_smooth_cond {R : realType} {n : nat} (a : 'rV[R]_n.+1) :=
  let m := \big[minr/1(*def element*)]_i a``_i in
  forall i j, i != j -> a``_i != m /\ a``_j != m.

Definition weakly_smooth {R : realType} (n : nat) (f : 'rV[R]_n.+1 -> R) :=
  (forall a, {for a, continuous f}) /\
  (forall a, weakly_smooth_cond a -> {for a, continuous (gradient f)}).



End shadow_lifting.

