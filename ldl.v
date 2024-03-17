From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra.

(**md**************************************************************************)
(* # Logics                                                                   *)
(*                                                                            *)
(* ## Definitions                                                             *)
(* - product_dl_mul                                                           *)
(* - shadow_lifting f with f : rV[R]_n.+1 -> R                                *)
(*   $\forall p, p > 0 \to \forall i, \frac{d\,f}{d\,x_i} [p; \cdots; p] > 0$ *)
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
Reserved Notation "nu .-[[ e ]]_stle" (at level 10, format "nu .-[[ e ]]_stle").
Reserved Notation "nu .-[[ e ]]_stl" (at level 10, format "nu .-[[ e ]]_stl").
Reserved Notation "[[ e ]]_dl2e" (at level 10, format "[[ e ]]_dl2e").
Reserved Notation "[[ e ]]_dl2" (at level 10, format "[[ e ]]_dl2").

(* Polarity of formulas: pos allows only positive formulas, neg allows negation *)
Inductive polarity := pos | neg.

Inductive ldl_type :=
| Bool_T of polarity
| Index_T of nat
| Real_T
| Vector_T of nat
| Fun_T of nat & nat.

Definition Bool_P := Bool_T pos.
Definition Bool_N := Bool_T neg.

Inductive comparison : Type := cmp_le | cmp_eq.

Section expr.
Context {R : realType}.

Inductive expr : ldl_type -> Type :=
  (* base expressions *)
  | ldl_real : R -> expr Real_T
  | ldl_bool : forall p, bool -> expr (Bool_T p)
  | ldl_idx : forall n, 'I_n -> expr (Index_T n)
  | ldl_vec : forall n, n.-tuple R -> expr (Vector_T n)
  (* connectives *)
  | ldl_and : forall x, seq (expr (Bool_T x)) -> expr (Bool_T x)
  | ldl_or : forall x, seq (expr (Bool_T x)) -> expr (Bool_T x)
  | ldl_not : expr Bool_N -> expr Bool_N
  (* comparisons *)
  | ldl_cmp : forall x, comparison -> expr Real_T -> expr Real_T -> expr (Bool_T x)
  (* networks and applications *)
  | ldl_fun : forall n m, (n.-tuple R -> m.-tuple R) -> expr (Fun_T n m)
  | ldl_app : forall n m, expr (Fun_T n m) -> expr (Vector_T n) -> expr (Vector_T m)
  | ldl_lookup : forall n, expr (Vector_T n) -> expr (Index_T n) -> expr Real_T.

End expr.

HB.instance Definition _ (R : realType) b :=
  @gen_eqMixin (@expr R (Bool_T b)).

Declare Scope ldl_scope.
Context {R : realType}.

Notation "a `/\ b" := (ldl_and [:: a; b]) (at level 45).
Notation "a `\/ b" := (ldl_or [:: a; b]) (at level 45).
Notation "a `=> b" := (ldl_or [:: (ldl_not a); b]) (at level 55).
Notation "`~ a"    := (ldl_not a) (at level 75).
Let ldl_add := ldl_fun (fun (t : 2.-tuple R) => [tuple [tnth t 0] + [tnth t 1] ])%R.
Let ldl_mul := ldl_fun (fun (t : 2.-tuple R) => [tuple [tnth t 0] * [tnth t 1] ])%R.
Let ldl_sub := ldl_fun (fun (t : 2.-tuple R) => [tuple [tnth t 0] - [tnth t 1] ])%R.
Let ldl_opp := ldl_fun (fun (t : 1.-tuple R) => [tuple -[tnth t 0] ])%R.
Notation "a `+ b"  := (ldl_lookup (ldl_app ldl_add [tuple a b]) 0) (at level 50).
Notation "a `- b"  := (ldl_lookup (ldl_app ldl_sub [tuple a b]) 0) (at level 45).
Notation "a `* b"  := (ldl_lookup (ldl_app ldl_mul [tuple a b]) 0) (at level 40).
Notation "`- a"    := (ldl_lookup (ldl_app ldl_opp [tuple a]) 0) (at level 45).

Let ldl_norm_infty n := ldl_fun (fun (t : (n.+1).-tuple R) => [tuple \big[maxr/[tnth t 0] ]_(i <- t) i ])%R.
Notation "`|| t ||" := (ldl_lookup (ldl_norm_infty t) 0).
Notation "t `! n" := (ldl_lookup _ t n) (at level 55).

Local Open Scope ldl_scope.

Notation "a `<= b" := (ldl_cmp _ cmp_le a b) (at level 70).
Notation "a `== b" := (ldl_cmp _ cmp_eq a b) (at level 70).
Notation "a `!= b" := (`~ (a == b)) (at level 70).
Notation "a `< b"  := (a `<= b /\ a `!= b) (at level 70).
Notation "a `>= b" := (b `<= a) (at level 70).
Notation "a `> b"  := (b `< a) (at level 70).

Lemma expr_ind' (Real : realType) :
  forall P : forall s : ldl_type, expr s -> Prop,
    (forall s : Real, P Real_T (ldl_real s)) ->
    (forall (b : bool) p, P (Bool_T p) (ldl_bool p b)) ->
    (forall n (o : 'I_n), P (Index_T n) (ldl_idx o)) ->
    (forall n (t : n.-tuple Real), P (Vector_T n) (ldl_vec t)) ->
    (forall b (l : seq (expr (Bool_T b))), List.Forall (fun x => P (Bool_T b) x) l -> P (Bool_T b) (ldl_and l)) ->
    (forall b (l : seq (expr (Bool_T b))), List.Forall (fun x => P (Bool_T b) x) l -> P (Bool_T b) (ldl_or l)) ->
    (forall e : expr Bool_N, P Bool_N e -> P Bool_N (`~ e)) ->
    (* (forall e : expr Real_T, *)
    (*  P Real_T e -> forall e0 : expr Real_T, P Real_T e0 -> P Real_T (e `+ e0)) -> *)
    (* (forall e : expr Real_T, *)
    (*  P Real_T e -> forall e0 : expr Real_T, P Real_T e0 -> P Real_T (e `* e0)) -> *)
    (* (forall e : expr Real_T, P Real_T e -> P Real_T (`- e)) -> *)
    (forall (n m : nat) (t : n.-tuple Real -> m.-tuple Real), P (Fun_T n m) (ldl_fun t)) ->
    (forall (n m : nat) (e : expr (Fun_T n m)),
     P (Fun_T n m) e ->
     forall e0 : expr (Vector_T n), P (Vector_T n) e0 -> P (Vector_T m) (ldl_app e e0)) ->
    (forall (n : nat) (e : expr (Vector_T n)),
     P (Vector_T n) e ->
     forall e0 : expr (Index_T n), P (Index_T n) e0 -> P Real_T (ldl_lookup e e0)) ->
    (forall (c : comparison) (e : expr Real_T) b,
     P Real_T e -> forall e0 : expr Real_T, P Real_T e0 -> P (Bool_T b) (ldl_cmp b c e e0)) ->
    forall (s : ldl_type) (e : expr s), P s e.
Proof.
move => P H H0 H1 H2 H3 H4 H7 H11 H12 H13 H14 s e.
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
  * apply H14; eauto.
  * apply H11.
  * apply H12; eauto.
  * apply H13; eauto.
Qed.

Local Close Scope ldl_scope.

Inductive DL := Lukasiewicz | Yager | Godel | product.

Section type_translation.
Context {Real : realType}.

Definition type_translation (t : ldl_type) : Type:=
  match t with
  | Bool_T x => Real
  | Real_T => Real
  | Vector_T n => n.-tuple Real
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple Real -> m.-tuple Real
end.

Definition bool_type_translation (t : ldl_type) : Type:=
  match t with
  | Bool_T x => bool
  | Real_T => Real
  | Vector_T n => n.-tuple Real
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple Real -> m.-tuple Real
  end.

Definition ereal_type_translation (t : ldl_type) : Type :=
  match t with
  | Bool_T x => \bar Real
  | Real_T => Real
  | Vector_T n => n.-tuple Real
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple Real -> m.-tuple Real
end.

End type_translation.

Section bool_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {Real : realType}.

Fixpoint bool_translation {t} (e : @expr Real t) : bool_type_translation t :=
  match e in expr t return bool_type_translation t with
  | ldl_bool b x => x
  | ldl_real r => r%R
  | ldl_idx n i => i
  | ldl_vec n t => t

  | ldl_and b Es => \big[andb/true]_(i <- map bool_translation Es) i
  | ldl_or b Es => \big[orb/false]_(i <- map bool_translation Es) i
  | `~ E1 => ~~ << E1 >>

  (*comparisons*)
  | E1 `== E2 => << E1 >> == << E2 >>
  | E1 `<= E2 => << E1 >> <= << E2 >>
  | ldl_fun n m f => f
  | ldl_app n m f v => << f >> << v >>
  | ldl_lookup n v i => tnth << v >> << i >>
  end
where "<< e >>" := (bool_translation e).

End bool_translation.

Notation "[[ e ]]b" := (bool_translation e) : ldl_scope.

Definition product_dl_mul {R : numDomainType} (a b : R) := (a + b - a * b)%R.

Definition product_dl_prod {R : numDomainType} (s : seq R) :=
  (\big[product_dl_mul/0]_(i <- s) i)%R.

Section product_dl_mul.
Context {R : realDomainType}.
Local Open Scope ring_scope.

Local Notation "x * y" := (product_dl_mul x y).

Lemma product_dl_mul_01 (x y : R) : 0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= x * y <= 1.
Proof. by rewrite /product_dl_mul; nra. Qed.

Lemma product_dl_mul_seq_01 (T : eqType) (f : T -> R) (l0 : seq T) :
  (forall i, i \in l0 -> 0 <= f i <= 1) -> (0 <= \big[product_dl_mul/0]_(i <- l0) f i <= 1).
Proof.
elim: l0.
- by rewrite big_nil lexx ler01.
- move=> a l0 IH h.
  rewrite big_cons product_dl_mul_01 ?h ?mem_head//.
  apply: IH => i il0; apply: h.
  by rewrite in_cons il0 orbT.
Qed.

Lemma product_dl_mul_inv (x y : R) :
  0 <= x <= 1 -> 0 <= y <= 1 ->
  reflect (x = 1 \/ y = 1) (x * y == 1).
Proof.
by move=> x01 y01; apply: (iffP eqP); rewrite /product_dl_mul; nra.
Qed.

Lemma product_dl_prod_inv0 (x y : R) :
  0 <= x <= 1 -> 0 <= y <= 1 ->
  reflect (x = 0 /\ y = 0) (x * y == 0).
Proof.
by move=> x01 y01; apply: (iffP eqP); rewrite /product_dl_mul; nra.
Qed.

End product_dl_mul.

Section goedel_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (l : DL) (p : R).

Fixpoint translation {t} (e : @expr R t) {struct e} : type_translation t :=
   match e in expr t return type_translation t with
   | ldl_bool _ true => (1%R : type_translation (Bool_T _))
   | ldl_bool _ false => (0%R : type_translation (Bool_T _))
   | ldl_real r => r%R
   | ldl_idx n i => i
   | ldl_vec n t => t

   | ldl_and b Es =>
       match l with
       | Lukasiewicz => maxr (sumR (map translation Es) - (size Es)%:R+1) 0
       | Yager => maxr (1 - (sumR (map (fun E => (1 - ({[ E ]} : type_translation (Bool_T _)))`^p) Es))`^p^-1) 0
       | Godel => minR (map translation Es)
       | product => prodR (map translation Es)
       end
   | ldl_or b Es =>
       match l with
       | Lukasiewicz => minr (sumR (map translation Es)) 1
       | Yager => minr ((sumR (map (fun E => ({[ E ]} : type_translation (Bool_T _))`^p) Es))`^p^-1) 1
       | Godel => maxR (map translation Es)
       | product => product_dl_prod (map translation Es)
       end

    | `~ E1 => 1 - {[ E1 ]}

    (*comparisons*)
    | E1 `== E2 => if {[ E1 ]} == -{[ E2 ]} then ({[ E1 ]} == {[ E2 ]})%:R else maxr (1 - `|({[ E1 ]} - {[ E2 ]}) / ({[ E1 ]} + {[ E2 ]})|) 0
    | E1 `<= E2 => if {[ E1 ]} == -{[ E2 ]} then ({[ E1 ]} <= {[ E2 ]})%R%:R else maxr (1 - maxr (({[ E1 ]} - {[ E2 ]}) / `|{[ E1 ]} + {[ E2 ]}|) 0) 0

    | ldl_fun n m f => f
    | ldl_app n m f v => (translation f) (translation v)
    | ldl_lookup n v i => tnth (translation v) (translation i)
    end
where "{[ e ]}" := (translation e).

End goedel_translation.

Section dl2_ereal_translation.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint dl2_ereal_translation {t} (e : @expr R t) {struct e} : ereal_type_translation t :=
  match e in expr t return ereal_type_translation t with
  | ldl_bool _ true => 0
  | ldl_bool _ false => -oo
  | ldl_real r => r
  | ldl_idx n i => i
  | ldl_vec n t => t

  | ldl_and _ Es => sumE (map dl2_ereal_translation Es)
  | ldl_or _ Es => ((- 1) ^+ (size Es).+1)%:E * prodE (map dl2_ereal_translation Es)
  | `~ E1 => +oo (* default value, all lemmas are for negation-free formulas *)

  (*comparisons*)
  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
  | E1 `<= E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)%:E

  | ldl_fun n m f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_lookup n v i => tnth {[ v ]} {[ i ]}
  end
where "{[ e ]}" := (dl2_ereal_translation e).

End dl2_ereal_translation.
Notation "[[ e ]]_dl2e" := (dl2_ereal_translation e) : ldl_scope.

Section dl2_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint dl2_translation {t} (e : @expr R t) {struct e} : type_translation t :=
  match e in expr t return type_translation t with
  | ldl_bool _ true => 0
  | ldl_bool _ false => -1
  | ldl_real r => r
  | ldl_idx n i => i
  | ldl_vec n t => t

  | ldl_and _ Es => sumR (map dl2_translation Es)
  | ldl_or _ s => (- 1) ^+ (size s).+1 * prodR (map dl2_translation s)
  | `~ E1 => 0 (* default value, all lemmas are for negation-free formulas *)

  (*comparisons*)
  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)
  | E1 `<= E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)

  | ldl_fun n m f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_lookup n v i => tnth {[ v ]} {[ i ]}
end
where "{[ e ]}" := (dl2_translation e).

End dl2_translation.
Notation "[[ e ]]_dl2" := (dl2_translation e) : ldl_scope.

Section stl_ereal_translation.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (p : R) (nu : R).
Hypothesis p1 : (1 <= p)%R.
Hypothesis nu0 : (0 < nu)%R.

Definition mine_dev (x y : \bar R) : \bar R :=
  (x - y) * (fine y)^-1%:E.

Definition maxe_dev (x y : \bar R) : \bar R :=
  (x - y) * (fine x)^-1%:E.

Fixpoint stl_ereal_translation {t} (e : expr t) : ereal_type_translation t :=
  match e in expr t return ereal_type_translation t with
  | ldl_bool _ true => +oo
  | ldl_bool _ false => -oo
  | ldl_real r => r
  | ldl_idx n i => i
  | ldl_vec n t => t

  | ldl_and _ Es =>
      let A := map stl_ereal_translation Es in
      let a_min : \bar R := foldr mine +oo A in
      let a'_i (a_i : \bar R) := mine_dev a_i a_min in
      if a_min == -oo then -oo
      else if a_min == +oo then +oo
        else if a_min < 0 then
          sumE (map (fun a => a_min * expeR (a'_i a) * expeR (nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * a'_i a)) A)))^-1%:E
        else if a_min > 0 then
          sumE (map (fun a => a * expeR (-nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
        else 0
  | ldl_or _ Es =>
      let A := map stl_ereal_translation Es in
      let a_max : \bar R := foldr maxe -oo A in
      let a'_i (a_i : \bar R) := maxe_dev a_max a_i in
      if a_max == -oo then -oo
      else if a_max == +oo then +oo
        else if a_max > 0 then
          sumE (map (fun a => a_max * expeR (a'_i a) * expeR (nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
        else if a_max < 0 then
          sumE (map (fun a => a * expeR (-nu%:E * (a'_i a))) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
        else 0
  | `~ E1 => - {[ E1 ]}

  (*comparisons*)
  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
  | E1 `<= E2 => ({[ E2 ]} - {[ E1 ]})%:E(* (- maxr ({[ E1 ]} - {[ E2 ]}) 0)%:E *)

  | ldl_fun n m f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_lookup n v i => tnth {[ v ]} {[ i ]}
    end
where "{[ e ]}" := (stl_ereal_translation e).

End stl_ereal_translation.

Notation "nu .-[[ e ]]_stle" := (stl_ereal_translation nu e) : ldl_scope.

Definition min_dev {R : realType} (x : R) (s : seq R) : R :=
  let r := \big[minr/x]_(i <- s) i in (x - r) * r^-1.

Definition max_dev {R : realType} (x : R) (s : seq R) : R :=
  let r := \big[maxr/x]_(i <- s) i in (r - x) * r^-1.

Section stl_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (p : R) (nu : R).
Hypothesis p1 : (1 <= p)%R.
Hypothesis nu0 : (0 < nu)%R.

Definition stl_and_gt0 (v : seq R) :=
  sumR (map (fun a => a * expR (-nu * min_dev a v)) v) *
    (sumR (map (fun a => expR (-nu * min_dev a v)) v))^-1.

Definition stl_and_lt0 (v : seq R) :=
  sumR (map (fun a => (\big[minr/a]_(i <- v) i) *
                      expR (min_dev a v) * expR (nu * min_dev a v)) v) *
    (sumR (map (fun a => expR (nu * min_dev a v)) v))^-1.

Definition stl_or_gt0 (v : seq R) :=
  sumR (map (fun a => (\big[maxr/a]_(i <- v) i) *
                      expR (max_dev a v) * expR (nu * max_dev a v)) v) *
    (sumR (map (fun a => expR (nu * max_dev a v)) v))^-1.

Definition stl_or_lt0 (v : seq R) :=
  sumR (map (fun a => a * expR (-nu * (max_dev a v))) v) *
    (sumR (map (fun a => expR (nu * max_dev a (v))) v))^-1 .

Fixpoint stl_translation {t} (e : expr t) : type_translation t :=
  match e in expr t return type_translation t with
  | ldl_bool _ true => 1
  | ldl_bool _ false => -1
  | ldl_real r => r
  | ldl_idx n i => i
  | ldl_vec n t => t

  | ldl_and _ [::] => 1
  | ldl_and _ (e0 :: s) =>
      let A := map stl_translation s in
      let a0 := stl_translation e0 in
      let a_min : R := \big[minr/a0]_(i <- A) i in
      if a_min < 0 then
        stl_and_lt0 (a0 :: A)
      else if a_min > 0 then
        stl_and_gt0 (a0 :: A)
      else 0
  | ldl_or _ [::] => -1
  | ldl_or _ (e0 :: s) =>
      let A := map stl_translation s in
      let a0 := stl_translation e0 in
      let a_max: R := \big[maxr/a0]_(i <- A) i in
      if a_max > 0 then
        stl_or_gt0 (a0 :: A)
      else if a_max < 0 then
        stl_or_lt0 (a0 :: A)
      else 0
  | `~ E1 => - {[ E1 ]}

  (*comparisons*)
  | E1 `== E2 => - `| {[ E1 ]} - {[ E2 ]}|
  | E1 `<= E2 => {[ E2 ]} - {[ E1 ]}

  | ldl_fun n m f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_lookup n v i => tnth {[ v ]} {[ i ]}
  end
where "{[ e ]}" := (stl_translation e).

End stl_translation.

Notation "nu .-[[ e ]]_stl" := (stl_translation nu e) : ldl_scope.


(* this is already in MCA master *)
#[global] Hint Extern 0 (Filter (nbhs _^'+)) =>
  (apply: at_right_proper_filter) : typeclass_instances.

#[global] Hint Extern 0 (Filter (nbhs _^'-)) =>
  (apply: at_left_proper_filter) : typeclass_instances.

Section shadow_lifting.
Local Open Scope ring_scope.

Definition shadow_lifting {R : realType} n (f : 'rV_n.+1 -> R) :=
  forall p, p > 0 -> forall i, ('d f '/d i) (const_mx p) > 0.

(* TODO(rei): rm this comment? *)
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

(* NB(rei): not used *)
Definition gradient {R : realType} (n : nat) (f : 'rV_n.+1 -> R) a :=
  \row_(i < n.+1) ('d f '/d i) a.

Lemma gradientP {R : realType} (n : nat) (f : 'rV[R]_n.+1 -> R^o) (v : 'rV[R]_n.+1) :
  forall x : 'rV[R]_n.+1, (gradient f x) *d v = 'D_v f x.
Proof.
move=> x.
rewrite /gradient.
Abort.

Definition weakly_smooth_cond {R : realType} {n : nat} (a : 'rV[R]_n.+1) :=
  let m := \big[minr/1(*def element*)]_i a``_i in
  forall i j, i != j -> a``_i != m /\ a``_j != m.

Definition weakly_smooth {R : realType} (n : nat) (f : 'rV[R]_n.+1 -> R) :=
  (forall a, {for a, continuous f}) /\
  (forall a, weakly_smooth_cond a -> {for a, continuous (gradient f)}).

End shadow_lifting.
