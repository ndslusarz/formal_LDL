From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder finmap multiset.
Require Import mathcomp_extra analysis_extra.
From HB Require Import structures.

(**md**************************************************************************)
(* # Logics                                                                   *)
(*                                                                            *)
(* This file provides a formalization of the LDL language. The inductive type *)
(* `expr` defines the language itself, which is intrisically typed on the     *)
(* types defined by `ldl_type`. Boolean formulas take an argument of type     *)
(* `flag`: `def` allows negation in the expression, while `undef` disallows   *)
(* it.                                                                        *)
(*                                                                            *)
(* ## Definitions                                                             *)
(* - `type_translation`: the real-valued translation of ldl_type into the     *)
(*   corresponding type of the interpretation; maps `Bool_T` to $\mathbb R$   *)
(* - `ereal_type_translation`: same as before, but maps                       *)
(*   `Bool_T` to $\bar{\mathbb R}}$                                           *)
(* - `bool_type_translation`: type translation for the boolean interpretation;*)
(*   maps `Bool_T` to `bool`                                                  *)
(* - `bool_translation`: maps an LDL-formula to a Boolean formula, with the   *)
(*   obvious interpretation                                                   *)
(* - `translation`: maps an LDL-formula to its fuzzy interpretation;          *)
(*   takes as additional argument a parameter of type `DL` to specify the     *)
(*   logic, among `Lukasiewicz`, `Yager`, `Godel`, and `product`              *)
(* - `dl2_translation`: maps an LDL-formula to its interpretation in DL2,     *)
(*   mapping true to $0$ and false to $-1$                                    *)
(* - `dl2_ereal_translation`: maps an LDL-formula to its interpretation in    *)
(*   DL2 on extended reals, mapping true to $0$ and false to $-\infty$        *)
(* - `stl_translation`: maps an LDL-formula to its interpretation in STL,     *)
(*   mapping true to $1$ and false to $-1$                                    *)
(* - `stl_ereal_translation`: maps an LDL-formula to its interpretation in    *)
(*   STL on extended reals, mapping true to $\infty$ and false to $-\infty$   *)
(*                                                                            *)
(* ## Mathematical definitions:                                               *)
(* `shadow_lifting f` with `f : rV[R]_n.+1 -> R`                              *)
(*   $\forall p, p > 0 \to \forall i, \frac{d\,f}{d\,x_i} [p; \cdots; p] > 0$ *)
(*                                                                            *)
(*## Examples                                                                 *)
(* - example_eps_delta_robust - exanmple constraint -robustness - expressed   *)
(*   using the custom language of `expr`                                      *)
(* - example_hierarchichal - example group constraint expressed using the     *)
(*   custom language of `expr`                                                *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Reserved Notation "{[ e ]}" (format "{[  e  ]}").
Reserved Notation "[[ e ]]_B" (at level 10, format "[[  e  ]]_B").
Reserved Notation "[[ e ]]_ l" (at level 10, format "[[ e ]]_ l").
Reserved Notation "nu .-[[ e ]]_stle" (at level 10, format "nu .-[[ e ]]_stle").
Reserved Notation "nu .-[[ e ]]_stl" (at level 10, format "nu .-[[ e ]]_stl").
Reserved Notation "[[ e ]]_dl2e" (at level 10, format "[[ e ]]_dl2e").
Reserved Notation "[[ e ]]_dl2" (at level 10, format "[[ e ]]_dl2").

(* flags which allow or disallow certain logical connectives:
- negation
- implication
- monoidal and, or
- lattice and, or*)
Inductive flag_neg := neg_def | neg_undef.
Inductive flag_impl := impl_def | impl_undef.
Inductive flag_monoid := m_def | m_undef.
Inductive flag_lattice := l_def | l_undef.

Inductive ldl_type :=
| Bool_T of flag_neg & flag_impl & flag_monoid & flag_lattice
| Index_T of nat
| Real_T
| Vector_T of nat
| Fun_T of nat & nat
| Fun2_T of nat & nat & nat.

Definition Bool_T_undef := Bool_T neg_undef.
Definition Bool_T_def := Bool_T neg_def.

(*flags of the DLs*)
Definition Bool_T_fuzzy := Bool_T neg_def impl_def m_def l_def.
Definition Bool_T_dl2 := Bool_T neg_undef impl_def m_def l_undef.
Definition Bool_T_stl := Bool_T neg_def impl_undef m_undef l_def.

Inductive comparison : Type := cmp_le | cmp_eq.

Section expr.
Context {R : realType}.

Inductive expr : ldl_type -> Type :=
  (* base expressions *)
  | ldl_bool : forall p r s t, bool -> expr (Bool_T p r s t)
  | ldl_idx : forall n, 'I_n -> expr (Index_T n)
  | ldl_real : R -> expr Real_T
  | ldl_vec : forall n, n.-tuple R -> expr (Vector_T n)
  (* connectives *)
  | ldl_and : forall x y z, seq (expr (Bool_T x y z l_def)) -> expr (Bool_T x y z l_def)
  | ldl_or : forall x y z, seq (expr (Bool_T x y z l_def)) -> expr (Bool_T x y z l_def)
  | ldl_not : forall x y z, expr (Bool_T neg_def x y z) -> expr (Bool_T neg_def  x y z)
  | ldl_impl :forall x y z, expr (Bool_T x impl_def y z) -> expr (Bool_T x impl_def y z)
                            -> expr (Bool_T x impl_def y z)
  | ldl_mand : forall x y z, seq (expr (Bool_T x y m_def z)) -> expr (Bool_T x y m_def z)
  | ldl_mor : forall x y z, seq (expr (Bool_T x y m_def z)) -> expr (Bool_T x y m_def z)
  (* comparisons *)
  | ldl_cmp : forall x y z v, comparison -> expr Real_T -> expr Real_T -> expr (Bool_T x y z v)
  (* networks and applications *)
  | ldl_fun : forall n m, (n.-tuple R -> m.-tuple R) -> expr (Fun_T n m)
  | ldl_fun2 : forall n m l, (n.-tuple R -> m.-tuple R -> l.-tuple R) -> expr (Fun2_T n m l)
  | ldl_app : forall n m, expr (Fun_T n m) -> expr (Vector_T n) -> expr (Vector_T m)
  | ldl_app2 : forall n m l, expr (Fun2_T n m l) -> expr (Vector_T n) -> expr (Vector_T m) -> expr (Vector_T l)
  | ldl_lookup : forall n, expr (Vector_T n) -> expr (Index_T n) -> expr Real_T.

End expr.

Declare Scope ldl_scope.

Notation "a `/\ b" := (ldl_and [:: a; b]) (at level 45).
Notation "a `\/ b" := (ldl_or [:: a; b]) (at level 45).
Notation "a `** b" := (ldl_mand [:: a; b]) (at level 45).
Notation "a `++ b" := (ldl_mor [:: a; b]) (at level 45).
Notation "a `=> b" := (ldl_impl a b) (at level 55).
(*Notation "a `=> b" := (ldl_or [:: (ldl_not a); b]) (at level 55).*)
Notation "`~ a"    := (ldl_not a) (at level 75).
Definition ldl_add (R : realType) := ldl_fun (fun (t : 2.-tuple R) => [tuple [tnth t 0] + [tnth t 1] ])%R.
Definition ldl_mul {R : realType} := ldl_fun (fun (t : 2.-tuple R) => [tuple [tnth t 0] * [tnth t 1] ])%R.
Definition ldl_sub {R : realType} := ldl_fun (fun (t : 2.-tuple R) => [tuple [tnth t 0] - [tnth t 1] ])%R.
Definition ldl_opp {R : realType}  := ldl_fun (fun (t : 1.-tuple R) => [tuple -[tnth t 0] ])%R.
Notation "a `+ b"  := (ldl_lookup (ldl_app ldl_add [tuple a; b]) 0) (at level 50).
Notation "a `- b"  := (ldl_lookup (ldl_app ldl_sub [tuple a; b]) 0) (at level 45).
Notation "a `* b"  := (ldl_lookup (ldl_app ldl_mul [tuple a; b]) 0) (at level 40).
Notation "`- a"    := (ldl_lookup (ldl_app ldl_opp [tuple a]) 0) (at level 45).

Local Open Scope ldl_scope.

Notation "a `<= b" := (ldl_cmp _ _ _ _ cmp_le a b) (at level 70).
Notation "a `== b" := (ldl_cmp _ _ _ _ cmp_eq a b) (at level 70).
Notation "a `!= b" := (`~ (a == b)) (at level 70).
Notation "a `< b"  := (a `<= b /\ a `!= b) (at level 70).
Notation "a `>= b" := (b `<= a) (at level 70).
Notation "a `> b"  := (b `< a) (at level 70).
Notation "a `! b"  := (ldl_lookup a b). 

Check expr_ind.

Lemma expr_ind' (R : realType) :
  forall P : forall l : ldl_type, expr l -> Prop,
       (forall (p : flag_neg) (r : flag_impl) (s : flag_monoid) (t : flag_lattice) (b : bool),
        P (Bool_T p r s t) (ldl_bool p r s t b)) ->
       (forall (n : nat) (o : 'I_n), P (Index_T n) (ldl_idx o)) ->
       (forall s : R, P Real_T (ldl_real s)) ->
       (forall (n : nat) (t : n.-tuple R), P (Vector_T n) (ldl_vec t)) ->
       (forall (x : flag_neg) (y : flag_impl) (z : flag_monoid) (l : seq (expr (Bool_T x y z l_def))),
          List.Forall (fun a => P (Bool_T x y z l_def) a) l -> P (Bool_T x y z l_def) (ldl_and l)) ->
       (forall (x : flag_neg) (y : flag_impl) (z : flag_monoid) (l : seq (expr (Bool_T x y z l_def))),
        List.Forall (fun a => P (Bool_T x y z l_def) a) l -> P (Bool_T x y z l_def) (ldl_or l)) ->
       (forall (x : flag_impl) (y : flag_monoid) (z : flag_lattice) (e : expr (Bool_T_def x y z)),
        P (Bool_T_def x y z) e -> P (Bool_T_def x y z) (ldl_not e)) ->
       (forall (x : flag_neg) (y : flag_monoid) (z : flag_lattice) (e : expr (Bool_T x impl_def y z)),
        P (Bool_T x impl_def y z) e ->
        forall e0 : expr (Bool_T x impl_def y z),
        P (Bool_T x impl_def y z) e0 -> P (Bool_T x impl_def y z) (ldl_impl e e0)) ->
       (forall (x : flag_neg) (y : flag_impl) (z : flag_lattice) (l : seq (expr (Bool_T x y m_def z))),
          List.Forall (fun a => P (Bool_T x y m_def z) a) l -> P (Bool_T x y m_def z) (ldl_mand l)) ->
       (forall (x : flag_neg) (y : flag_impl) (z : flag_lattice) (l : seq (expr (Bool_T x y m_def z))),
        List.Forall (fun a => P (Bool_T x y m_def z) a) l -> P (Bool_T x y m_def z) (ldl_mor l)) ->
       (forall (x : flag_neg) (y : flag_impl) (z : flag_monoid) (v : flag_lattice) 
          (c : comparison) (e : expr Real_T),
        P Real_T e -> forall e0 : expr Real_T, P Real_T e0 -> P (Bool_T x y z v) (ldl_cmp x y z v c e e0)) ->
       (forall (n m : nat) (t : n.-tuple R -> m.-tuple R), P (Fun_T n m) (ldl_fun t)) ->
       (forall (n m l : nat) (t : n.-tuple R -> m.-tuple R -> l.-tuple R), P (Fun2_T n m l) (ldl_fun2 t)) ->
       (forall (n m : nat) (e : expr (Fun_T n m)),
        P (Fun_T n m) e -> forall e0 : expr (Vector_T n), P (Vector_T n) e0 -> P (Vector_T m) (ldl_app e e0)) ->
       (forall (n m l : nat) (e : expr (Fun2_T n m l)),
        P (Fun2_T n m l) e -> forall (e0 : expr (Vector_T n)) (e1 : expr (Vector_T m)), P (Vector_T n) e0 -> P (Vector_T m) e1 -> P (Vector_T l) (ldl_app2 e e0 e1)) ->
       (forall (n : nat) (e : expr (Vector_T n)),
        P (Vector_T n) e -> forall e0 : expr (Index_T n), P (Index_T n) e0 -> P Real_T (ldl_lookup e e0)) ->
       forall (l : ldl_type) (e : expr l), P l e.
Proof.
move => P H H0 H1 H2 H3 H4 H7 H11 H12 H13 H14 H15 H16 H17 H18 H19 s e.
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
  * apply H11; eauto.
  * apply H12.
    induction l.
    + apply List.Forall_nil.
    + apply List.Forall_cons_iff.
      split.
      - apply F1.
      - apply IHl.
  * apply H13.
    induction l.
    + apply List.Forall_nil.
    + apply List.Forall_cons_iff.
      split.
      - apply F1.
      - apply IHl.
  * apply H14; eauto.
  * apply H15; eauto.
  * apply H16; eauto.
  * apply H17; eauto.
  * apply H18; eauto.
  * apply H19; eauto.
Qed.

Local Close Scope ldl_scope.

Inductive DL := Lukasiewicz | Yager | Godel | product | GodelS | productS.

Section type_translation.
Context {R : realType}.

Definition type_translation (t : ldl_type) : Type:=
  match t with
  | Bool_T x y z v  => R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
  | Fun2_T n m l => n.-tuple R -> m.-tuple R -> l.-tuple R
end.

Definition bool_type_translation (t : ldl_type) : Type:=
  match t with
  | Bool_T x y z v=> bool
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
  | Fun2_T n m l => n.-tuple R -> m.-tuple R -> l.-tuple R
  end.

Definition ereal_type_translation (t : ldl_type) : Type :=
  match t with
  | Bool_T x y z v=> \bar R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
  | Fun2_T n m l => n.-tuple R -> m.-tuple R -> l.-tuple R
end.

End type_translation.

Section bool_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint bool_translation {t} (e : @expr R t) : bool_type_translation t :=
  match e in expr t return bool_type_translation t with
  | ldl_bool f1 f2 f3 f4 x => x
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and f1 f2 f3  Es => \big[andb/true]_(i <- map bool_translation Es) i
  | ldl_or f1 f2 f3  Es => \big[orb/false]_(i <- map bool_translation Es) i
  | ldl_not f2 f3 f4  E1 => ~~ << E1 >>
  | ldl_impl f1 f3 f4 E1  E2 => << E1 >> ==> << E2>>
  | ldl_mand f1 f2 f4  Es => \big[andb/true]_(i <- map bool_translation Es) i
  | ldl_mor f1 f2 f4  Es => \big[orb/false]_(i <- map bool_translation Es) i

  | E1 `== E2 => << E1 >> == << E2 >>
  | E1 `<= E2 => << E1 >> <= << E2 >>

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => << f >> << v >>
  | ldl_app2 n m l f v1 v2 => << f >> << v1 >> << v2 >>
  | ldl_lookup n v i => tnth << v >> << i >>
  end
where "<< e >>" := (bool_translation e).

End bool_translation.

Notation "[[ e ]]_B" := (bool_translation e) : ldl_scope.

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

Section fuzzy_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (l : DL) (p : R).

Fixpoint translation {t} (e : @expr R t) {struct e} : type_translation t :=
  match e in expr t return type_translation t with
   | ldl_bool _ _ _ _ true => (1%R : type_translation (Bool_T _ _ _ _))
   | ldl_bool _ _ _ _ false => (0%R : type_translation (Bool_T _ _ _ _ ))
   | ldl_idx n i => i
   | ldl_real r => r
   | ldl_vec n t => t

   | ldl_and _ _ _  Es => minR (map translation Es)
   | ldl_or _ _ _ Es => maxR (map translation Es)
   | ldl_mand _ _ _ Es =>
       match l with
       | Lukasiewicz => maxr (\sum_(i <- map translation Es) i - (size Es)%:R+1) 0
       | Yager => maxr (1 - (\sum_(i <- map (fun E => (1 - ({[ E ]} :
                  type_translation (Bool_T _ _ m_def _ )))`^p) Es) i)`^p^-1) 0
       | Godel => minR (map translation Es)
       | product => \prod_(i <- map translation Es) i
       | GodelS => minR (map translation Es)
       | productS => \prod_(i <- map translation Es) i
       end
   | ldl_mor _ _ _ Es =>
       match l with
       | Lukasiewicz => minr (\sum_(i <- map translation Es) i) 1
       | Yager => minr ((\sum_(i <- map (fun E => ({[ E ]} :
                  type_translation (Bool_T _ _ m_def _))`^p) Es) i)`^p^-1) 1
       | Godel => maxR (map translation Es)
       | product => product_dl_prod (map translation Es)
       | GodelS => maxR (map translation Es)
       | productS => product_dl_prod (map translation Es)
       end
  (*| `~ E1 => 1 - {[ E1 ]}*)
  | ldl_not _ _ _ E1 =>
      match l with
      | Lukasiewicz => 1 - {[ E1 ]}
      | Yager => 1 - {[ E1 ]}
      | Godel => if {[ E1 ]} > 0 then 0 else 1
      | product => if {[ E1 ]} > 0 then 0 else 1
      | GodelS => 1 - {[ E1 ]}
      | productS => 1 - {[ E1 ]}
      end

  | ldl_impl _ _ _ E1 E2 =>
      match l with
      | Lukasiewicz => minr (1 - {[ E1 ]} + {[ E2 ]}) 1
      | Yager => minr (((1 - {[ E1 ]})`^p + ({[ E2 ]})`^p )`^p^-1) 1
      | Godel => if {[ E2 ]} < {[ E1 ]} then {[ E2 ]} else 1
      | product => if {[ E2 ]} < {[ E1 ]} then
                     {[ E2 ]} / {[ E1 ]}
                   else
                     1
      | GodelS => maxr (1 - {[ E1 ]}) {[ E2 ]}
      | productS => 1 - ( 1 - {[ E2 ]}) * {[ E1 ]}
      end

  | E1 `== E2 =>
      let e1 := translation E1 in
      let e2 := translation E2 in
      if e1 == - e2 then (e1 == e2)%:R
      else maxr (1 - `|(e1 - e2) / (e1 + e2)|) 0
  | E1 `<= E2 =>
      let e1 := translation E1 in
      let e2 := translation E2 in
      if e1 == - e2 then (e1 <= e2)%R%:R
      else maxr (1 - maxr ((e1 - e2) / `|e1 + e2|) 0) 0

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
  | ldl_lookup n v i => tnth {[ v ]} {[ i ]}
  end
where "{[ e ]}" := (translation e).

End fuzzy_translation.

Section dl2_ereal_translation.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint dl2_ereal_translation {t} (e : @expr R t) {struct e} : ereal_type_translation t :=
  match e in expr t return ereal_type_translation t with
  | ldl_bool _ _ _ _ true => 0
  | ldl_bool _ _ _ _ false => -oo
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t
  | ldl_and _ _ _ Es => +oo (* default value, all lemmas are for negation-free formulas *)
  | ldl_or _ _ _ Es => +oo (* default value, all lemmas are for negation-free formulas *)
  | ldl_mand _ _ _ Es =>
      if has (pred1 -oo) (map dl2_ereal_translation Es) then
        -oo
      else if has (pred1 +oo) (map dl2_ereal_translation Es) then
        -oo
      else
        \sum_(i <- map dl2_ereal_translation Es) i
  | ldl_mor _ _ _ Es =>
      if has (pred1 -oo) (map dl2_ereal_translation Es) then
        -oo
      else if has (pred1 +oo) (map dl2_ereal_translation Es) then
        -oo
      else
        \sum_(i <- map dl2_ereal_translation Es) i
  | ldl_not _ _ _ E1 => +oo (* default value, all lemmas are for negation-free formulas *)
  | ldl_impl _ _ _ E1 E2 =>  (- maxe ({[ E1 ]} - {[ E2 ]}) 0)
                                
  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
  | E1 `<= E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)%:E

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
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
  | ldl_bool _ _ _ _ true => 0
  | ldl_bool _ _ _ _ false => -1
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and _ _ _ Es => 0 (* default value, all lemmas are for negation-free formulas *)
  | ldl_or _ _ _ Es => 0 (* default value, all lemmas are for negation-free formulas *)
  | ldl_mand _ _ _ Es => \sum_(i <- map dl2_translation Es) i
  | ldl_mor _ _ _ Es => \sum_(i <- map dl2_translation Es) i

  | ldl_not _ _ _ E1 => 0 (* default value, all lemmas are for negation-free formulas *)
  | ldl_impl _ _ _ E1 E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)

  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)
  | E1 `<= E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
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

Definition mine_dev (x y : \bar R) : \bar R := (x - y) / y.

Definition maxe_dev (x y : \bar R) : \bar R := (x - y) / x.

Let bigmine (s : seq (\bar R)) := \big[mine/+oo]_(i <- s) i.
Let bigmaxe (s : seq (\bar R)) := \big[maxe/-oo]_(i <- s) i.

Fixpoint stl_ereal_translation {t} (e : expr t) : ereal_type_translation t :=
  match e in expr t return ereal_type_translation t with
  | ldl_bool _ _ _ _ true => +oo
  | ldl_bool _ _ _ _ false => -oo
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and _ _ _ Es =>
      let A := map stl_ereal_translation Es in
      let a_min : \bar R := bigmine A in
      let a'_i (a_i : \bar R) := mine_dev a_i a_min in
      if a_min == -oo then -oo
      else if a_min == +oo then +oo
        else if a_min < 0 then
          (\sum_(a <- A) a_min * expeR (a'_i a) * expeR (nu%:E * a'_i a)) /
          (\sum_(a <- A) expeR (nu%:E * a'_i a))
        else if a_min > 0 then
          (\sum_(a <- A) (a * expeR (-nu%:E * a'_i a))) /
          (\sum_(a <- A) expeR (nu%:E * a'_i a))
        else 0
  | ldl_or _ _ _ Es =>
      let A := map stl_ereal_translation Es in
      let a_max : \bar R := bigmaxe A in
      let a'_i (a_i : \bar R) := maxe_dev a_max a_i in
      if a_max == -oo then -oo
      else if a_max == +oo then +oo
        else if a_max > 0 then
          (\sum_(a <- A) a_max * expeR (a'_i a) * expeR (nu%:E * a'_i a)) /
          (\sum_(a <- A) expeR (nu%:E * a'_i a))
        else if a_max < 0 then
          (\sum_(a <- A) a * expeR (-nu%:E * a'_i a)) /
          (\sum_(a <- A) expeR (nu%:E * a'_i a))
        else 0
  | ldl_mand _ _ _ Es => 0 (* default value, all lemmas are for monoid free formulas *)
  | ldl_mor _ _ _ Es => 0 (* default value, all lemmas are for monoid free formulas *)
  | ldl_not _ _ _ E1 => - {[ E1 ]}
  | ldl_impl _ _ _ E1 E2 => 0 (* default value, all lemmas are for implication-free formulas *)

  (*comparisons*)
  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
  | E1 `<= E2 => ({[ E2 ]} - {[ E1 ]})%:E(* (- maxr ({[ E1 ]} - {[ E2 ]}) 0)%:E *)

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
  | ldl_lookup n v i => tnth {[ v ]} {[ i ]}
    end
where "{[ e ]}" := (stl_ereal_translation e).

End stl_ereal_translation.

Notation "nu .-[[ e ]]_stle" := (stl_ereal_translation nu e) : ldl_scope.

Section min_max_dev.
Context {R : realType}.

Definition min_dev (x : R) (s : seq R) : R :=
  let r := \big[minr/x]_(i <- s) i in (x - r) / r.

Lemma min_dev_nseq (p : R) n : min_dev p (nseq n.+1 p) = 0%R.
Proof. by rewrite /min_dev big_nseq iter_minr// subrr mul0r. Qed.

Definition max_dev {R : realType} (x : R) (s : seq R) : R :=
  let r := \big[maxr/x]_(i <- s) i in (r - x) / r.

End min_max_dev.

Section stl_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (p : R) (nu : R).
Hypothesis p1 : 1 <= p.
Hypothesis nu0 : 0 < nu.

Definition stl_and_gt0 (v : seq R) :=
  (\sum_(a <- v) a * expR (- nu * min_dev a v)) /
    \sum_(a <- v) expR (-nu * min_dev a v).

Definition stl_and_lt0 (v : seq R) :=
  (\sum_(a <- v)
    (\big[minr/a]_(i <- v) i) * expR (min_dev a v) * expR (nu * min_dev a v)) /
      \sum_(a <- v) expR (nu * min_dev a v).

Definition stl_or_gt0 (v : seq R) :=
  (\sum_(a <- v)
    (\big[maxr/a]_(i <- v) i) * expR (max_dev a v) * expR (nu * max_dev a v)) /
    (\sum_(a <- v) expR (nu * max_dev a v)).

Definition stl_or_lt0 (v : seq R) :=
  (\sum_(a <- v) a * expR (-nu * max_dev a v)) /
    (\sum_(a <- v) expR (nu * max_dev a v)).

Definition stl_and (a_min : R) h (t : seq R) : R :=
  if a_min < 0 then
    stl_and_lt0 (h :: t)
  else if a_min > 0 then
    stl_and_gt0 (h :: t)
  else 0.

Definition stl_or (a_max : R) h (t : seq R) : R :=
  if a_max > 0 then
    stl_or_gt0 (h :: t)
  else if a_max < 0 then
    stl_or_lt0 (h :: t)
  else 0.

Fixpoint stl_translation {t} (e : expr t) : type_translation t :=
  match e in expr t return type_translation t with
  | ldl_bool _ _ _ _ true => 1
  | ldl_bool _ _ _ _ false => -1
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and _ _ _ [::] => 1
  | ldl_and _ _ _ (e0 :: s) =>
      let A := map stl_translation s in
      let a0 := stl_translation e0 in
      let a_min : R := \big[minr/a0]_(i <- A) i in
      stl_and a_min a0 A
  | ldl_or _ _ _ [::] => -1
  | ldl_or _ _ _ (e0 :: s) =>
      let A := map stl_translation s in
      let a0 := stl_translation e0 in
      let a_max: R := \big[maxr/a0]_(i <- A) i in
      stl_or a_max a0 A
  | ldl_mand _ _ _ Es => 0 (* default value, all lemmas are for negation-free formulas *)
  | ldl_mor _ _ _ Es => 0 (* default value, all lemmas are for negation-free formulas *)
  | `~ E1 => - {[ E1 ]}
  | E1 `=> E2 => 0 (* default value, all lemmas are for negation-free formulas *)

  | E1 `== E2 => - `| {[ E1 ]} - {[ E2 ]}|
  | E1 `<= E2 => {[ E2 ]} - {[ E1 ]}

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
  | ldl_lookup n v i => tnth {[ v ]} {[ i ]}
  end
where "{[ e ]}" := (stl_translation e).

End stl_translation.

Notation "nu .-[[ e ]]_stl" := (stl_translation nu e) : ldl_scope.

Section shadow_lifting.
Local Open Scope ring_scope.

Definition shadow_lifting {R : realType} n (f : 'rV_n.+1 -> R) :=
  forall p, p > 0 -> forall i, ('d f '/d i) (const_mx p) > 0.

End shadow_lifting.
