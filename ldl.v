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
(*   corresponding type of the interpretation; maps `boolT` to $\mathbb R$    *)
(* - `ereal_type_translation`: same as before, but maps                       *)
(*   `boolT` to $\bar{\mathbb R}}$                                            *)
(* - `bool_type_translation`: type translation for the boolean interpretation;*)
(*   maps `boolT` to `bool`                                                   *)
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
(* - `stl_infty_translation`: maps an LDL-formula to its interpretation in    *)
(*   STLinfty, STL where parameter nu tends to infinity$                      *)
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

Inductive ldl_type :=
| boolT
| indexT of nat
| realT
| vectorT of nat
| funT of nat & nat
| fun2T of nat & nat & nat.

Inductive comparison : Type := cmp_le | cmp_eq.

Section expr.
Context {R : realType}.

Inductive expr : ldl_type -> Type :=
  (* base expressions *)
  | ldl_bool : bool -> expr boolT
  | ldl_idx : forall n, 'I_n -> expr (indexT n)
  | ldl_real : R -> expr realT
  | ldl_vec : forall n, R ^ n -> expr (vectorT n)
  (* connectives *)
  | ldl_and : forall n, ('I_n -> (expr boolT)) -> expr boolT
  | ldl_or : forall n, ('I_n -> (expr boolT)) -> expr boolT
  | ldl_not : expr boolT -> expr boolT 
  | ldl_impl : expr boolT -> expr boolT -> expr boolT
  | ldl_mand : forall n, ('I_n -> (expr boolT)) -> expr boolT
  | ldl_mor : forall n, ('I_n -> (expr boolT)) -> expr boolT 
  (* comparisons *)
  | ldl_cmp : comparison -> expr realT -> expr realT -> expr boolT
  (* networks and applications *)
  | ldl_fun : forall n m, (R ^ n -> R ^ m) -> expr (funT n m)
  | ldl_fun2 : forall n m l, (R ^ n -> R ^ m -> R ^ l) -> expr (fun2T n m l)
  | ldl_app : forall n m, expr (funT n m) -> expr (vectorT n) -> expr (vectorT m)
  | ldl_app2 : forall n m l, expr (fun2T n m l) -> expr (vectorT n) -> expr (vectorT m) -> expr (vectorT l)
  | ldl_lookup : forall n, expr (vectorT n) -> expr (indexT n) -> expr realT.

Inductive negation_free : expr boolT -> Prop :=
  | nf_bool : forall b, negation_free (ldl_bool b)
  | nf_and : forall n f, negation_free (@ldl_and n f)
  | nf_or : forall n f, negation_free (@ldl_or n f)
  | nf_impl : forall x y, negation_free (ldl_impl x y)
  | nf_mand : forall n f, negation_free (@ldl_mand n f)
  | nf_mor : forall n f, negation_free (@ldl_mor n f)
  | nf_cmp : forall c x y, negation_free (ldl_cmp c x y)
.

Inductive implication_free : expr boolT -> Prop :=
  | if_bool : forall b, implication_free (ldl_bool b)
  | if_and : forall n f, implication_free (@ldl_and n f)
  | if_or : forall n f, implication_free (@ldl_or n f)
  | if_not : forall x, implication_free (ldl_not x)
  | if_mand : forall n f, implication_free (@ldl_mand n f)
  | if_mor : forall n f, implication_free (@ldl_mor n f)
  | if_cmp : forall c x y, implication_free (ldl_cmp c x y)
.

Inductive monoid_free : expr boolT -> Prop :=
  | mf_bool : forall b, monoid_free (ldl_bool b)
  | mf_and : forall n f, monoid_free (@ldl_and n f)
  | mf_or : forall n f, monoid_free (@ldl_or n f)
  | mf_not : forall x, monoid_free (ldl_not x)
  | mf_impl : forall x y, monoid_free (ldl_impl x y)
  | mf_cmp : forall c x y, monoid_free (ldl_cmp c x y)
.

Inductive lattice_free : expr boolT -> Prop :=
  | lf_bool : forall b, lattice_free (ldl_bool b)
  | lf_not : forall x, lattice_free (ldl_not x)
  | lf_impl : forall x y, lattice_free (ldl_impl x y)
  | lf_mand : forall n f, lattice_free (@ldl_mand n f)
  | lf_mor : forall n f, lattice_free (@ldl_mor n f)
  | lf_cmp : forall c x y, lattice_free (ldl_cmp c x y)
.

End expr.

Declare Scope ldl_scope.

Notation "a `/\ b" := (ldl_and (tnth [:: a; b])) (at level 65) : ldl_scope.
Notation "a `\/ b" := (ldl_or (tnth [:: a; b])) (at level 65) : ldl_scope.
Notation "a `** b" := (ldl_mand (tnth [:: a; b])) (at level 65) : ldl_scope.
Notation "a `++ b" := (ldl_mor (tnth [:: a; b])) (at level 65) : ldl_scope.
Notation "a `=> b" := (ldl_impl a b) (at level 70) : ldl_scope.
Notation "`~ a"    := (ldl_not a) (at level 61) : ldl_scope.

Local Open Scope ldl_scope.

Notation "a `<= b" := (ldl_cmp cmp_le a b) (at level 40) : ldl_scope.
Notation "a `== b" := (ldl_cmp cmp_eq a b) (at level 40) : ldl_scope.
Notation "a `!= b" := (`~ (a == b)) (at level 40) : ldl_scope.
Notation "a `< b"  := (a `<= b /\ a `!= b) (at level 40) : ldl_scope.
Notation "a `>= b" := (b `<= a) (at level 40) : ldl_scope.
Notation "a `> b"  := (b `< a) (at level 40) : ldl_scope.
Notation "a `! b"  := (ldl_lookup a b) : ldl_scope.
Notation "f '`@' x" := (ldl_app f x) (at level 60) : ldl_scope.
Notation "f '`@2' ( x , y )" := (ldl_app2 f x y) (at level 60) : ldl_scope.

Local Close Scope ldl_scope.

Lemma expr_ind' (R : realType) :
  forall P : forall l : ldl_type, expr l -> Prop,
       (forall (b : bool), P boolT (ldl_bool b)) ->
       (forall (n : nat) (o : 'I_n), P (indexT n) (ldl_idx o)) ->
       (forall s : R, P realT (ldl_real s)) ->
       (forall (n : nat) (t : R ^ n), P (vectorT n) (ldl_vec t)) ->
       (forall n (l : 'I_n -> (expr boolT)),
          (forall a, P boolT (l a)) -> P boolT (ldl_and l)) ->
       (forall n (l : 'I_n -> (expr boolT)),
        (forall a, P boolT (l a)) -> P boolT (ldl_or l)) ->
       (forall (e : expr boolT),
        P boolT e -> P boolT (ldl_not e)) ->
       (forall (e : expr boolT),
        P boolT e ->
        forall e0 : expr boolT,
        P boolT e0 -> P boolT (ldl_impl e e0)) ->
       (forall n (l : 'I_n -> (expr boolT)),
          (forall a, P boolT (l a)) -> P boolT (ldl_mand l)) ->
       (forall n (l : 'I_n -> (expr boolT)),
        (forall a, P boolT (l a)) -> P boolT (ldl_mor l)) ->
       (forall (c : comparison) (e : expr realT),
        P realT e -> forall e0 : expr realT, P realT e0 -> P boolT (ldl_cmp c e e0)) ->
       (forall (n m : nat) (t : R ^ n -> R ^ m), P (funT n m) (ldl_fun t)) ->
       (forall (n m l : nat) (t : R ^ n -> R ^ m -> R ^ l), P (fun2T n m l) (ldl_fun2 t)) ->
       (forall (n m : nat) (e : expr (funT n m)),
        P (funT n m) e -> forall e0 : expr (vectorT n), P (vectorT n) e0 -> P (vectorT m) (ldl_app e e0)) ->
       (forall (n m l : nat) (e : expr (fun2T n m l)),
        P (fun2T n m l) e -> forall (e0 : expr (vectorT n)) (e1 : expr (vectorT m)), P (vectorT n) e0 -> P (vectorT m) e1 -> P (vectorT l) (ldl_app2 e e0 e1)) ->
       (forall (n : nat) (e : expr (vectorT n)),
        P (vectorT n) e -> forall e0 : expr (indexT n), P (indexT n) e0 -> P realT (ldl_lookup e e0)) ->
       forall (l : ldl_type) (e : expr l), P l e.
Proof.
move => P H H0 H1 H2 H3 H4 H7 H11 H12 H13 H14 H15 H16 H17 H18 H19.
fix F1 2.
destruct e.
  * exact: H.
  * exact: H0.
  * exact: H1.
  * exact: H2.
  * exact: H3.
  * exact: H4.
  * exact: H7; eauto.
  * exact: H11; eauto.
  * exact: H12.
  * exact: H13.
  * exact: H14; eauto.
  * exact: H15; eauto.
  * exact: H16; eauto.
  * exact: H17; eauto.
  * exact: H18; eauto.
  * exact: H19; eauto.
Qed.

Inductive DL := Lukasiewicz | Yager | Godel | product | GodelS | productS.

Section type_translation.
Context {R : realType}.

Definition type_translation (t : ldl_type) : Type:=
  match t with
  | boolT  => R
  | realT => R
  | vectorT n => R ^ n
  | indexT n => 'I_n
  | funT n m => R ^ n -> R ^ m
  | fun2T n m l => R ^ n -> R ^ m -> R ^ l
end.

Definition bool_type_translation (t : ldl_type) : Type:=
  match t with
  | boolT => bool
  | realT => R
  | vectorT n => R ^ n
  | indexT n => 'I_n
  | funT n m => R ^ n -> R ^ m
  | fun2T n m l => R ^ n -> R ^ m -> R ^ l
  end.

Definition ereal_type_translation (t : ldl_type) : Type :=
  match t with
  | boolT => \bar R
  | realT => R
  | vectorT n => R ^ n
  | indexT n => 'I_n
  | funT n m => R ^ n -> R ^ m
  | fun2T n m l => R ^ n -> R ^ m -> R ^ l
  end.

End type_translation.

Section bool_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint bool_translation {t} (e : @expr R t) : bool_type_translation t :=
  match e in expr t return bool_type_translation t with
  | ldl_bool x => x
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and n Es => \big[andb/true]_(i < n) bool_translation (Es i)
  | ldl_or n Es => \big[orb/false]_(i < n) bool_translation (Es i)
  | ldl_not E1 => ~~ << E1 >>
  | ldl_impl E1  E2 => << E1 >> ==> << E2>>
  | ldl_mand n Es => \big[andb/true]_(i < n) bool_translation (Es i)
  | ldl_mor n Es => \big[orb/false]_(i < n) bool_translation (Es i)

  | E1 `== E2 => << E1 >> == << E2 >>
  | E1 `<= E2 => << E1 >> <= << E2 >>

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => << f >> << v >>
  | ldl_app2 n m l f v1 v2 => << f >> << v1 >> << v2 >>
  | ldl_lookup n v i => << v >> << i >>
  end
where "<< e >>" := (bool_translation e).

End bool_translation.

Notation "[[ e ]]_B" := (bool_translation e) : ldl_scope.

Definition product_dl_mul {R : numDomainType} (a b : R) := (a + b - a * b)%R.

Definition product_dl_prod {R : numDomainType} n (f : 'I_n -> R) :=
  (\big[product_dl_mul/0]_(i < n) f i)%R.

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
   | ldl_bool true => (1%R : type_translation boolT)
   | ldl_bool false => (0%R : type_translation boolT)
   | ldl_idx n i => i
   | ldl_real r => r
   | ldl_vec n t => t

   | ldl_and n Es => minR (fun i => translation (Es i))
   | ldl_or n Es => maxR (fun i => translation (Es i))
   | ldl_mand n Es =>
       match l with
       | Lukasiewicz => maxr (\sum_(i < n) translation (Es i) - n%:R+1) 0
       | Yager => maxr (1 - (\sum_(i < n) (1 - ({[ Es i ]} :
                  type_translation boolT))`^p)`^p^-1) 0
       | Godel => minR (fun i => translation (Es i))
       | product => \prod_(i < n) translation (Es i)
       | GodelS => minR (fun i => translation (Es i))
       | productS => \prod_(i < n) translation (Es i)
       end
   | ldl_mor n Es =>
       match l with
       | Lukasiewicz => minr (\sum_(i < n) translation (Es i)) 1
       | Yager => minr ((\sum_(i < n) ({[ Es i ]} :
                  type_translation boolT)`^p)`^p^-1) 1
       | Godel => maxR (fun i => translation (Es i))
       | product => product_dl_prod (fun i => translation (Es i))
       | GodelS => maxR (fun i => translation (Es i))
       | productS => product_dl_prod (fun i => translation (Es i))
       end
  (*| `~ E1 => 1 - {[ E1 ]}*)
  | ldl_not E1 =>
      match l with
      | Lukasiewicz => 1 - {[ E1 ]}
      | Yager => 1 - {[ E1 ]}
      | Godel => if {[ E1 ]} > 0 then 0 else 1
      | product => if {[ E1 ]} > 0 then 0 else 1
      | GodelS => 1 - {[ E1 ]}
      | productS => 1 - {[ E1 ]}
      end

  | ldl_impl E1 E2 =>
      match l with
      | Lukasiewicz => minr (1 - {[ E1 ]} + {[ E2 ]}) 1
      | Yager => if {[ E1 ]} < {[ E2 ]} then 1
                 else 1 - ((1 - {[ E2 ]})`^p - (1 - {[ E1 ]})`^p)`^p^-1
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
  | ldl_lookup n v i => {[ v ]} {[ i ]}
  end
where "{[ e ]}" := (translation e).

End fuzzy_translation.

Section dl2_ereal_translation.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

Fixpoint dl2_ereal_translation {t} (e : @expr R t) {struct e} : ereal_type_translation t :=
  match e in expr t return ereal_type_translation t with
  | ldl_bool true => 0
  | ldl_bool false => -oo
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t
  | ldl_and n Es => \big[mine/0]_(i < n) dl2_ereal_translation (Es i)
  | ldl_or n Es =>\big[maxe/-oo]_(i < n) dl2_ereal_translation (Es i)
  | ldl_mand n Es =>
      \sum_(i < n) dl2_ereal_translation (Es i)
  | ldl_mor n Es =>
      ((-1) ^+ n.+1)%:E * \prod_(i < n) dl2_ereal_translation (Es i)
  | ldl_not E1 => +oo (* default value, all lemmas are for negation-free formulas *)
  | ldl_impl E1 E2 =>  (- maxe ({[ E1 ]} - {[ E2 ]}) 0)
  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
  | E1 `<= E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)%:E

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
  | ldl_lookup n v i => {[ v ]} {[ i ]}
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
  | ldl_bool true => 0
  | ldl_bool false => -1
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and 0 _ => 0
  | ldl_and n.+1 Es => \big[minr/dl2_translation (Es ord0)]_(i < n.+1) dl2_translation (Es i)
  | ldl_or 0 _ => 0
  | ldl_or n.+1 Es => \big[maxr/dl2_translation (Es ord0)]_(i < n.+1) dl2_translation (Es i)
  | ldl_mand n Es => \sum_(i < n) dl2_translation (Es i)
  | ldl_mor n Es => (-1) ^+ n.+1 * \prod_(i < n) dl2_translation (Es i)

  | ldl_not E1 => 0 (* default value, all lemmas are for negation-free formulas *)
  | ldl_impl E1 E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)

  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)
  | E1 `<= E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
  | ldl_lookup n v i => {[ v ]} {[ i ]}
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

Let bigmine n (f : 'I_n -> (\bar R)) := \big[mine/+oo]_(i < n) f i.
Let bigmaxe n (f : 'I_n -> (\bar R)) := \big[maxe/-oo]_(i < n) f i.

Fixpoint stl_ereal_translation {t} (e : expr t) : ereal_type_translation t :=
  match e in expr t return ereal_type_translation t with
  | ldl_bool true => +oo
  | ldl_bool false => -oo
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and n Es =>
      let A := stl_ereal_translation \o Es in
      let a_min : \bar R := bigmine A in
      let a'_i (a_i : \bar R) := mine_dev a_i a_min in
      if a_min == -oo then -oo
      else if a_min == +oo then +oo
        else if a_min < 0 then
          (\sum_(i < n) a_min * expeR (a'_i (A i)) * expeR (nu%:E * a'_i (A i))) /
          (\sum_(i < n) expeR (nu%:E * a'_i (A i)))
        else if a_min > 0 then
          (\sum_(i < n) ((A i) * expeR (-nu%:E * a'_i (A i)))) /
          (\sum_(i < n) expeR (nu%:E * a'_i (A i)))
        else 0
  | ldl_or n Es =>
      let A := stl_ereal_translation \o Es in
      let a_max : \bar R := bigmaxe A in
      let a'_i (a_i : \bar R) := maxe_dev a_max a_i in
      if a_max == -oo then -oo
      else if a_max == +oo then +oo
        else if a_max > 0 then
          (\sum_(i < n) a_max * expeR (a'_i (A i)) * expeR (nu%:E * a'_i (A i))) /
          (\sum_(i < n) expeR (nu%:E * a'_i (A i)))
        else if a_max < 0 then
          (\sum_(i < n) (A i) * expeR (-nu%:E * a'_i (A i))) /
          (\sum_(i < n) expeR (nu%:E * a'_i (A i)))
        else 0
  | ldl_mand n Es => 0 (* default value, all lemmas are for monoid free formulas *)
  | ldl_mor n Es => 0 (* default value, all lemmas are for monoid free formulas *)
  | ldl_not E1 => - {[ E1 ]}
  | ldl_impl E1 E2 => 0 (* default value, all lemmas are for implication-free formulas *)

  (*comparisons*)
  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
  | E1 `<= E2 => ({[ E2 ]} - {[ E1 ]})%:E

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
  | ldl_lookup n v i => {[ v ]} {[ i ]}
    end
where "{[ e ]}" := (stl_ereal_translation e).

End stl_ereal_translation.

Notation "nu .-[[ e ]]_stle" := (stl_ereal_translation nu e) : ldl_scope.

Section min_max_dev.
Context {R : realType}.
Local Open Scope ring_scope.

Definition min_dev n i (f : 'I_n.+1 -> R) : R :=
  let r := \big[minr/f ord0]_(j < n.+1) f j in (f i - r) / r.

Definition max_dev {R : realType} n i (f : 'I_n.+1 -> R) : R :=
  let r := \big[maxr/f ord0]_(i < n.+1) f i in (r - f i) / r.

End min_max_dev.

Section stl_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (p : R) (nu : R).
Hypothesis p1 : 1 <= p.
Hypothesis nu0 : 0 < nu.

Definition stl_and_gt0 n (v : 'I_n.+1 -> R) :=
  (\sum_(a < n.+1) v a * expR (- nu * min_dev a v)) /
    \sum_(a < n.+1) expR (-nu * min_dev a v).

Definition stl_and_lt0 n (v : 'I_n.+1 -> R) :=
  (\sum_(a < n.+1)
    (\big[minr/v ord0]_(i < n.+1) v i) * expR (min_dev a v) * expR (nu * min_dev a v)) /
      \sum_(a < n.+1) expR (nu * min_dev a v).

Definition stl_or_gt0 n (v : 'I_n.+1 -> R) :=
  (\sum_(a < n.+1)
    (\big[maxr/v ord0]_(i < n.+1) v i) * expR (max_dev a v) * expR (nu * max_dev a v)) /
    (\sum_(a < n.+1) expR (nu * max_dev a v)).

Definition stl_or_lt0 n (v : 'I_n.+1 -> R) :=
  (\sum_(a < n.+1) v a * expR (-nu * max_dev a v)) /
    (\sum_(a < n.+1) expR (nu * max_dev a v)).

Definition stl_and (a_min : R) n (t : 'I_n.+1 -> R) : R :=
  if a_min < 0 then stl_and_lt0 t
  else if a_min > 0 then stl_and_gt0 t
  else 0.

Definition stl_or (a_max : R) n (t : 'I_n.+1 -> R) : R :=
  if a_max > 0 then stl_or_gt0 t
  else if a_max < 0 then stl_or_lt0 t
  else 0.

Fixpoint stl_translation {t} (e : expr t) : type_translation t :=
  match e in expr t return type_translation t with
  | ldl_bool true => 1
  | ldl_bool false => -1
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and 0 _ => 1
  | ldl_and n.+1 s =>
      let A := stl_translation \o s in
      let a_min : R := \big[minr/A ord0]_(i < n.+1) A i in
      stl_and a_min A
  | ldl_or 0 _ => -1
  | ldl_or n.+1 s =>
      let A := stl_translation \o s in
      let a_max: R := \big[maxr/A ord0]_(i < n.+1) A i in
      stl_or a_max A
  | ldl_mand _ _ => 0 (* default value, all lemmas are for monoid-free formulas *)
  | ldl_mor _ _ => 0 (* default value, all lemmas are for monoid-free formulas *)
  | `~ E1 => - {[ E1 ]}
  | E1 `=> E2 => 0 (* default value, all lemmas are for implication-free formulas *)

  | E1 `== E2 => - `| {[ E1 ]} - {[ E2 ]}|
  | E1 `<= E2 => {[ E2 ]} - {[ E1 ]}

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
  | ldl_lookup n v i => {[ v ]} {[ i ]}
  end
where "{[ e ]}" := (stl_translation e).

End stl_translation.

Notation "nu .-[[ e ]]_stl" := (stl_translation nu e) : ldl_scope.

Section shadow_lifting.
Local Open Scope ring_scope.

Definition shadow_lifting {R : realType} n (f : 'rV_n.+1 -> R) :=
  forall p, p > 0 -> forall i, ('d f '/d i) (const_mx p) > 0.

End shadow_lifting.

Section stl_infty_translation.
Local Open Scope ereal_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

(*version of STL where nu tends to \infty, which we prove in stl.v converges*)
Fixpoint stl_infty_translation {t} (e : @expr R t) {struct e} : ereal_type_translation t :=
  match e in expr t return ereal_type_translation t with
  | ldl_bool true => +oo
  | ldl_bool false => -oo
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and 0 _ => 0
  | ldl_and n.+1 Es  => \big[mine/+oo]_(i < n.+1) stl_infty_translation (Es i)
  | ldl_or 0 _ => 0
  | ldl_or n.+1 Es  => \big[maxe/-oo]_(i < n.+1) stl_infty_translation (Es i)
  | ldl_mand 0 _ => 0
  | ldl_mand n.+1 Es  => \big[mine/+oo]_(i < n.+1) stl_infty_translation (Es i)
  | ldl_mor 0 _ => 0
  | ldl_mor n.+1 Es => \big[maxe/-oo]_(i < n.+1) stl_infty_translation (Es i)

  | ldl_not E1 => - {[ E1 ]}
  | ldl_impl E1 E2 => 
      if {[ E1 ]} <= {[ E2 ]} then +oo
      else {[ E2 ]}

  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
  | E1 `<= E2 => ({[ E2 ]} - {[ E1 ]})%:E

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
  | ldl_lookup n v i => {[ v ]} {[ i ]}
end
where "{[ e ]}" := (stl_infty_translation e).

End stl_infty_translation.
Notation "[[ e ]]_stli" := (stl_infty_translation e) : ldl_scope.
