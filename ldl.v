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
| boolT of flag_neg & flag_impl & flag_monoid & flag_lattice
| indexT of nat
| realT
| vectorT of nat
| funT of nat & nat
| fun2T of nat & nat & nat.

Definition boolT_undef := boolT neg_undef.
Definition boolT_def := boolT neg_def.

(*flags of the DLs*)
Definition boolT_fuzzy := boolT neg_def impl_def m_def l_def.
Definition boolT_dl2 := boolT neg_undef impl_def m_def l_def.
Definition boolT_stl := boolT neg_def impl_undef m_undef l_def.

Inductive comparison : Type := cmp_le | cmp_eq.

Section expr.
Context {R : realType}.

Inductive expr : ldl_type -> Type :=
  (* base expressions *)
  | ldl_bool : forall p r s t, bool -> expr (boolT p r s t)
  | ldl_idx : forall n, 'I_n -> expr (indexT n)
  | ldl_real : R -> expr realT
  | ldl_vec : forall n, R ^ n -> expr (vectorT n)
  (* connectives *)
  | ldl_and : forall fn fi fm n, (expr (boolT fn fi fm l_def)) ^ n -> expr (boolT fn fi fm l_def)
  | ldl_or : forall fn fi fm n, (expr (boolT fn fi fm l_def)) ^ n -> expr (boolT fn fi fm l_def)
  | ldl_not : forall fi fm fl, expr (boolT neg_def fi fm fl) -> expr (boolT neg_def  fi fm fl) 
  | ldl_impl :forall fn fm fl, expr (boolT fn impl_def fm fl) 
                               -> expr (boolT fn impl_def fm fl) -> expr (boolT fn impl_def fm fl)
  | ldl_mand : forall fn fi fl n, (expr (boolT fn fi m_def fl)) ^ n -> expr (boolT fn fi m_def fl)
  | ldl_mor : forall fn fi fl n, (expr (boolT fn fi m_def fl)) ^ n -> expr (boolT fn fi m_def fl) 
  (* comparisons *)
  | ldl_cmp : forall fn fi fm fl, comparison -> expr realT -> expr realT -> expr (boolT fn fi fm fl)
  (* networks and applications *)
  | ldl_fun : forall n m, (R ^ n -> R ^ m) -> expr (funT n m)
  | ldl_fun2 : forall n m l, (R ^ n -> R ^ m -> R ^ l) -> expr (fun2T n m l)
  | ldl_app : forall n m, expr (funT n m) -> expr (vectorT n) -> expr (vectorT m)
  | ldl_app2 : forall n m l, expr (fun2T n m l) -> expr (vectorT n) -> expr (vectorT m) -> expr (vectorT l)
  | ldl_lookup : forall n, expr (vectorT n) -> expr (indexT n) -> expr realT.

End expr.

Declare Scope ldl_scope.

Notation "a `/\ b" := (ldl_and [:: a; b]) (at level 65) : ldl_scope.
Notation "a `\/ b" := (ldl_or [:: a; b]) (at level 65) : ldl_scope.
Notation "a `** b" := (ldl_mand [:: a; b]) (at level 65) : ldl_scope.
Notation "a `++ b" := (ldl_mor [:: a; b]) (at level 65) : ldl_scope.
Notation "a `=> b" := (ldl_impl a b) (at level 70) : ldl_scope.
Notation "`~ a"    := (ldl_not a) (at level 61) : ldl_scope.

Local Open Scope ldl_scope.

Notation "a `<= b" := (ldl_cmp _ _ _ _ cmp_le a b) (at level 40) : ldl_scope.
Notation "a `== b" := (ldl_cmp _ _ _ _ cmp_eq a b) (at level 40) : ldl_scope.
Notation "a `!= b" := (`~ (a == b)) (at level 40) : ldl_scope.
Notation "a `< b"  := (a `<= b /\ a `!= b) (at level 40) : ldl_scope.
Notation "a `>= b" := (b `<= a) (at level 40) : ldl_scope.
Notation "a `> b"  := (b `< a) (at level 40) : ldl_scope.
Notation "a `! b"  := (ldl_lookup a b) : ldl_scope.
Notation "f '`@' x" := (ldl_app f x) (at level 60) : ldl_scope.
Notation "f '`@2' ( x , y )" := (ldl_app2 f x y) (at level 60) : ldl_scope.

Local Close Scope ldl_scope.

Inductive DL := Lukasiewicz | Yager | Godel | product | GodelS | productS.

Section type_translation.
Context {R : realType}.

Definition type_translation (t : ldl_type) : Type:=
  match t with
  | boolT x y z v  => R
  | realT => R
  | vectorT n => R ^ n
  | indexT n => 'I_n
  | funT n m => R ^ n -> R ^ m
  | fun2T n m l => R ^ n -> R ^ m -> R ^ l
end.

Definition bool_type_translation (t : ldl_type) : Type:=
  match t with
  | boolT x y z v=> bool
  | realT => R
  | vectorT n => R ^ n
  | indexT n => 'I_n
  | funT n m => R ^ n -> R ^ m
  | fun2T n m l => R ^ n -> R ^ m -> R ^ l
  end.

Definition ereal_type_translation (t : ldl_type) : Type :=
  match t with
  | boolT x y z v=> \bar R
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
  | ldl_bool f1 f2 f3 f4 x => x
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and f1 f2 f3 n Es => \big[andb/true]_(i < n) bool_translation (Es i)
  | ldl_or f1 f2 f3 n Es => \big[orb/false]_(i < n) bool_translation (Es i)
  | ldl_not f2 f3 f4  E1 => ~~ << E1 >>
  | ldl_impl f1 f3 f4 E1  E2 => << E1 >> ==> << E2>>
  | ldl_mand f1 f2 f4 n Es => \big[andb/true]_(i < n) bool_translation (Es i)
  | ldl_mor f1 f2 f4 n Es => \big[orb/false]_(i < n) bool_translation (Es i)

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
   | ldl_bool _ _ _ _ true => (1%R : type_translation (boolT _ _ _ _))
   | ldl_bool _ _ _ _ false => (0%R : type_translation (boolT _ _ _ _ ))
   | ldl_idx n i => i
   | ldl_real r => r
   | ldl_vec n t => t

   | ldl_and _ _ _ n Es => minR (fun i => translation (Es i))
   | ldl_or _ _ _ n Es => maxR (fun i => translation (Es i))
   | ldl_mand _ _ _ n Es =>
       match l with
       | Lukasiewicz => maxr (\sum_(i < n) translation (Es i) - n%:R+1) 0
       | Yager => maxr (1 - (\sum_(i < n) (1 - ({[ Es i ]} :
                  type_translation (boolT _ _ m_def _ )))`^p)`^p^-1) 0
       | Godel => minR (fun i => translation (Es i))
       | product => \prod_(i < n) translation (Es i)
       | GodelS => minR (fun i => translation (Es i))
       | productS => \prod_(i < n) translation (Es i)
       end
   | ldl_mor _ _ _ n Es =>
       match l with
       | Lukasiewicz => minr (\sum_(i < n) translation (Es i)) 1
       | Yager => minr ((\sum_(i < n) ({[ Es i ]} :
                  type_translation (boolT _ _ m_def _))`^p)`^p^-1) 1
       | Godel => maxR (fun i => translation (Es i))
       | product => product_dl_prod (fun i => translation (Es i))
       | GodelS => maxR (fun i => translation (Es i))
       | productS => product_dl_prod (fun i => translation (Es i))
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
  | ldl_bool _ _ _ _ true => 0
  | ldl_bool _ _ _ _ false => -oo
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t
  | ldl_and _ _ _ n Es => \big[mine/0]_(i < n) dl2_ereal_translation (Es i)
  | ldl_or _ _ _ n Es =>\big[maxe/-oo]_(i < n) dl2_ereal_translation (Es i)
  | ldl_mand _ _ _ n Es =>
      if [exists i, dl2_ereal_translation (Es i) == -oo ] then -oo
      else if [exists i, dl2_ereal_translation (Es i) == +oo] then -oo
      else
        \sum_(i < n) dl2_ereal_translation (Es i)
  | ldl_mor _ _ _ n Es =>
      if [exists i, dl2_ereal_translation (Es i) == -oo ] then -oo
      else if [exists i, dl2_ereal_translation (Es i) == +oo] then -oo
      else
        (- 1)%:E ^+ n.+1 * \prod_(i < n) dl2_ereal_translation (Es i)
  | ldl_not _ _ _ E1 => +oo (* default value, all lemmas are for negation-free formulas *)
  | ldl_impl _ _ _ E1 E2 =>  (- maxe ({[ E1 ]} - {[ E2 ]}) 0)
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
  | ldl_bool _ _ _ _ true => 0
  | ldl_bool _ _ _ _ false => -1
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and _ _ _ 0 _ => 0
  | ldl_and _ _ _ n.+1 Es => 0(* \big[minr/Es 0]_(i < n.+1) dl2_translation (Es i) *)
  | ldl_or _ _ _ 0 _ => 0
  | ldl_or _ _ _ n.+1 Es => 0 (* \big[maxr/Es 0]_(i < n.+1) dl2_translation (Es i) *)
  | ldl_mand _ _ _ n Es => \sum_(i < n) dl2_translation (Es i)
  | ldl_mor _ _ _ n Es => (- 1) ^+ n.+1 * \prod_(i < n) dl2_translation (Es i)

  | ldl_not _ _ _ E1 => 0 (* default value, all lemmas are for negation-free formulas *)
  | ldl_impl _ _ _ E1 E2 => (- maxr ({[ E1 ]} - {[ E2 ]}) 0)

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
  | ldl_bool _ _ _ _ true => +oo
  | ldl_bool _ _ _ _ false => -oo
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and _ _ _ n Es =>
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
  | ldl_or _ _ _ n Es =>
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
  | ldl_mand _ _ _ n Es => 0 (* default value, all lemmas are for monoid free formulas *)
  | ldl_mor _ _ _ n Es => 0 (* default value, all lemmas are for monoid free formulas *)
  | ldl_not _ _ _ E1 => - {[ E1 ]}
  | ldl_impl _ _ _ E1 E2 => 0 (* default value, all lemmas are for implication-free formulas *)

  (*comparisons*)
  | E1 `== E2 => (- `| {[ E1 ]} - {[ E2 ]}|)%:E
  | E1 `<= E2 => ({[ E2 ]} - {[ E1 ]})%:E(* (- maxr ({[ E1 ]} - {[ E2 ]}) 0)%:E *)

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

Definition min_dev (x : R) n (f : 'I_n -> R) : R :=
  let r := \big[minr/x]_(i < n) f i in (x - r) / r.

Lemma min_dev_nseq (p : R) n : min_dev p (fun i : 'I_n.+1 => p) = 0%R.
Admitted.

Definition max_dev {R : realType} (x : R) n (f : 'I_n -> R) : R :=
  let r := \big[maxr/x]_(i < n) f i in (r - x) / r.

End min_max_dev.

Section stl_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (p : R) (nu : R).
Hypothesis p1 : 1 <= p.
Hypothesis nu0 : 0 < nu.

Definition stl_and_gt0 n (v : 'I_n -> R) :=
  (\sum_(a < n) v a * expR (- nu * min_dev (v a) v)) /
    \sum_(a < n) expR (-nu * min_dev (v a) v).

Definition stl_and_lt0 n (v : 'I_n -> R) :=
  (\sum_(a < n)
    (\big[minr/v a]_(i < n) v i) * expR (min_dev (v a) v) * expR (nu * min_dev (v a) v)) /
      \sum_(a < n) expR (nu * min_dev (v a) v).

Definition stl_or_gt0 n (v : 'I_n -> R) :=
  (\sum_(a < n)
    (\big[maxr/v a]_(i < n) v i) * expR (max_dev (v a) v) * expR (nu * max_dev (v a) v)) /
    (\sum_(a < n) expR (nu * max_dev (v a) v)).

Definition stl_or_lt0 n (v : 'I_n -> R) :=
  (\sum_(a < n) v a * expR (-nu * max_dev (v a) v)) /
    (\sum_(a < n) expR (nu * max_dev (v a) v)).

Definition stl_and (a_min : R) n (t : 'I_n -> R) : R :=
  if a_min < 0 then stl_and_lt0 t
  else if a_min > 0 then stl_and_gt0 t
  else 0.

Definition stl_or (a_max : R) n (t : 'I_n -> R) : R :=
  if a_max > 0 then stl_or_gt0 t
  else if a_max < 0 then stl_or_lt0 t
  else 0.

Fixpoint stl_translation {t} (e : expr t) : type_translation t :=
  match e in expr t return type_translation t with
  | ldl_bool _ _ _ _ true => 1
  | ldl_bool _ _ _ _ false => -1
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and _ _ _ 0 _ => 1
  | ldl_and _ _ _ n.+1 s =>
      let A := stl_translation \o s in
      let a_min : R := \big[minr/A ord0]_(i < n.+1) A i in
      stl_and a_min A
  | ldl_or _ _ _ 0 _ => -1
  | ldl_or _ _ _ n.+1 s =>
      let A := stl_translation \o s in
      let a_max: R := \big[maxr/A ord0]_(i < n.+1) A i in
      stl_or a_max A
  | ldl_mand _ _ _ _ _ => 0 (* default value, all lemmas are for negation-free formulas *)
  | ldl_mor _ _ _ _ _ => 0 (* default value, all lemmas are for negation-free formulas *)
  | `~ E1 => - {[ E1 ]}
  | E1 `=> E2 => 0 (* default value, all lemmas are for negation-free formulas *)

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
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.

(*version of STL where nu tends to \infty, which we prove in stl.v converges*)
Fixpoint stl_infty_translation {t} (e : @expr R t) {struct e} : type_translation t :=
  match e in expr t return type_translation t with
  | ldl_bool _ _ _ _ true => -1
  | ldl_bool _ _ _ _ false => 1
  | ldl_idx n i => i
  | ldl_real r => r
  | ldl_vec n t => t

  | ldl_and _ _ _ 0 _ => 0
  | ldl_and _ _ _ n.+1 Es  => \big[minr/stl_infty_translation (Es ord0)]_(i < n.+1) stl_infty_translation (Es i)
  | ldl_or _ _ _ 0 _ => 0
  | ldl_or _ _ _ n.+1 Es  => \big[maxr/stl_infty_translation (Es ord0)]_(i < n.+1) stl_infty_translation (Es i)
  | ldl_mand _ _ _ 0 _ => 0
  | ldl_mand _ _ _ n.+1 Es  => \big[minr/stl_infty_translation (Es ord0)]_(i < n.+1) stl_infty_translation (Es i)
  | ldl_mor _ _ _ 0 _ => 0
  | ldl_mor _ _ _ n.+1 Es => \big[maxr/stl_infty_translation (Es ord0)]_(i < n.+1) stl_infty_translation (Es i)

  | ldl_not _ _ _ E1 => - {[ E1 ]}
  | ldl_impl _ _ _ E1 E2 => 0 (* default value, all lemmas are for negation-free formulas *)

  | E1 `== E2 => - `| {[ E1 ]} - {[ E2 ]}|
  | E1 `<= E2 => {[ E2 ]} - {[ E1 ]}

  | ldl_fun n m f => f
  | ldl_fun2 n m l f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
  | ldl_app2 n m l f v1 v2 => {[ f ]} {[ v1 ]} {[ v2 ]}
  | ldl_lookup n v i => {[ v ]} {[ i ]}
end
where "{[ e ]}" := (stl_infty_translation e).

End stl_infty_translation.
Notation "[[ e ]]_stli" := (stl_infty_translation e) : ldl_scope.
