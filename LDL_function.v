From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import LDL_util.

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

Reserved Notation "u '``_' i" (at level 3, i at level 2,
  left associativity, format "u '``_' i").
Reserved Notation "'d f '/d i" (at level 10, f, i at next level,
  format "''d'  f  ''/d'  i").

Reserved Notation "{[ e ]}" (format "{[  e  ]}").
Reserved Notation "[[ e ]]b" (at level 10, format "[[  e  ]]b").
Reserved Notation "[[ e ]]_ l" (at level 10, format "[[ e ]]_ l").
Reserved Notation "nu .-[[ e ]]_stl" (at level 10, format "nu .-[[ e ]]_stl").
Reserved Notation "[[ e ]]_dl2" (at level 10, format "[[ e ]]_dl2").

Local Open Scope ring_scope.

Notation "u '``_' i" := (u 0%R i) : ring_scope.

Section partial.
Context {R : realType}.
Variables (n : nat) (f : 'rV[R^o]_n.+1 -> R^o).

Definition err_vec {R : ringType} (i : 'I_n.+1) : 'rV[R]_n.+1 :=
  \row_(j < n.+1) (i == j)%:R.

Definition partial (i : 'I_n.+1) (a : 'rV[R]_n.+1) :=
  lim (h^-1 * (f (a + h *: err_vec i) - f a) @[h --> (0:R)^']).

Lemma partialE (i : 'I_n.+1) (a : 'rV[R]_n.+1) :
  partial i a = 'D_(err_vec i) f a .
Proof.
rewrite /partial /derive/=.
by under eq_fun do rewrite (addrC a).
Qed.

End partial.
Notation "'d f '/d i" := (partial f i).

Lemma nonincreasing_at_right_cvgr {R : realType} (f : R -> R) a (b : itv_bound R) :
    (BRight a < b)%O ->
    {in Interval (BRight a) b &, nonincreasing_fun f} ->
    has_ubound (f @` [set` Interval (BRight a) b]) ->
  f x @[x --> a ^'+] --> sup (f @` [set` Interval (BRight a) b]).
Proof.
move=> ab nif ubf.
exact: realfun.nonincreasing_at_right_cvgr.
Qed.

Lemma nondecreasing_at_right_cvgr {R : realType} (f : R -> R) a (b : itv_bound R) :
    (BRight a < b)%O ->
    {in Interval (BRight a) b &, nondecreasing_fun f} ->
    has_lbound (f @` [set` Interval (BRight a) b]) ->
  f x @[x --> a ^'+] --> inf (f @` [set` Interval (BRight a) b]).
Proof.
move=> ab ndf lbf.
exact: realfun.nondecreasing_at_right_cvgr.
Qed.

Lemma monotonous_bounded_is_cvg {R : realType} (f : R -> R) x y :
  (BRight x < y)%O ->
  monotonous ([set` Interval (BRight x)(*NB(rei): was BSide b x*) y]) f ->
  has_ubound (f @` setT) -> has_lbound (f @` setT) ->
  cvg (f x @[x --> x^'+]).
Proof.
move=> xy [inc uf lf|dec uf lf].
  apply/cvg_ex; exists (inf (f @` [set` Interval (BRight x) y])).
  apply: nondecreasing_at_right_cvgr => //.
    by move=> a b axy bxy ab;rewrite inc//= inE.
  (* TODO(rei): need a lemma? *)
  case: lf => r fr; exists r => z/= [s].
  by rewrite in_itv/= => /andP[xs _] <-{z}; exact: fr.
apply/cvg_ex; exists (sup (f @` [set` Interval (BRight x)(*NB(rei): was (BSide b x)*) y])).
apply: nonincreasing_at_right_cvgr => //.
  by move=> a b axy bxy ab; rewrite dec// inE.
case: uf => r fr; exists r => z/= [s].
by rewrite in_itv/= => /andP[xs _] <-{z}; exact: fr.
Qed.

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

Section product_dl_prod.
Context {R : realType}.

Lemma product_dl_prod_01 : forall (x y : R), 0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= product_dl_prod x y <= 1.
Proof. by move => x y; rewrite /product_dl_prod; nra. Qed.

Lemma product_dl_prod_seq_01 (T : eqType) (f : T -> R) (l0 : seq T) :
  (forall i, i \in l0 -> 0 <= f i <= 1) -> (0 <= \big[product_dl_prod/0]_(i <- l0) f i <= 1).
Proof.
elim: l0.
- by rewrite big_nil lexx ler01.
- move=> a l0 IH h.
  rewrite big_cons product_dl_prod_01 ?h ?mem_head//.
  apply: IH => i il0; apply: h.
  by rewrite in_cons il0 orbT.
Qed.

Lemma product_dl_prod_inv (x y : R) :
  (0 <= x <= 1) -> (0 <= y <= 1) ->
    reflect (x = 1 \/ y = 1) (product_dl_prod x y == 1).
Proof.
move=> x01 y01; apply: (iffP eqP); rewrite /product_dl_prod; nra.
Qed.

Lemma product_dl_prod_inv0 (x y : R) :
  (0 <= x <= 1) -> (0 <= y <= 1) ->
    reflect (x = 0 /\ y = 0) (product_dl_prod x y == 0).
Proof.
move=> x01 y01; apply: (iffP eqP); rewrite /product_dl_prod; nra.
Qed.

Lemma bigsum_0x (T : eqType) f :
  forall [s : seq T], (forall e, e \in s -> 0 <= f e) ->
    (\sum_(j <- s) f j == 0 <-> (forall e, e \in s -> f e = (0:R))).
Proof.
elim.
- by rewrite big_nil.
- move => a l0 h1 h2 .
  rewrite big_cons big_seq.
  rewrite paddr_eq0; last 2 first.
  + by apply: h2; rewrite mem_head.
  + by apply: sumr_ge0 => i il0; apply: h2; rewrite in_cons il0 orbT.
  split.
  + move/andP => [/eqP a0].
    rewrite -big_seq h1 => h3 e.
      by rewrite in_cons => /orP[/eqP->//|el0]; exact: h3.
    by apply: h2; rewrite in_cons e orbT.
  + move=> h3.
    apply/andP; split.
      by apply/eqP; apply: h3; rewrite mem_head.
    rewrite psumr_eq0.
      by apply/allP => x xl0; apply/implyP => _; apply/eqP; apply: h3; rewrite in_cons xl0 orbT.
    by move=> i xl0; apply: h2; rewrite in_cons xl0 orbT.
Qed.

(* NB: not used *)
Lemma bigmax_le' : (* ab: not needed, but maybe worth having instead of bigmax_le? *)
  forall [I : eqType] (r : seq I) (f : I -> R) (P : pred I) (x0 x : R),
    reflect (x0 <= x /\ forall i, i \in r -> P i -> f i <= x)
      (\big[Order.max/x0]_(i <- r | P i) f i <= x).
Proof.
move=> I r f P x0.
elim: r => [x|]; first by rewrite big_nil; apply: (iffP idP);move=>//[->//].
move=> a l0 IH x.
apply: (iffP idP).
- rewrite big_cons {1}/maxr.
  case: ifPn => Pa.
  + case: ifPn => [fabig h|].
    * have /IH[-> h'] := h; split=>//i.
      rewrite in_cons => /orP[/eqP -> _|il0 Pi].
        by apply: le_trans (ltW fabig) h.
      exact: h'.
    rewrite -leNgt => fabig fax.
    have /IH[x0fa h] := fabig.
    split; first apply: (le_trans x0fa fax).
    move=> i.
    rewrite in_cons => /orP[/eqP ->//|il0 Pi].
    apply: le_trans.
    apply: h => //.
    apply: fax.
  + move=> /IH[-> h]; split=>// i.
    rewrite in_cons => /orP[/eqP ->|]; first by move: Pa=> /[swap]->.
    exact: h.
- move=>[x0x h].
  have h' : forall i, i \in l0 -> P i -> f i <= x.
    by move=> i il0 Pi; rewrite h ?in_cons ?il0 ?orbT.
  have /IH h'' := conj x0x h'.
  rewrite big_cons {1}/maxr.
  case: ifPn => Pa//.
  case: ifPn => //_.
  apply: h => //.
  exact: mem_head.
Qed.

End product_dl_prod.

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
        let a_max: \bar R := - (foldr maxe (+oo)%E A) in
        let a'_i (a_i: \bar R) := (- a_i - a_max) * (fine a_max)^-1%:E  in
        if a_max == -oo then -oo
        else if a_max == +oo then +oo
        else if a_max < 0 then
          sumE (map (fun a => a_max * expeR (a'_i a) * expeR (nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
        else if a_max > 0 then
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
Notation "[[ e ]]_dl2" := (dl2_translation e) : ldl_scope.

Section translation_lemmas.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (l : DL) (p : R).
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (@translation R l p _ e).

Lemma translations_Network_coincide:
  forall n m (e : expr (Network_T n m)), [[ e ]]_l = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  [[ e ]]_l = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ p1 _ e2 erefl JMeq_refl).
Qed.

Lemma translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_l = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma translations_Real_coincide (e : expr Real_T):
  [[ e ]]_l = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite translations_Vector_coincide translations_Index_coincide.
Qed.

Lemma translate_Bool_T_01 dl (e : expr Bool_N) :
  0 <= [[ e ]]_ dl <= 1.
Proof.
dependent induction e using expr_ind'.
- rewrite /=; case b; lra.
- move: H. case: dl; rewrite /=; move=> /List.Forall_forall H.
  + rewrite /sumR/maxr. case: ifP.
    * by lra.
    * move=> /negbT; rewrite -leNgt => -> /=.
      rewrite big_map -lerBrDr subrr subr_le0 sum_01// => e el0.
      by rewrite (andP (H e _ _ _ _)).2 //; exact/In_in.
  + rewrite /sumR/maxr. case: ifP.
    * by lra.
    * move=> /negbT; rewrite -leNgt => -> /=.
      by rewrite big_map gerBl ?powR_ge0.
  + apply/andP; split.
    * rewrite /minR big_seq.
      rewrite le_bigmin// => i /mapP[x xl0 ->].
      by apply: (andP (@H _ _ _ _ _)).1 => //; rewrite -In_in.
    * rewrite /minR big_map big_seq.
      rewrite bigmin_idl.
      suff : forall (x y : R), minr x y <= x => // x y.
      by rewrite /minr; case: ifPn; lra.
  + rewrite /prodR.
    apply: prod01 => e.
    move/mapP => [x xl0 ->].
    by apply: H _ _ _ _ _ => //; rewrite -In_in.
- move: H. case: dl; rewrite /=; move=> /List.Forall_forall H.
  + rewrite /sumR/minr. case: ifP.
    * move=> /ltW ->.
      rewrite andbT big_map big_seq sumr_ge0// => e.
      by move=> /In_in/H /(_ e erefl) /(_ _)/andP[|].
    * by lra.
  + rewrite /sumR/minr. case: ifP.
    * move=> /ltW ->.
      by rewrite andbT big_map big_seq powR_ge0.
    * by lra.
  + rewrite /maxR big_map big_seq.
    apply/andP; split.
    * rewrite bigmax_idl.
      suff : forall (x y : R), x <= maxr x y => // x y.
      by rewrite /maxr; case: ifPn; lra.
    * rewrite bigmax_le ?ler01// => i il0.
      by apply: (andP (H _ _ _ _ _)).2 => //; rewrite -In_in.
  + rewrite /product_dl_prodR big_map product_dl_prod_seq_01=> //i il0.
    by apply: H => //; rewrite -In_in.
(*- move/List.Forall_forall in H.
  have [il0|il0] := ltP i (size l0).
    rewrite (H (nth (Bool c false) l0 i))//.
    by apply/In_in; rewrite mem_nth.
  by rewrite nth_default//= lexx ler01.*)
- move: IHe => /(_ e erefl JMeq_refl).
  case dl => //=; set a := [[e]]_ _; lra.
- case: c => /=; case: ifP => ?.
  - by case: ([[e1]]_dl <= [[e2]]_dl)%R; rewrite lexx ler01.
  - by rewrite le_maxr lexx orbT/= le_maxl ler01 gerBl// le_maxr lexx orbT.
  - by case: ([[e1]]_dl == [[e2]]_dl); rewrite lexx ler01.
  - by rewrite le_maxr lexx orbT/= le_maxl ler01 gerBl// normr_ge0 andTb.
Qed.

Lemma nary_inversion_andE1 (Es : seq (expr (Bool_N)) ) :
  [[ and_E  Es ]]_ l = 1 -> (forall i, (i < size Es)%N -> [[ nth (Bool _ false) Es i ]]_ l = 1).
Proof.
have H := translate_Bool_T_01 l. move: H.
case: l => /=; move => H.
- move/eqP. rewrite maxr01 /sumR eq_sym -subr_eq subrr eq_sym subr_eq0.
  move/eqP; rewrite big_map psumr_eqsize.
  + move => h i iEs.
    move: h => /(_ (nth (Bool _ false) Es i)).
    apply.
    apply/(nthP (Bool _ false)). 
    by exists i.
  + move => i //=.
    move: (H i); set a := [[i]]_ _; lra.
- move/eqP.
  rewrite maxr01 eq_sym addrC -subr_eq subrr eq_sym oppr_eq0 powR_eq0 invr_eq0 => /andP [+ _].
  + rewrite /sumR big_map psumr_eq0.
    move => /allP h i iEs.
    apply/eqP.
    move: h => /(_ (nth (Bool _ false) Es i)).
    rewrite implyTb powR_eq0 subr_eq0 eq_sym (gt_eqF (lt_le_trans _ p1))// ?andbT.
    apply.
    apply/(nthP (Bool _ false)).
    by exists i.
  + move => i //=.
    move: (H i). rewrite le_pow_01. 
    * lra. 
    * move: (H i); set a := [[i]]_ _; lra.
- move/eqP.
  rewrite /minR big_map=>/bigmin_eqP/= => h i iEs.
  apply/eqP.
  rewrite eq_sym eq_le.
  rewrite ((andP (H _)).2) h//.
  exact: mem_nth.
- move/eqP. rewrite /prodR big_map.
  move => h i iEs.
  apply (@prod1_01 _ (map (@translation R product p (Bool_T _)) Es)) => // [e||].
  - by move=> /mapP[x _ ->].
  - by apply/eqP; rewrite big_map.
  - by apply/mapP; eexists; last reflexivity; exact: mem_nth.
Qed.

Lemma nary_inversion_andE0 (Es : seq (expr (Bool_N)) ) :
  l <> Lukasiewicz -> l <> Yager ->
    [[ and_E Es ]]_ l = 0 -> (exists (i : nat), ([[ nth (Bool _ false) Es i ]]_ l == 0) && (i < size Es)%nat).
Proof.
have H := translate_Bool_T_01. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move => l1 l2; move/eqP.
  rewrite /minR big_map.
  elim: Es.
  + by rewrite big_nil oner_eq0.
  + move=> a l0 IH.
    rewrite big_cons {1}/minr.
    case: ifPn => _; first by exists 0%nat; rewrite ltn0Sn andbT.
    move/IH => [i i0].
    by exists i.+1.
- move=> l1 l2 /eqP.
  rewrite /prodR big_map prodf_seq_eq0 => /hasP[e eEs/= /eqP e0].
  move/(nthP (Bool _ false)) : eEs => [i iEs ie].
  by exists i; rewrite ie e0 eqxx.
Qed.

Lemma nary_inversion_orE1 (Es : seq (expr (Bool_N)) ) :
  l <> Lukasiewicz -> l <> Yager ->
    [[ or_E Es ]]_ l = 1 -> (exists i, ([[ nth (Bool _ false) Es i ]]_ l == 1) && (i < size Es)%nat).
Proof.
have H := translate_Bool_T_01 l. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move => l1 l2; move/eqP.
  rewrite /maxR big_map big_seq.
  elim: Es.
  + by rewrite big_nil eq_sym oner_eq0.
  + move=> a l0 IH.
    rewrite -big_seq big_cons {1}/maxr.
    case: ifPn => [_|_ a1]; last by exists 0%nat; rewrite a1 ltn0Sn.
    rewrite big_seq; move/IH => [i i1].
    by exists i.+1.
- move => l1 l2 /eqP.
  rewrite /product_dl_prodR big_map big_seq.
  elim: Es.
  + by rewrite big_nil eq_sym oner_eq0.
  + move=> a l0 IH.
    rewrite -big_seq big_cons {1}/product_dl_prod.
    move/product_dl_prod_inv => [|||/eqP].
    * exact: H.
    * by apply: product_dl_prod_seq_01.
    * by exists 0%nat; rewrite a0 eq_refl ltn0Sn.
    * by rewrite big_seq; move/IH => [x ?]; exists x.+1.
Qed.

Lemma nary_inversion_orE0 (Es : seq (expr (Bool_N)) ) :
    [[ or_E Es ]]_ l  = 0 -> (forall i, (i < size Es)%nat -> [[ nth (Bool _ false) Es i ]]_ l = 0).
Proof.
have H := translate_Bool_T_01 l. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move/eqP. rewrite minr10 /sumR.
  rewrite big_map.
  rewrite (@bigsum_0x R _ _ Es) => h i.
    by move=> iEs; apply: h; rewrite mem_nth.
  exact: (andP (translate_Bool_T_01 _ _)).1.
- move/eqP; rewrite minr10 /sumR powR_eq0.
  move/andP => [].
  rewrite (@gt_eqF _ _ (p^-1)) ?invr_gt0//.
  rewrite big_seq big_map psumr_eq0=>[|i]; last by rewrite powR_ge0.
  move/allP => h _ i iEs.
  apply/eqP.
  suff: ([[nth (Bool _ false) Es i]]_Yager == 0) && (p != 0).
    by move/andP=>[].
  rewrite -powR_eq0.
  apply: (implyP (h (nth (Bool _ false) Es i) _)).
    by rewrite mem_nth.
  apply/mapP; exists (nth (Bool _ false) Es i) => //.
    by rewrite mem_nth.
- rewrite /maxR/product_dl_prodR.
  elim: Es => [h i|a l0 IH h]; first by rewrite nth_nil.
  elim => /=[_|].
  + move: h.
    rewrite big_cons big_map {1}/maxr.
    case: ifPn => // /[swap] ->.
    have := H a; set b := [[_]]_ _; lra.
  + move=> n h' nl0.
    apply: IH => //.
    move: h; rewrite !big_map big_cons {1}/maxr.
    case: ifPn => // /[swap] ->; rewrite -leNgt => bigle0.
    by apply/eqP; rewrite eq_le bigle0 bigmax_idl le_maxr lexx.
- rewrite /product_dl_prodR.
  rewrite big_map.
  elim: Es => // a l0 IH.
  rewrite big_cons => /eqP /product_dl_prod_inv0 h.
  case => /=[_|i].
  + apply: (h _ _).1 => //.
    exact: product_dl_prod_seq_01.
  + rewrite ltnS => isize.
    apply: IH =>//.
    apply: (h _ _).2 => //.
    exact: product_dl_prod_seq_01.
Qed.

Lemma soundness (e : expr (Bool_N)) b :
  l <> Lukasiewicz -> l <> Yager ->
    [[ e ]]_ l = [[ Bool _ b ]]_ l -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind' => ll ly.
- move: b b0 => [] [] //=; lra.
- rewrite List.Forall_forall in H.
  rewrite [ [[Bool _ b]]_l ]/=.
  move: b => [].
  + move/nary_inversion_andE1.
    rewrite [bool_translation (and_E l0)]/= foldrE big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (Bool _ false).
    by apply: H  => //; rewrite ?h// -In_in mem_nth.
  + move/nary_inversion_andE0.
    rewrite [bool_translation (and_E l0)]/= foldrE big_map big_all.
    elim=>// i /andP[/eqP i0 isize].
    apply/allPn; exists (nth (Bool _ false) l0 i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    by rewrite -In_in mem_nth.
- rewrite List.Forall_forall in H.
  rewrite [ [[Bool _ b]]_l]/=.
  move: b => [].
  + move/nary_inversion_orE1.
    rewrite [bool_translation (or_E l0)]/= foldrE big_map big_has.
    elim=>// i /andP[/eqP i0 isize].
    apply/hasP; exists (nth (Bool _ false) l0 i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
  + move/nary_inversion_orE0.
    rewrite [bool_translation (or_E l0)]/= foldrE big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (Bool _ false).
    by apply/negPf; apply: H => //; rewrite ?h// -In_in mem_nth.
- move=>/=h; rewrite (IHe e erefl JMeq_refl (~~ b) ll ly) ?negbK//.
  move: h; case: b => /=; lra.
- case: c; rewrite //=; rewrite -!translations_Real_coincide;
  set t1 := _ e1; set t2 := _ e2.
  + case: ifPn => [/eqP ->|e12eq].
    have [] := leP (-t2) t2 => /=; case: b; lra.
    rewrite /maxr.
    have ? : 0 < `|t1 + t2| by rewrite normr_gt0 addr_eq0.
    have ? : 0 < `|t1 + t2|^-1 by rewrite invr_gt0.
    case: b; repeat case: ifPn; try lra; rewrite -?leNgt.
    * rewrite pmulr_llt0; lra.
    * rewrite pmulr_lge0// subr_ge0 => t120 _ ?.
      have : (t1 - t2) / `|t1 + t2| = 0 by lra.
      nra.
    * rewrite pmulr_lge0// subr_ge0 => t120.
      rewrite subr_lt0.
      rewrite ltr_pdivlMr ?normr_gt0 ?addr_eq0// mul1r.
      rewrite lter_norml opprD opprK.
      lra.
    * rewrite pmulr_lge0// => t120.
      rewrite subr_ge0 ler_pdivrMr ?normr_gt0 ?addr_eq0// mul1r.
      rewrite lter_normr => ? ?.
      have : (t1 - t2) / `|t1 + t2| = 1 by lra.
      move/divr1_eq => /eqP.
      rewrite eq_sym eqr_norml; lra.
  + case: ifP => [/eqP ->|e12eq].
    have [] := eqVneq (-t2) t2 => /=; case: b; lra.
    rewrite /maxr.
    case: b; case: ifPn; try lra; rewrite -?leNgt.
    * move=> _ H.
      have : `|(t1 - t2) / (t1 + t2)|%R == 0.
        clear -H.
        simpl in *.
        by lra.
      simpl in *.
      rewrite normr_eq0 mulf_eq0 invr_eq0.
      clear -H e12eq.
      lra.
    * rewrite subr_lt0 lter_normr.
      have [|t120] := leP (t1+t2) 0.
      rewrite le_eqVlt => /orP [|t120]; first lra.
      rewrite -mulNr !ltr_ndivlMr// !mul1r opprD opprK.
      lra.
      rewrite -mulNr.
      rewrite !ltr_pdivlMr// !mul1r opprD opprK.
      lra.
    * move=> H0 H1.
      have : `|(t1 - t2) / (t1 + t2)| == 1.
        simpl in *.
        clear -e12eq H0 H1.
        lra.
      rewrite eqr_norml.
      nra.
Qed.

End translation_lemmas.

(* this is already in MCA master *)
#[global] Hint Extern 0 (Filter (nbhs _^'+)) =>
  (apply: at_right_proper_filter) : typeclass_instances.

#[global] Hint Extern 0 (Filter (nbhs _^'-)) =>
  (apply: at_left_proper_filter) : typeclass_instances.

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

Definition product_and {R : fieldType} n (u : 'rV[R]_n) : R :=
  \prod_(i < n) u ``_ i.

Section shadow_lifting_product_and.
Context {R : realType}.
Variable M : nat.
Hypothesis M0 : M != 0%N.

Lemma shadowlifting_product_andE p : p > 0 ->
  forall i, ('d (@product_and R M.+1) '/d i) (const_mx p) = p ^+ M.
Proof.
move=> p0 i.
rewrite /partial.
have /cvg_lim : h^-1 * (product_and (const_mx p + h *: err_vec i) -
                        product_and (n:=M.+1) (const_mx p))
       @[h --> (0:R)^'] --> p ^+ M.
  rewrite /product_and.
  have H : forall h : R, h != 0 ->
      \prod_(x < M.+1) (const_mx p + h *: err_vec i) 0 x -
      \prod_(x < M.+1) const_mx (m:=M.+1) p 0 x = h * p ^+ M.
    move=> h h0; rewrite [X in X - _](bigD1 i)//= !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> j ji; rewrite !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite [X in _ - X](eq_bigr (fun=> p)); last by move=> *; rewrite mxE.
    rewrite [X in _ - X](bigD1 i)//= -mulrBl addrAC subrr add0r; congr (h * _).
    transitivity (\prod_(i0 in @predC1 [the eqType of 'I_M.+1] i) p).
      by apply: eq_bigl => j; rewrite inE.
    rewrite prodr_const; congr (_ ^+ _).
    by rewrite cardC1 card_ord.
  have : h^-1 * (h * p ^+ M) @[h --> (0:R)^'] --> p ^+ M.
    have : {near (0:R)^', (fun=> p ^+ M) =1 (fun h => h^-1 * (h * p ^+ M))}.
      near=> h; rewrite mulrA mulVf ?mul1r//.
      by near: h; exact: nbhs_dnbhs_neq.
    by move/near_eq_cvg/cvg_trans; apply; exact: cvg_cst.
  apply: cvg_trans; apply: near_eq_cvg; near=> k.
  have <-// := H k.
    congr (_ * (_ - _)).
    apply: eq_bigr => /= j _.
    by rewrite !mxE.
  by near: k; exact: nbhs_dnbhs_neq.
by apply; exact: Rhausdorff.
Unshelve. all: by end_near. Qed.

Corollary shadow_lifting_product_and :
  shadow_lifting (@product_and R M.+1).
Proof.
by move=> p p0 i; rewrite shadowlifting_product_andE// exprn_gt0.
Qed.

End shadow_lifting_product_and.

Definition dl2_and {R : fieldType} n (v : 'rV[R]_n) :=
  \sum_(i < n) v ``_ i.

Section shadow_lifting_dl2_and.
Context {R : realType}.
Variable M : nat.
Hypothesis M0 : M != 0%N.

Lemma shadowlifting_dl2_andE (p : R) : p > 0 ->
  forall i, ('d (@dl2_and _ M.+1) '/d i) (const_mx p) = 1.
Proof.
move=> p0 i.
rewrite /partial.
have /cvg_lim : h^-1 * (dl2_and (const_mx p + h *: err_vec i) -
                        dl2_and (n:=M.+1) (const_mx p))
       @[h --> (0:R)^'] --> (1:R)%R.
  rewrite /dl2_and.
  have H : forall h, h != 0 ->
      \sum_(x < M.+1) (const_mx p + h *: err_vec i) ``_ x -
      \sum_(x < M.+1) (const_mx (n:=M.+1) (m:=1) p) ``_ x = h.
    move=> h h0; rewrite [X in X - _](bigD1 i)//= !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> j ji; rewrite !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite [X in _ - X](eq_bigr (fun=> p)); last by move=> *; rewrite mxE.
    rewrite [X in _ - X](bigD1 i)//= (addrC p h) -addrA.
    by rewrite addrA -(addrA h) addrK.
  have : h^-1 * h @[h --> (0:R)^'] --> (1:R)%R.
    have : {near (0:R)^', (fun=> 1) =1 (fun h => h^-1 * h)}.
      near=> h; rewrite mulVf//.
      by near: h;  exact: nbhs_dnbhs_neq.
    by move/near_eq_cvg/cvg_trans; apply; exact: cvg_cst.
  apply: cvg_trans; apply: near_eq_cvg => /=; near=> k.
  by rewrite H//; near: k; exact: nbhs_dnbhs_neq.
by apply; exact: Rhausdorff.
Unshelve. all: by end_near. Qed.

Corollary shadow_lifting_dl2_and :  shadow_lifting (@dl2_and R M.+1).
Proof. by move=> p p0 i; rewrite shadowlifting_dl2_andE. Qed.

End shadow_lifting_dl2_and.

Section shadow_lifting_stl_and.
Context {R : realType}.
Variable nu : R.
Variable M : nat.
Hypothesis M0 : M != 0%N.
(*add hypothesis nu>0 if needed*)

(* The ones below do not type check yet, need to check if we can extend to ereal *)

Definition min_dev {R : numDomainType} (x : \bar R) (xs : seq \bar R) : \bar R :=
  (x - minE xs) * (fine (minE xs))^-1%:E.

Definition min_devR {R : realType} (x : R) (xs : seq R) : R :=
  (x - minR xs) * (minR xs)^-1.

Local Open Scope ereal_scope.

(*Natalia: will only consider >0 and <0 without edge cases, as to separate cases*)
(* Definition stl_and (xs : seq \bar R) : \bar R :=
  if minE xs == +oo then +oo
  else if minE xs == -oo then -oo (*Check if needed*)
  else if minE xs < 0 then
    sumE (map (fun a => minE xs * expeR (min_dev a xs) * expeR (nu%:E * min_dev a xs)) xs) *
    (fine (sumE (map (fun a => expeR (nu%:E * min_dev a xs)) xs)))^-1%:E
  else if minE xs > 0 then
    sumE (map (fun a => a * expeR (-nu%:E * min_dev a xs)) xs) *
    (fine (sumE (map (fun a => expeR (nu%:E * min_dev a xs)) xs)))^-1%:E
    else 0. *)

(*to do: change map to big operator probably*)

Local Close Scope ereal_scope.

Definition stl_and_gt0 n (v : 'rV[R]_n)  :=
  sumR (map (fun a => a * expR (-nu * min_devR a ( MatrixFormula.seq_of_rV v))) ( MatrixFormula.seq_of_rV v)) *
  (sumR (map (fun a => expR (nu * min_devR a ( MatrixFormula.seq_of_rV v))) ( MatrixFormula.seq_of_rV v)))^-1.

Definition stl_and_lt0 n (v : 'rV[R]_n) :=
  sumR (map (fun a => a * expR (-nu * min_devR a ( MatrixFormula.seq_of_rV v))) ( MatrixFormula.seq_of_rV v)) *
    (sumR (map (fun a => expR (nu * min_devR a ( MatrixFormula.seq_of_rV v))) ( MatrixFormula.seq_of_rV v)))^-1.


 Search (_ `^ _).
Lemma shadowlifting_stl_and_gt0 (p : R) : p > 0 ->
  forall i, ('d (@stl_and_gt0 M.+1) '/d i) (const_mx p) = (M%:R) ^ -1.
Proof.
move=> p0 i.
rewrite /partial.
(* have /cvg_lim : h^-1 * (stl_and_gt0 (const_mx p + h *: err_vec i) -
                        stl_and_gt0 (n:=M.+1) (const_mx p))
       @[h --> (0:R)^'] --> ((M%:R)^ -1):R. *)


Admitted.


End shadow_lifting_stl_and.


Section Lukasiewicz_lemmas.
Local Open Scope ldl_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Lukasiewicz_andC (e1 e2 : expr Bool_N) :
  [[ e1 `/\ e2 ]]_Lukasiewicz = [[ e2 `/\ e1 ]]_Lukasiewicz.
Proof.
rewrite /=/sumR ?big_cons ?big_nil.
by rewrite addr0 addr0 (addrC (_ e1)).
Qed.

Lemma Lukasiewicz_orC (e1 e2 : expr Bool_N) :
  [[ e1 `\/ e2 ]]_Lukasiewicz = [[ e2 `\/ e1 ]]_Lukasiewicz.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
by rewrite /= addr0 addr0 (addrC (_ e1)).
Qed.

Lemma Lukasiewicz_orA (e1 e2 e3 : expr Bool_N) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_Lukasiewicz = [[ ((e1 `\/ e2) `\/ e3) ]]_Lukasiewicz.
Proof.
have := translate_Bool_T_01 p Lukasiewicz e1.
have := translate_Bool_T_01 p Lukasiewicz e2.
have := translate_Bool_T_01 p Lukasiewicz e3.
rewrite /=/sumR/minR?big_cons ?big_nil.
rewrite /minr.
repeat case: ifP; set a := [[_]]__; set b := [[_]]__; set c := [[_]]__; lra.
Qed. 

Theorem Lukasiewicz_andA (e1 e2 e3 : expr Bool_N) : (0 < p) ->
  [[ (e1 `/\ e2) `/\ e3]]_Lukasiewicz = [[ e1 `/\ (e2 `/\ e3) ]]_Lukasiewicz.
Proof.
have := translate_Bool_T_01 p Lukasiewicz e1.
have := translate_Bool_T_01 p Lukasiewicz e2.
have := translate_Bool_T_01 p Lukasiewicz e3. 
rewrite /=/sumR/maxR/minR/product_dl_prodR ?big_cons ?big_nil.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
rewrite /maxr.
by repeat case: ifP; lra.
Qed.

End Lukasiewicz_lemmas.

Section Yager_lemmas.
Local Open Scope ldl_scope.
Context {R : realType}.
Variable p : R.
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Yager_andC (e1 e2 : expr Bool_N) :
  [[ e1 `/\ e2 ]]_Yager = [[ e2 `/\ e1 ]]_Yager.
Proof.
rewrite /=/sumR ?big_cons ?big_nil.
by rewrite /= addr0 addr0 (addrC (_ `^ _)).
Qed.

Lemma Yager_orC (e1 e2 : expr Bool_N) :
  [[ e1 `\/ e2 ]]_Yager = [[ e2 `\/ e1 ]]_Yager.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
by rewrite /= addr0 addr0 (addrC (_ `^ _)).
Qed.

Lemma Yager_orA (e1 e2 e3 : expr Bool_N) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_Yager = [[ ((e1 `\/ e2) `\/ e3) ]]_Yager.
Proof.
have p0 : 0 < p by rewrite (lt_le_trans ltr01).
have ? : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 p Yager e1.
have := translate_Bool_T_01 p Yager e2.
have := translate_Bool_T_01 p Yager e3.
rewrite /=/sumR/maxR/minR/product_dl_prodR ?big_cons ?big_nil.
rewrite ![in _ + _]addr0 addr0 addr0.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
have powRpinv : 1 = 1 `^ p^-1.
  by rewrite powR1.
have powRge1 : forall x, 0 <= x -> 1 <= x `^ p^-1 -> 1 <= x.
  move=> x x0; rewrite {1}powRpinv.
  move/(@ge0_ler_powR _ p (ltW p0)).
  by rewrite -!powRrM !mulVf// powR1 powRr1//; apply; rewrite nnegrE ?powR_ge0.
move => ht3 ht2 ht1.
rewrite {2}/minr. 
case: ifPn => [h1|].
- rewrite -powRrM mulVf ?p0 ?powRr1 ?addr_ge0 ?powR_ge0// addrA.
  rewrite {3}/minr.
  case: ifPn => [h2|].
    by rewrite -powRrM mulVf ?p0 ?powRr1 ?powR_ge0// addr_ge0 ?powR_ge0.
  rewrite -leNgt; move/(powRge1 _ (addr_ge0 (powR_ge0 _ _) (powR_ge0 _ _))) => h2.
  rewrite {2}/minr.
  case: ifPn.
    suff : (1 `^ p + t3 `^ p) `^ p^-1 >= 1.
      set a := (1 `^ p + t3 `^ p) `^ p^-1; lra.
    by rewrite {1}(_: 1 = 1`^p^-1) ?ge0_ler_powR ?powR1 ?invr_ge0 ?(ltW p0) ?nnegrE ?addr_ge0 ?powR_ge0// cprD powR_ge0.
  rewrite -leNgt /minr=> h3.
  case: ifPn => //.
  suff : (t1 `^ p + t2 `^ p + t3 `^ p) `^ p^-1 >= 1.
    set a := (t1 `^ p + t2 `^ p + t3 `^ p) `^ p^-1; lra.
  rewrite powRpinv ge0_ler_powR ?invr_ge0 ?nnegrE ?(ltW p0) ?addr_ge0 ?powR_ge0//.
  apply: le_trans; first exact: h2.
  by rewrite lerDl powR_ge0.
- rewrite -leNgt {1}/minr.
  move/(powRge1 _ (addr_ge0 (powR_ge0 _ _) (powR_ge0 _ _))) => h1.
  case: ifPn => [|_].
    suff : (t1 `^ p + 1 `^ p) `^ p^-1 >= 1.
      set a := (t1 `^ p + 1 `^ p) `^ p^-1; lra.
    by rewrite {1}powRpinv ge0_ler_powR ?invr_ge0 ?(ltW p0) ?nnegrE ?addr_ge0 ?powR_ge0 ?powR1// lerDr powR_ge0.
  rewrite {2}/minr.
  case: ifPn => [h2|_].
    rewrite -powRrM mulVf// powRr1 ?addr_ge0 ?powR_ge0//.
    rewrite /minr.
    case: ifPn => //.
    suff : (t1 `^ p + t2 `^ p + t3 `^ p) `^ p^-1 >= 1.
      set a := (t1 `^ p + t2 `^ p + t3 `^ p) `^ p^-1; lra.
    rewrite {1}powRpinv ge0_ler_powR ?invr_ge0 ?(ltW p0) ?nnegrE ?addr_ge0 ?powR_ge0//.
    apply: le_trans; first exact: h1.
    by rewrite -addrA lerDr powR_ge0.
  rewrite /minr.
  case: ifPn => //.
  suff : (1 `^ p + t3 `^ p) `^ p^-1 >= 1.
    set a := (1 `^ p + t3 `^ p) `^ p^-1; lra.
  rewrite {1}powRpinv ge0_ler_powR ?invr_ge0 ?(ltW p0) ?nnegrE ?addr_ge0 ?powR_ge0//.
  by rewrite powR1 lerDl powR_ge0.
Qed.

Theorem Yager_andA (e1 e2 e3 : expr Bool_N) : (0 < p) ->
  [[ (e1 `/\ e2) `/\ e3]]_Yager = [[ e1 `/\ (e2 `/\ e3) ]]_Yager.
Proof.
move=> p0.
have pneq0 : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 p Yager e1.
have := translate_Bool_T_01 p Yager e2.
have := translate_Bool_T_01 p Yager e3.
rewrite /=/sumR/maxR/minR/product_dl_prodR ?big_cons ?big_nil.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
set a1 := (1 - t1)`^p.
set a2 := (1 - t2)`^p.
set a3 := (1 - t3)`^p.
have a1ge0 : 0 <= a1 by rewrite powR_ge0.
have a2ge0 : 0 <= a2 by rewrite powR_ge0.
have a3ge0 : 0 <= a3 by rewrite powR_ge0.
have powRpinv : 1 = 1 `^ p^-1.
  by rewrite powR1.
have powRle1 : forall x, 0 <= x -> x `^ p^-1 <= 1 -> x <= 1.
  move=> x x0; rewrite {1}powRpinv.
  move/(@ge0_ler_powR _ p (ltW p0)).
  by rewrite -!powRrM !mulVf// powR1 powRr1//; apply; rewrite nnegrE ?powR_ge0.
have powRgt1 : forall x, 0 <= x -> 1 < x `^ p^-1 -> 1 < x.
  move=> x x0; rewrite {1}powRpinv.
  move/(@gt0_ltr_powR _ p p0).
  by rewrite -!powRrM !mulVf// powR1 powRr1//; apply; rewrite in_itv/= ?ler01 ?powR_ge0.
have se_ge0 r := @addr_ge0 R _ _ (@powR_ge0 _ _ r) (@powR_ge0 _ _ r).
rewrite {2}/maxr=> ht3 ht2 ht1.
case: ifPn; rewrite addr0 subr_lt0.
- move/(powRgt1 _ (addr_ge0 a1ge0 a2ge0)) => h1.
  rewrite subr0 powR1 addr0.
  rewrite {3}/maxr; case: ifPn; rewrite addr0.
  + rewrite subr0 subr_lt0 => h2.
    rewrite {1}/maxr; case: ifPn.
    * rewrite subr_lt0 => h3.
      rewrite /maxr; case: ifPn => //.
      rewrite -leNgt subr_ge0.
      move/(powRle1 _ (addr_ge0 (powR_ge0 _ _) (powR_ge0 _ _))).
      rewrite powR1 gerDr -/a1 => h4.
      have -> : a1 = 0 by lra.
      by rewrite add0r powR1 subrr.
    * rewrite -leNgt subr_ge0.
      move/(powRle1 _ (addr_ge0 ler01 (powR_ge0 _ _))).
      rewrite gerDl -/a3 => h3.
      have -> : a3 = 0 by lra.
      rewrite addr0 powR1 subrr.
      rewrite /maxr; case: ifPn => //.
      rewrite -leNgt subr_ge0.
      move/(powRle1 _ (addr_ge0 (powR_ge0 _ _) ler01)).
      rewrite -/a1 gerDr => h5.
      have -> : a1 = 0 by lra.
      by rewrite add0r powR1 subrr.
  + rewrite -leNgt subr_ge0.
    move/(powRle1 _ (addr_ge0 (powR_ge0 _ _) (powR_ge0 _ _))).
    rewrite -/a2 -/a3 => h2.
    rewrite {1}/maxr; case: ifPn.
    * rewrite subr_lt0.
      move/(powRgt1 _ (addr_ge0 ler01 a3ge0)).
      rewrite cprD => h3.
      rewrite opprD opprK addrA subrr add0r -powRrM mulVf// powRr1 ?addr_ge0// addrA.
      rewrite /maxr; case: ifPn => //.
      rewrite -leNgt subr_ge0.
      move/(powRle1 _ (addr_ge0 (addr_ge0 a1ge0 a2ge0) a3ge0)).
      lra.
    * rewrite -leNgt subr_ge0.
      move/(powRle1 _ (addr_ge0 ler01 a3ge0)).
      rewrite cprD => h3.
      have -> : a3 = 0 by lra.
      rewrite !addr0 powR1 subrr.
      rewrite /maxr; case: ifPn => //.
      rewrite -leNgt subr_ge0.
      move/(powRle1 _ (addr_ge0 a1ge0 (powR_ge0 _ _))).
      rewrite opprB addrCA subrr addr0 -powRrM mulVf// powRr1//.
      lra.
- rewrite -leNgt.
  move/(powRle1 _ (addr_ge0 a1ge0 a2ge0)) => h1.
  rewrite {3}/maxr; case: ifPn.
  + rewrite !addr0 !subr0 subr_lt0.
    move/(powRgt1 _ (addr_ge0 a2ge0 a3ge0)) => h2.
    rewrite {2}/maxr; case: ifPn.
    * rewrite subr_lt0 powR1.
      move/(powRgt1 _ (addr_ge0 a1ge0 ler01)).
      rewrite cprD => h3.
      rewrite /maxr; case: ifPn => //.
      rewrite -leNgt subr_ge0.
      move/(powRle1 _ (addr_ge0 (powR_ge0 _ _) a3ge0)).
      rewrite opprB addrCA subrr addr0 -powRrM mulVf// powRr1 ?addr_ge0//.
      lra.
    * rewrite -leNgt subr_ge0 powR1.
      move/(powRle1 _ (addr_ge0 a1ge0 ler01)).
      rewrite gerDr => h3.
      move: h1.
      have -> : a1 = 0 by lra.
      rewrite add0r => h1.
      rewrite add0r powR1 subrr.
      rewrite /maxr; case: ifPn => //.
      rewrite -leNgt subr_ge0.
      move/(powRle1 _ (addr_ge0 (powR_ge0 _ _) a3ge0)).
      rewrite opprB addrCA subrr addr0 -powRrM mulVf// powRr1//.
      lra.
  + rewrite -leNgt subr_ge0 addr0.
    move/(powRle1 _ (addr_ge0 a2ge0 a3ge0)) => h2.
    rewrite {1}opprB (@addrC _ _ (_ - _)) -addrA (@addrC _ (-1)) subrr addr0.
    rewrite -powRrM mulVf// powRr1 ?addr_ge0// addr0.
    rewrite {1}opprB (@addrC _ _ (_ - _)).
    rewrite -[in RHS]addrA (@addrC _ (-1)) subrr addr0.
    by rewrite -powRrM mulVf ?pneq0 ?powRr1 ?addrA ?addr_ge0.
Qed.

End Yager_lemmas.

Section Godel_lemmas.
Local Open Scope ldl_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Godel_idempotence (e : expr Bool_N) : [[ e `/\ e ]]_Godel = [[ e ]]_Godel.
Proof.
rewrite /=/minR ?big_cons ?big_nil.
have := translate_Bool_T_01 p Godel e.
set t1 := _ e.
move => h.
rewrite /=/minr; repeat case: ifP; lra.
Qed.

Lemma Godel_orI (e : expr Bool_N) : [[ e `\/ e ]]_Godel = [[ e ]]_Godel.
Proof.
rewrite /= /maxR !big_cons big_nil.
have /max_idPl -> : 0 <= [[ e ]]_Godel.
  by have /andP[] := translate_Bool_T_01 p Godel e.
by rewrite maxxx.
Qed.

Lemma Godel_andC (e1 e2 : expr Bool_N) :
  [[ e1 `/\ e2 ]]_Godel = [[ e2 `/\ e1 ]]_Godel.
Proof.
rewrite /=/minR ?big_cons ?big_nil.
by rewrite /=/minr; repeat case: ifP; lra. 
Qed.

Lemma Godel_orC (e1 e2 : expr Bool_N) :
  [[ e1 `\/ e2 ]]_Godel = [[ e2 `\/ e1 ]]_Godel.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
rewrite /=/maxr; repeat case: ifP; lra.
Qed.

Lemma Godel_orA (e1 e2 e3 : expr Bool_N) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_Godel = [[ ((e1 `\/ e2) `\/ e3) ]]_Godel.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil. 
rewrite /maxr.
by repeat case: ifPn => //; lra.
Qed.

Theorem Godel_andA (e1 e2 e3 : expr Bool_N) : (0 < p) ->
  [[ (e1 `/\ e2) `/\ e3]]_Godel = [[ e1 `/\ (e2 `/\ e3) ]]_Godel.
Proof.
rewrite /=/sumR/minR !big_cons !big_nil.
have := translate_Bool_T_01 p Godel e1.
have := translate_Bool_T_01 p Godel e2.
have := translate_Bool_T_01 p Godel e3.
set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
move => h1 h2 h3 p0.
rewrite /minr. 
by repeat case: ifPn => //; lra.
Qed.

End Godel_lemmas.

Section product_lemmas.
Local Open Scope ldl_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma product_andC (e1 e2 : expr Bool_N) :
  [[ e1 `/\ e2 ]]_product = [[ e2 `/\ e1 ]]_product.
Proof. 
rewrite /=/prodR ?big_cons ?big_nil.
by rewrite /= mulr1 mulr1 mulrC. 
Qed.

Lemma product_orC (e1 e2 : expr Bool_N) :
  [[ e1 `\/ e2 ]]_product = [[ e2 `\/ e1 ]]_product.
Proof.
rewrite /=/sumR/maxR/product_dl_prodR ?big_cons ?big_nil.
by rewrite /=/product_dl_prod addr0 addr0 mulr0 mulr0 subr0 subr0 mulrC -(addrC (_ e2)).
Qed.

Lemma product_orA (e1 e2 e3 : expr Bool_N) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_product = [[ ((e1 `\/ e2) `\/ e3) ]]_product.
Proof.
rewrite /=/sumR/product_dl_prodR ?big_cons ?big_nil.
rewrite /product_dl_prod !addr0 !mulr0 !subr0.
lra.
Qed.

Theorem product_andA (e1 e2 e3 : expr Bool_N) : (0 < p) ->
  [[ (e1 `/\ e2) `/\ e3]]_product = [[ e1 `/\ (e2 `/\ e3) ]]_product.
Proof.
rewrite /=/sumR/maxR/minR/product_dl_prodR ?big_cons ?big_nil.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
rewrite /prodR/= !big_cons !big_nil.
lra.
Qed.

End product_lemmas.

Lemma prodrN1 {R : realDomainType} T (l : seq T) (f : T -> R) :
  (forall e, f e < 0)%R ->
  sgr (\big[*%R/1%R]_(e <- l) f e) = (- 1) ^+ (size l).
Proof.
move=> f0; elim: l => [|h t ih]; first by rewrite big_nil/= expr0 sgr1.
by rewrite big_cons sgrM ih/= exprS ltr0_sg.
Qed.

Definition sge {R : numDomainType} (x : \bar R) : R :=
  match x with | -oo%E => -1 | +oo%E => 1 | r%:E => sgr r end.

(* NB: this should be shorter *)
Lemma sgeM {R : realDomainType} (x y : \bar R) :
  sge (x * y) = sge x * sge y.
Proof.
move: x y => [x| |] [y| |] //=.
- by rewrite sgrM.
- rewrite mulry/=; have [x0|x0|->] := ltgtP x 0.
  + by rewrite ltr0_sg//= EFinN mulN1e/= mulN1r.
  + by rewrite gtr0_sg//= !mul1e mul1r.
  + by rewrite sgr0 mul0e mul0r/= sgr0.
- rewrite mulrNy/=; have [x0|x0|->] := ltgtP x 0.
  + by rewrite ltr0_sg//= EFinN mulN1e/= mulN1r opprK.
  + by rewrite gtr0_sg//= !mul1e mul1r.
  + by rewrite sgr0 mul0e mul0r/= sgr0.
- rewrite mulyr/=; have [x0|x0|->] := ltgtP y 0.
  + by rewrite ltr0_sg//= EFinN mulN1e/= mulrN1.
  + by rewrite gtr0_sg//= !mul1e mul1r.
  + by rewrite sgr0 mul0e mulr0/= sgr0.
- by rewrite mulyy mulr1.
- by rewrite mulyNy mulrN1.
- rewrite mulNyr/=; have [x0|x0|->] := ltgtP y 0.
  + by rewrite ltr0_sg//= EFinN mulN1e/= mulrN1 opprK.
  + by rewrite gtr0_sg//= !mul1e mulN1r.
  + by rewrite sgr0 mul0e mulr0/= sgr0.
- by rewrite mulNyy mulN1r.
- by rewrite mulrN1 opprK.
Qed.

Lemma lte0_sg {R : numDomainType} (x : \bar R) :
  (x < 0)%E -> sge x = -1.
Proof. by move: x => [x| |]//; rewrite lte_fin => /ltr0_sg. Qed.

Lemma sgeN1_lt0 {R : realDomainType} (x : \bar R) :
  sge x = -1 -> (x < 0)%E.
Proof.
move: x => [x| |]//=.
- by rewrite lte_fin => /eqP; rewrite sgr_cp0.
- by move=> /eqP; rewrite -subr_eq0 opprK -(natrD _ 1%N 1%N) pnatr_eq0.
Qed.

Lemma sge1_gt0 {R : realDomainType} (x : \bar R) : sge x = 1 -> (0 < x)%E.
Proof.
move: x => [x| |]//=.
- by rewrite lte_fin => /eqP; rewrite sgr_cp0.
- by move=> /eqP; rewrite eq_sym -subr_eq0 opprK -(natrD _ 1%N 1%N) pnatr_eq0.
Qed.

Lemma prodeN1 {R : realDomainType} (T : eqType) (l : seq T) (f : T -> \bar R) :
  (forall e, e \in l -> f e < 0)%E ->
  sge (\big[*%E/1%E]_(e <- l) f e) = (- 1) ^+ (size l).
Proof.
elim: l => [|h t ih H]; first by rewrite big_nil/= expr0 sgr1.
rewrite big_cons sgeM ih/=; last first.
  by move=> e et; rewrite H// inE et orbT.
by rewrite exprS lte0_sg// H// mem_head.
Qed.

Lemma prode_seq_eq0 {R : numDomainType} {I : Type} (r : seq I) (P : pred I)
    (F : I -> \bar R) :
  (\big[*%E/1]_(i <- r | P i) F i == 0)%E = has (fun i => P i && (F i == 0)) r.
Proof.
elim: r => /= [|h t ih]; first by rewrite big_nil onee_eq0.
rewrite big_cons; case: ifPn => Ph /=; last by rewrite ih.
by rewrite mule_eq0 ih.
Qed.

(* TODO(rei): move to analysis *)
Lemma nadde_lt0 {R : realFieldType} (x y : \bar R) :
  (x <= 0)%E -> (y <= 0)%E -> (x + y < 0)%E -> ((x < 0) || (y < 0))%E.
Proof.
move: x y => [x| |] [y| |]//; rewrite ?lee_fin ?lte_fin.
- move=> x0 y0; rewrite !ltNge -negb_and; apply: contra.
  by move=> /andP[x0' y0']; rewrite addr_ge0.
- by move=> x0 _ _; rewrite ltNyr orbT.
- by move=> _ y0 _; rewrite ltNyr.
- by move=> _ _ _; rewrite ltNy0.
Qed.

Section dl2_lemmas.
Local Open Scope ldl_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_dl2" := (@dl2_translation R _ e).

Lemma dl2_andC (e1 e2 : expr Bool_N) : [[ e1 `/\ e2 ]]_dl2 = [[ e2 `/\ e1 ]]_dl2.
Proof.
by rewrite /=/sumE ?big_cons ?big_nil /= adde0 adde0 addeC.
Qed.

Lemma dl2_andA (e1 e2 e3 : expr Bool_P) :
  [[ e1 `/\ (e2 `/\ e3) ]]_dl2 = [[ (e1 `/\ e2) `/\ e3 ]]_dl2.
Proof.
by rewrite /=/sumE ?big_cons ?big_nil !adde0 addeA.
Qed.

Lemma dl2_orC (e1 e2 : expr Bool_P) :
 [[ e1 `\/ e2 ]]_dl2 = [[ e2 `\/ e1 ]]_dl2.
Proof.
rewrite /= !big_cons big_nil !mule1; congr *%E.
by rewrite muleC.
Qed.

Lemma dl2_orA (e1 e2 e3 : expr Bool_P) :
  [[ e1 `\/ (e2 `\/ e3) ]]_dl2 = [[ (e1 `\/ e2) `\/ e3 ]]_dl2.
Proof.
rewrite /=.
rewrite !big_cons big_nil !mule1.
congr (_ * _)%E.
rewrite muleCA.
by rewrite !muleA.
Qed.

Lemma dl2_translation_le0 e :
  ([[ e ]]_dl2 <= 0 :> dl2_type_translation Bool_P)%E.
Proof.
dependent induction e using expr_ind' => /=.
- by case: b.
- rewrite /sumE big_map big_seq sume_le0// => t tl.
  move/List.Forall_forall : H => /(_ t); apply => //.
  exact/In_in.
- rewrite big_map big_seq; have [ol|ol] := boolP (odd (length l)).
    rewrite exprS -signr_odd ol expr1 mulrN1 !EFinN oppeK mul1e.
    have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2 != 0)%E; last first.
      move/existsNP : l0 => [/= x /not_implyP[xl /negP/negPn/eqP x0]].
      rewrite le_eqVlt; apply/orP; left.
      rewrite prode_seq_eq0; apply/hasP; exists x => //.
      by rewrite xl x0 eqxx.
    apply/ltW/sgeN1_lt0; rewrite -big_seq prodeN1.
      by rewrite -signr_odd ol expr1.
    move=> e el; rewrite lt_neqAle l0//=.
    by move/List.Forall_forall : H => /(_ e); apply => //; exact/In_in.
  rewrite exprS -signr_odd (negbTE ol) expr0 mulN1r.
  rewrite EFinN mulN1e oppe_le0.
  have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2 != 0)%E; last first.
    move/existsNP : l0 => [/= x /not_implyP[xl /negP/negPn/eqP x0]].
    rewrite le_eqVlt; apply/orP; left.
    rewrite eq_sym prode_seq_eq0; apply/hasP; exists x => //.
    by rewrite xl x0 eqxx.
  apply/ltW/sge1_gt0; rewrite -big_seq prodeN1.
    by rewrite -signr_odd (negbTE ol) expr0.
  move=> e el; rewrite lt_neqAle l0//=.
  by move/List.Forall_forall : H => /(_ e); apply => //; exact/In_in.
- case: c => //=.
  by rewrite lee_fin oppr_le0 le_maxr lexx orbT.
Qed.

(*move to util once proven*)

Lemma psume_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> \bar R) :
    (forall i, P i -> 0 <= F i)%E ->
  (\sum_(i <- r | P i) (F i) == 0)%E = (all (fun i => (P i) ==> (F i == 0%E)) r).
Proof.
elim: r => [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
case: ifPn => pa /=; last exact: ihr.
have [Fa0|Fa0/=] := eqVneq (F a) 0; first by rewrite Fa0 add0r/= ihr.
by apply/negbTE; rewrite padde_eq0;
  [rewrite negb_and Fa0|exact: hr|exact: sume_ge0].
Qed.

Definition is_dl2 b (x : \bar R) := (if b then x == 0 else x < 0)%E.

Lemma dl2_nary_inversion_andE1 (s : seq (expr (Bool_P))) :
  is_dl2 true ([[ and_E s ]]_dl2) ->
  (forall i, (i < size s)%N -> is_dl2 true ([[ nth (Bool _ false) s i ]]_dl2)).
Proof.
rewrite/is_dl2.
elim: s => //= h t ih H [_|]/=.
  move: H; rewrite /sumE big_cons.
  rewrite nadde_eq0//.
  - by move=> /andP[->].
  - exact: dl2_translation_le0.
  - rewrite big_seq_cond; apply: sume_le0 => /= x.
    by rewrite andbT => /mapP[/= e et] ->; exact: dl2_translation_le0.
move=> n; rewrite ltnS => nt /=; apply: ih => //.
move: H; rewrite /sumE big_cons.
rewrite nadde_eq0.
- by move=> /andP[_ ->].
- exact: dl2_translation_le0.
- rewrite big_seq_cond; apply: sume_le0 => /= x.
  by rewrite andbT => /mapP[/= e et] ->; exact: dl2_translation_le0.
Qed.

Lemma dl2_nary_inversion_andE0 (s : seq (expr (Bool_P))) :
  is_dl2 false ([[ and_E s ]]_dl2) ->
  (exists i, (is_dl2 false ([[ nth (Bool _ false) s i ]]_dl2)) && (i < size s)%nat).
Proof.
rewrite/is_dl2.
elim: s => [|h t ih] //=; first by rewrite /sumE big_nil ltxx.
rewrite /sumE big_cons => /nadde_lt0 => /(_ (dl2_translation_le0 _)).
have : (\sum_(j <- [seq [[i]]_dl2 | i <- t]) j <= 0)%E.
  rewrite big_seq_cond; apply: sume_le0 => /= z.
  by rewrite andbT => /mapP[/= e et ->]; exact: dl2_translation_le0.
move=> /[swap] /[apply] /orP[H|/ih[j /andP[j0 jt]]].
  by exists 0%N; rewrite /= H.
by exists j.+1; rewrite /= j0.
Qed.

Lemma dl2_nary_inversion_orE1 (s : seq (expr (Bool_P))) : [[ or_E s ]]_dl2 = 0%E ->
  exists i, ([[ nth (Bool _ false) s i ]]_dl2 == 0%E) && (i < size s)%nat.
Proof.
elim: s => [|h t ih] /=.
  rewrite big_nil mule1 expr1 EFinN => /eqe_oppLRP.
  by rewrite oppe0 => /eqP; rewrite onee_eq0.
move=> /eqP; rewrite mule_eq0 eqe signr_eq0/=.
rewrite big_cons mule_eq0 => /orP[H|/eqP H].
  by exists 0%N; rewrite /= H.
have /ih[j /andP[Hj jt]] : [[or_E t]]_dl2 = 0 by rewrite /= H mule0.
by exists j.+1; rewrite /= Hj.
Qed.

Lemma prode_le0 (A : Type) (l : seq A) (f: A -> \bar R) :
  (forall i, f i <= 0)%E ->
  (((-1) ^+ (length l).+1)%:E * \big[*%E/1]_(j <- l) f j <= 0%R)%E.
Proof.
move=> fle0.
elim: l => [|a l IH].
  by rewrite /= big_nil mule1 lee_fin expr1.
rewrite /= big_cons exprS EFinM (muleC (f a)) -muleA mulN1e.
by rewrite -!muleN muleA mule_le0_ge0// oppe_ge0.
Qed.

Lemma dl2_nary_inversion_orE0 (Es : seq (expr (Bool_P)) ) :
    ([[ or_E Es ]]_dl2  < 0)%E  -> (forall i, (i < size Es)%nat -> ([[ nth (Bool _ false) Es i ]]_dl2 < 0)%E).
Proof.
elim: Es => //= a l IH.
rewrite big_cons muleCA mule_lt0 => /andP[aneq0]/andP[]/[swap] _.
rewrite exprS EFinM -muleA EFinN mulN1e oppe_eq0 => lneq0.
have ale0 := dl2_translation_le0 a.
have alt0 : ([[a]]_dl2 < 0)%E by rewrite lt_neqAle aneq0 ale0.
elim => [_//=|i _].
rewrite ltnS => isize.
apply IH => //.
rewrite lt_neqAle lneq0/= big_map.
apply: prode_le0 => j.
exact: dl2_translation_le0.
Qed.

Lemma dl2_translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  [[ e ]]_dl2 = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ e2 erefl JMeq_refl).
Qed.

Lemma dl2_translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_dl2 = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma dl2_translations_Real_coincide (e : expr Real_T):
  [[ e ]]_dl2 = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite dl2_translations_Vector_coincide dl2_translations_Index_coincide.
Qed.

Lemma maxr0_le :
  forall x : R , (- maxr x 0)%:E = 0%E -> x <= 0.
Proof.
move => r.
rewrite /maxr. case: ifP.
- by lra.
- by move => h; case; lra.
Qed.

Lemma dl2_soundness (e : expr Bool_P) b :
  is_dl2 b ([[ e ]]_dl2) -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind'.
- move: b b0 => [] [] //=.
  by rewrite lt_irreflexive.
- rewrite List.Forall_forall in H. 
  move: b => [].
  + move/dl2_nary_inversion_andE1.
    rewrite [bool_translation (and_E l)]/= foldrE big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (Bool _ false).
    apply: H => //. rewrite ?h// -In_in mem_nth//.
    by rewrite h. 
  + move/dl2_nary_inversion_andE0.
    rewrite [bool_translation (and_E l)]/= foldrE big_map big_all.
    elim=>// i /andP[/eqP i0 isize].
    apply/allPn; exists (nth (Bool _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    * by rewrite -In_in mem_nth.
    * rewrite /is_dl2/=. move: i0.
      by rewrite eqb_id.
- rewrite List.Forall_forall in H.
  move: b => [].
  + rewrite/is_dl2=>/eqP; move/dl2_nary_inversion_orE1.
    rewrite [bool_translation (or_E l)]/= foldrE big_map big_has.
    elim=>// i /andP[/eqP i0 isize].
    apply/hasP; exists (nth (Bool _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
    rewrite /is_dl2/=. by rewrite i0.
  + move/dl2_nary_inversion_orE0.
    rewrite [bool_translation (or_E l)]/= foldrE big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (Bool _ false).
    apply/negPf; apply: H => //. 
    * by rewrite ?h// -In_in mem_nth.
    * by rewrite /is_dl2/= h.
- case: c; rewrite //=; rewrite -!dl2_translations_Real_coincide;
  set t1 := _ e1; set t2 := _ e2; case: b => //.
  + by rewrite/is_dl2=>/eqP; move/maxr0_le; rewrite subr_le0.
  + rewrite/is_dl2 lte_fin oppr_lt0 /maxr; case: ifPn; first by rewrite lt_irreflexive.
    by rewrite subr_gt0 => _; move/lt_geF.
  + by rewrite/is_dl2=>/eqP; case=>/eqP; rewrite oppr_eq0 normr_eq0 subr_eq0.
  + rewrite/is_dl2; rewrite lte_fin oppr_lt0 normr_gt0.
    by rewrite subr_eq0; move/eqP => h; apply/eqP.
Qed.

End dl2_lemmas.

Section stl_lemmas.
Context {R : realType}.
Variables (nu : R).
Hypothesis nu0 : 0 < nu.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.

Lemma andI_stl (e : expr Bool_N) :
  nu.-[[e `/\ e]]_stl = nu.-[[e]]_stl.
Proof.
rewrite /=/sumE !big_cons !big_nil/=.
have [->//|epoo] := eqVneq (nu.-[[e]]_stl) (+oo)%E.
have [->//=|enoo] := eqVneq (nu.-[[e]]_stl) (-oo)%E.
set a_min := mine (nu.-[[e]]_stl) (mine (nu.-[[e]]_stl) +oo)%E.
set a := ((nu.-[[e]]_stl - a_min) * ((fine a_min)^-1)%:E)%E.
have a_min_e : a_min = nu.-[[e]]_stl.
  by rewrite /a_min /mine; repeat case: ifPn => //; rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0%E.
  by rewrite /a a_min_e subee ?mul0e// fin_numE epoo enoo.
rewrite !adde0 !mule0 expeR0 !mule1/= a_min_e.
have : ((nu.-[[e]]_stl + nu.-[[e]]_stl) * ((1 + 1)^-1)%:E)%E = nu.-[[e]]_stl.
  have -> : 1 + 1 = (2 : R) by lra.
  rewrite -(@fineK _ (nu.-[[e]]_stl)); last by rewrite fin_numE epoo enoo.
  by rewrite -EFinD -EFinM mulrDl -splitr.
case: ifPn => [/eqP h|_ ->]; first by rewrite !h.
case: ifPn => [/eqP ->//|?].
case: ifPn => //; rewrite -leNgt => ege0.
case: ifPn => //; rewrite -leNgt => ele0.
apply/eqP.
admit.
Admitted.

Lemma andC_stl (e1 e2 : expr Bool_N) :
  nu.-[[e1 `/\ e2]]_stl = nu.-[[e2 `/\ e1]]_stl.
Proof.
rewrite /=/sumE !big_cons !big_nil /=.
set a_min := mine (nu.-[[e1]]_stl) (mine (nu.-[[e2]]_stl) +oo)%E.
have -> : (mine (nu.-[[e2]]_stl) (mine (nu.-[[e1]]_stl) +oo))%E = a_min.
  by rewrite mineA [X in mine X _]mineC -mineA.
set a1 := ((nu.-[[e1]]_stl - a_min) * ((fine a_min)^-1)%:E)%E.
set a2 := ((nu.-[[e2]]_stl - a_min) * ((fine a_min)^-1)%:E)%E.
set d1 := ((fine (expeR (nu%:E * a1) + (expeR (nu%:E * a2) + 0)))^-1)%:E.
have -> : ((fine (expeR (nu%:E * a2) + (expeR (nu%:E * a1) + 0)))^-1)%:E = d1.
  by rewrite addeCA.
case: ifPn => //.
case: ifPn => //.
case: ifPn => _; first by rewrite addeCA.
by case: ifPn => _; first rewrite addeCA.
Qed.  

(* Lemma orI_stl (e : expr Bool_N) :
  nu.-[[e `\/ e]]_stl = nu.-[[e]]_stl.
Proof.
rewrite /=/sumE !big_cons !big_nil/=.
have [->//|enoo] := eqVneq (nu.-[[e]]_stl) (-oo)%E.
have [->//=|epoo] := eqVneq (nu.-[[e]]_stl) (+oo)%E. 
- admit.
set a_max := maxe (nu.-[[e]]_stl) (maxe (nu.-[[e]]_stl) +oo)%E.
set a := (((- nu.-[[e]]_stl - - a_max) * ((fine (- a_max))^-1)%:E))%E.
have a_max_e : a_max = nu.-[[e]]_stl.
  rewrite /a_max /maxe; repeat case: ifPn => //. (* rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0%E.
  by rewrite /a a_min_e subee ?mul0e// fin_numE epoo enoo.
rewrite !adde0 !mule0 expeR0 !mule1/= a_min_e.
have : ((nu.-[[e]]_stl + nu.-[[e]]_stl) * ((1 + 1)^-1)%:E)%E = nu.-[[e]]_stl.
  have -> : 1 + 1 = (2 : R) by lra.
  rewrite -(@fineK _ (nu.-[[e]]_stl)); last by rewrite fin_numE epoo enoo.
  by rewrite -EFinD -EFinM mulrDl -splitr.
case: ifPn => [/eqP->//|_].
case: ifPn => [_//|]; rewrite -leNgt => ege0.
case: ifPn => [_//|]; rewrite -leNgt => ele0 _.
by apply/eqP; rewrite eq_le ege0 ele0. *)
  (*seems to be contradition 
- my fault or truly not idempotent?*)
Admitted. *)

Lemma orC_stl (e1 e2 : expr Bool_N) :
  nu.-[[e1 `\/ e2]]_stl  = nu.-[[e2 `\/ e1]]_stl.
Proof.
rewrite /=/sumE !big_cons !big_nil /=.
set a_max := maxe (nu.-[[e1]]_stl) (maxe (nu.-[[e2]]_stl) +oo)%E.
have -> : (maxe (nu.-[[e2]]_stl) (maxe (nu.-[[e1]]_stl) +oo))%E = a_max.
  by rewrite maxA [X in maxe X _]maxC -maxA.
set a1 := ((- nu.-[[e1]]_stl - - a_max) * ((fine (- a_max))^-1)%:E)%E.
set a2 := (((- nu.-[[e2]]_stl - - a_max) * ((fine (- a_max))^-1)%:E))%E.
set d1 := ((fine (expeR (nu%:E * a1) + (expeR (nu%:E * a2) + 0)))^-1)%:E.
have -> : ((fine (expeR (nu%:E * a2) + (expeR (nu%:E * a1) + 0)))^-1)%:E = d1.
  by rewrite addeCA.
case: ifPn => // ?.
case: ifPn => // ?.
case: ifPn => [|?].
  by rewrite addeCA.
case: ifPn => // ?.
by rewrite addeCA.
Qed.

Lemma stl_nary_inversion_andE1 (Es : seq (expr Bool_N) ) :
  nu.-[[ and_E Es ]]_stl = +oo%E -> (forall i, (i < size Es)%N -> nu.-[[ nth (Bool _ false) Es i ]]_stl = +oo%E).
Proof.

Admitted.

Lemma stl_nary_inversion_andE0 (Es : seq (expr Bool_N) ) :
  nu.-[[ and_E Es ]]_stl = -oo%E -> (exists (i : nat), (nu.-[[ nth (Bool _ false) Es i ]]_stl == -oo)%E && (i < size Es)%nat).
Admitted.

Lemma stl_nary_inversion_orE1 (Es : seq (expr Bool_N) ) :
  nu.-[[ or_E Es ]]_stl = +oo%E -> (exists i, (nu.-[[ nth (Bool _ false) Es i ]]_stl == +oo)%E && (i < size Es)%nat).
Admitted.

Lemma stl_nary_inversion_orE0 (Es : seq (expr Bool_N) ) :
    nu.-[[ or_E Es ]]_stl = -oo%E -> (forall i, (i < size Es)%nat -> nu.-[[ nth (Bool _ false) Es i ]]_stl = -oo%E).
Admitted.

Lemma stl_translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  nu.-[[ e ]]_stl = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ _ e2 erefl JMeq_refl).
Qed.

Lemma stl_translations_Index_coincide: forall n (e : expr (Index_T n)),
  nu.-[[ e ]]_stl = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma stl_translations_Real_coincide (e : expr Real_T):
  nu.-[[ e ]]_stl = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite stl_translations_Vector_coincide stl_translations_Index_coincide.
Qed.

Lemma stl_soundness (e : expr Bool_N) b :
  nu.-[[ e ]]_stl = nu.-[[ Bool _ b ]]_stl -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind'.
- move: b b0 => [] [] //=.
- rewrite List.Forall_forall in H.
  rewrite [ nu.-[[Bool _ b]]_stl ]/=.  
  move: b => [].
  + move/stl_nary_inversion_andE1.
    rewrite [bool_translation (and_E l)]/= foldrE big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (Bool _ false).
    by apply: H => //; rewrite ?h// -In_in mem_nth.
  + move/stl_nary_inversion_andE0.
    rewrite [bool_translation (and_E l)]/= foldrE big_map big_all.
    elim=>// i /andP[/eqP i0 isize].
    apply/allPn; exists (nth (Bool _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    by rewrite -In_in mem_nth.
- rewrite List.Forall_forall in H.
  rewrite [ nu.-[[Bool _ b]]_stl]/=.
  move: b => [].
  + move/stl_nary_inversion_orE1.
    rewrite [bool_translation (or_E l)]/= foldrE big_map big_has.
    elim=>// i /andP[/eqP i0 isize].
    apply/hasP; exists (nth (Bool _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
  + move/stl_nary_inversion_orE0.
    rewrite [bool_translation (or_E l)]/= foldrE big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (Bool _ false).
    by apply/negPf; apply: H => //; rewrite ?h// -In_in mem_nth.
(*- have /orP[isize|isize] := leqVgt (size l) i.
    by rewrite !nth_default//=; case: b => ///eqP; rewrite lt_eqF ?ltr01.
  rewrite List.Forall_forall in H => h.
  by apply: H => //; rewrite -In_in mem_nth.*)
- rewrite //=.
  have {} IHe := IHe e erefl JMeq_refl.
  case: b => h.
  have: nu.-[[ e ]]_stl = -oo%E.
    by move: h; rewrite /oppe; case: (nu.-[[e]]_stl).
  by move/(IHe false) => ->.
  have: nu.-[[ e ]]_stl = +oo%E.
    by move: h; rewrite /oppe; case: (nu.-[[e]]_stl).
  by move/(IHe true) => ->.
- by case: c; rewrite //=; rewrite -!stl_translations_Real_coincide;
  set t1 := _ e1; set t2 := _ e2; case: b.  
Qed.


Definition is_stl b (x : \bar R) := (if b then x >= 0 else x < 0)%E.


Lemma mine_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (\big[mine/+oo]_(i <- s | P i) f i = +oo <-> forall i, i \in s -> P i -> f i = +oo)%E.
Proof.
elim s=>[|a l IH].
  by split; [move=> _ i; rewrite in_nil|move=>_; rewrite big_nil].
split.
- rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    move=> hlpoo i; rewrite inE => /orP[/eqP -> pa|il pi].
      by rewrite pa in npa.
    exact: IH.1 hlpoo i il pi.
  rewrite {1}/mine; case: ifPn.
    by move=>/[swap]->; rewrite lt_neqAle => /andP[]/[swap]; rewrite leye_eq => /eqP->; rewrite eq_refl.
  rewrite -leNgt=>/[swap] hlpoo. rewrite hlpoo leye_eq => /eqP fapoo i.
  rewrite inE => /orP[/eqP -> _|il pi]; first by rewrite fapoo.
  exact: IH.1 hlpoo i il pi.
- move=> hpoo.
  rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    by apply: IH.2 => i il pi; apply: hpoo => //; rewrite inE il orbT.
  rewrite {1}/mine; case: ifPn.
    rewrite IH.2 ?hpoo ?lt_neqAle ?inE ?eq_refl// => i il pi.
    by apply: hpoo=>//; rewrite inE il orbT.
  rewrite -leNgt IH.2// => i il pi.
  apply: hpoo => //.
  by rewrite inE il orbT.
Qed.

Lemma mine_geP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) (x : \bar R) :
  (x <= \big[mine/+oo]_(i <- s | P i) f i <-> forall i, i \in s -> P i -> x <= f i)%E.
Proof.
elim s=>[|a l IH].
  by split; [move=> _ i; rewrite in_nil//|move=>h; rewrite big_nil leey].
split.
- rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    move=> hlpoo i; rewrite inE => /orP[/eqP -> pa|il pi].
      by rewrite pa in npa.
    exact: IH.1 hlpoo i il pi.
  rewrite {1}/mine; case: ifPn.
    move=>/[swap] le1 le2.
    move: (le_lt_trans le1 le2).
    rewrite lt_neqAle => /andP[] _.
    move/IH=> h1 i.
    rewrite inE => /orP[/eqP->//|il pi].
    exact: h1.
  rewrite -leNgt=>/[swap] hlpoo h2.
  move: (le_trans hlpoo h2) => xlefa i.
  rewrite inE => /orP[/eqP->//|il pi].
  exact: IH.1.
- move=> hpoo.
  rewrite big_cons.
  case: ifPn => [pa|npa]; last first.
    by apply: IH.2 => i il pi; apply: hpoo => //; rewrite inE il orbT.
  rewrite {1}/mine; case: ifPn => [_|].
    by rewrite hpoo// inE eq_refl.
  rewrite -leNgt IH.2// => i il pi.
  by rewrite hpoo// inE il orbT.
Qed.

Lemma sume_gt0 (I : Type) (r : seq I) (P : pred I) (F : I -> \bar R) :
  (forall i : I, P i -> 0 <= F i)%E ->
  (exists i : I, P i /\ 0 < F i)%E ->
  (0 < \sum_(i <- r | P i) F i)%E.
Admitted.

Lemma mine_lt (I : Type) (r : seq I) (P : pred I) (f : I -> \bar R) x :
  (\big[mine/+oo]_(i <- r | P i) f i < x)%E
  -> exists i, P i /\ (f i < x)%E.
Admitted.

Lemma stl_nary_inversion_andE1' (Es : seq (expr Bool_P) ) :
  is_stl true (nu.-[[ and_E Es ]]_stl) -> (forall i, (i < size Es)%N -> is_stl true (nu.-[[ nth (Bool false false) Es i ]]_stl)).
Proof.
rewrite/is_stl/= foldrE big_map.
case: ifPn => [//|hnoo].
case: ifPn => [/eqP min_apoo _|hpoo].
  move=> i isize.
  move: ((mine_eqyP _ _ _).1 min_apoo (nth (Bool false false) Es i)).
  by rewrite mem_nth// => ->.
case: ifPn=>[hminlt0|].
  rewrite/sumE.
  rewrite leNgt !big_map.
  rewrite mule_lt0_gt0//; last first.
  rewrite lte_fin invr_gt0 fine_gt0//.
    apply/andP;split.
      rewrite big_seq_cond sume_gt0//.
      move=> i /andP[iEs _]; apply: expeR_ge0.
      have := hminlt0; rewrite big_seq_cond.
      move/mine_lt => [i [iEs]hilt0].
      exists i; split.
        exact: iEs.
      rewrite expeR_gt0//.
      rewrite ltNye !mule_eq_ninfty.
      rewrite !lte_fin !nu0/=.
      rewrite !negb_or !negb_and -!leNgt/= andbT !orbT/= (ltW nu0)/= -!big_seq_cond.
      rewrite andbT invr_le0 invr_ge0 fine_le0 ?orbT ?(ltW hminlt0)//=.
      rewrite -ltey lte_add_pinfty//.
        by apply: lt_trans; first exact: hilt0.
      by rewrite lte_oppl/= ltNye.
    apply: lte_sum_pinfty => i _.
    admit.
  admit.
(* rewrite -leNgt big_map mine_geP/= => h _ i isize. *) (*this errors out now?*)
(* by apply: h => //; rewrite mem_nth. *)
Admitted.

Lemma stl_nary_inversion_andE0' (Es : seq (expr Bool_P) ) :
  is_stl false (nu.-[[ and_E Es ]]_stl) -> (exists (i : nat), is_stl false (nu.-[[ nth (Bool false false) Es i ]]_stl)%E && (i < size Es)%nat).
Proof.
rewrite/is_stl/= foldrE !big_map.
case: ifPn => [/eqP|hpoo].
  by rewrite lt_neqAle leye_eq => _ /andP[_ /eqP].
case: ifPn => [|].
  (* move/bigmin_ltP. *) admit.
rewrite -leNgt => hge0.
case: ifPn => [hgt0|].
  (* sumE _ < 0 but it's positive *) admit.
by rewrite lt_irreflexive.
Admitted.

(* Lemma maxe_eqyP (T : eqType) (s : seq T) (P : pred T) (f : T -> \bar R) :
  (- (\big[maxe/+oo]_(i <- s | P i) f i) = -oo <-> exists i, i \in s -> P i -> f i = +oo)%E.
Proof.
elim s=>[|a l IH].
Admitted. *)

(*Natalia: I need the maxe_eqyP to match the goal in both or inversions - but can't come up
  with anything from knowing max_apoo that would give -oo, if anything the only
result is that there exists some value in Es that is +oo - does the inversion break?*)

Lemma oppeey (x : \bar R) : ((- x == +oo) = (x == -oo))%E.
Proof. by case: x. Qed.

Lemma stl_nary_inversion_orE1' (Es : seq (expr Bool_N) ) :
  is_stl true (nu.-[[ or_E Es ]]_stl) -> (exists i, is_stl true (nu.-[[ nth (Bool _ false) Es i ]]_stl) && (i < size Es)%nat).
Proof.
rewrite/is_stl/= foldrE !big_map.
case: ifPn => [/eqP//|_].
case: ifPn => [|].
rewrite oppeey.
case: h.
Admitted.

Lemma stl_nary_inversion_orE0' (Es : seq (expr Bool_P) ) :
    is_stl false (nu.-[[ or_E Es ]]_stl) -> (forall i, (i < size Es)%nat -> is_stl false (nu.-[[ nth (Bool false false) Es i ]]_stl)).
Admitted.

Lemma stl_soundness' (e : expr Bool_P) b :
  is_stl b (nu.-[[ e ]]_stl) -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind'.
- move: b b0 => [] [] //=.
- rewrite List.Forall_forall in H.
  move: b => []. rewrite /is_stl.
  + move/stl_nary_inversion_andE1'.
    rewrite [bool_translation (and_E l)]/= foldrE big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (Bool _ false).
    by apply: H => //; rewrite ?h// -In_in mem_nth.
  + move/stl_nary_inversion_andE0'.
    rewrite [bool_translation (and_E l)]/= foldrE big_map big_all.
    elim=>// i /andP[i0 isize].
    apply/allPn; exists (nth (Bool _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    by rewrite -In_in mem_nth.
- rewrite List.Forall_forall in H.
  move: b => [].
  + move/stl_nary_inversion_orE1'.
    rewrite [bool_translation (or_E l)]/= foldrE big_map big_has.
    elim=>// i /andP[i0 isize].
    apply/hasP; exists (nth (Bool _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
  + move/stl_nary_inversion_orE0'.
    rewrite [bool_translation (or_E l)]/= foldrE big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (Bool _ false).
    by apply/negPf; apply: H => //; rewrite ?h// -In_in mem_nth.
- case: c.
  + by case: b; rewrite /is_stl/= ?lee_fin ?lte_fin ?ltNge subr_ge0 !stl_translations_Real_coincide// => /negbTE.
  + case: b; rewrite /is_stl/= ?lee_fin ?lte_fin !stl_translations_Real_coincide.
    by rewrite oppr_ge0 normr_le0 subr_eq0.
    by rewrite oppr_lt0 normr_gt0 subr_eq0 => /negbTE.
Qed.


End stl_lemmas.
