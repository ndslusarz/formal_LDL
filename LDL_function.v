Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import LDL_util.

(******************************************************************************)
(*                                 Logics                                     *)
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
Reserved Notation "[[ e ]]_dl2" (at level 10, format "[[ e ]]_dl2").

Local Open Scope ring_scope.

Section partial.
Context {R : realType}.
Variables (n : nat) (f : 'rV[R]_n -> R).

Definition err_vec {R : ringType} n (i : 'I_n) : 'rV[R]_n :=
  \row_(j < n) (i != j)%:R.

Definition partial (i : 'I_n) (a : 'rV[R]_n) :=
  lim (h^-1 * (f (a + h *: err_vec i) - f a) @[h --> (0:R)^'+]).

(*Search ( (_ <= lim _)%R ). Search ( _ --> _).*)

End partial.

Inductive simple_type : Type :=
| Bool_T : simple_type
| Index_T : nat -> simple_type
| Real_T : simple_type
| Vector_T : nat -> simple_type
| Network_T : nat -> nat -> simple_type.

Inductive comparisons : Type :=
| le_E : comparisons
| eq_E : comparisons.

Section expr.
Context {R : realType}.

Inductive expr : simple_type -> Type :=
  | Real : R -> expr Real_T
  | Bool : bool -> expr Bool_T
  | Index : forall n : nat, 'I_n -> expr (Index_T n)
  | Vector : forall n : nat, n.-tuple R -> expr (Vector_T n)

  (*logical connectives*)
  | and_E : seq (expr Bool_T) -> expr Bool_T
  | or_E : seq (expr Bool_T) -> expr Bool_T
  | impl_E : expr Bool_T -> expr Bool_T -> expr Bool_T
  | not_E : expr Bool_T -> expr Bool_T

  (*arithmetic operations*)
  | add_E : expr Real_T -> expr Real_T -> expr Real_T
  | mult_E : expr Real_T -> expr Real_T -> expr Real_T
  | minus_E : expr Real_T -> expr Real_T

  (* networks and applications *)
  | net : forall n m : nat, (n.-tuple R -> m.-tuple R) -> expr (Network_T n m)
  | app_net : forall n m : nat, expr (Network_T n m) -> expr (Vector_T n) -> expr (Vector_T m)
  | lookup_E n: expr (Vector_T n) -> expr (Index_T n) -> expr Real_T

  (*comparisons*)
  | comparisons_E : comparisons -> expr Real_T -> expr Real_T -> expr Bool_T.

End expr.

Canonical expr_Bool_T_eqType (R : realType) :=
  Equality.Pack (@gen_eqMixin (@expr R Bool_T)).

Notation "a /\ b" := (and_E [:: a; b]).
Notation "a \/ b" := (or_E [:: a; b]).
Notation "a `=> b" := (impl_E a b) (at level 55).
Notation "`~ a" := (not_E a) (at level 75).
Notation "a `+ b" := (add_E a b) (at level 50).
Notation "a `* b" := (mult_E a b) (at level 40).
Notation "`- a" := (minus_E a) (at level 45).

Notation "a `<= b" := (comparisons_E le_E a b) (at level 70).
Notation "a `== b" := (comparisons_E eq_E a b) (at level 70).
Notation "a `!= b" := (`~ (a == b)) (at level 70).
Notation "a `< b" := (a `<= b /\ a `!= b) (at level 70).
Notation "a `>= b" := (b `<= a) (at level 70).
Notation "a `> b" := (b `< a) (at level 70).

Lemma expr_ind' (R : realType) :
  forall P : forall s : simple_type, expr s -> Prop,
       (forall s : R, P Real_T (Real s)) ->
       (forall b : bool, P Bool_T (Bool b)) ->
       (forall (n : nat) (o : 'I_n), P (Index_T n) (Index o)) ->
       (forall (n : nat) (t : n.-tuple R), P (Vector_T n) (Vector t)) ->
       (forall l : seq (expr Bool_T), List.Forall (fun x => P Bool_T x) l -> P Bool_T (and_E l)) ->
       (* (forall l : seq (expr Bool_T), P Bool_T (and_E l)) -> *)
       (forall l : seq (expr Bool_T), List.Forall (fun x => P Bool_T x) l -> P Bool_T (or_E l)) ->
       (forall (l : seq (expr Bool_T)) i, List.Forall (fun x => P Bool_T x) l -> P Bool_T (nth (Bool false) l i)) ->
       (forall e : expr Bool_T,
        P Bool_T e -> forall e0 : expr Bool_T, P Bool_T e0 -> P Bool_T (e `=> e0)) ->
       (forall e : expr Bool_T, P Bool_T e -> P Bool_T (`~ e)) ->
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
       (forall (c : comparisons) (e : expr Real_T),
        P Real_T e -> forall e0 : expr Real_T, P Real_T e0 -> P Bool_T (comparisons_E c e e0)) ->
       forall (s : simple_type) (e : expr s), P s e.
Proof.
move => P H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 s e.
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
  * apply H6; apply F1.
  * apply H7; eauto.
  * apply H8; eauto.
  * apply H9; eauto.
  * apply H10; eauto.
  * apply H11.
  * apply H12; eauto. 
  * apply H13; eauto. 
  * apply H14; eauto. 
Qed.

Section natalia_prod.
Context {R : realType}.

Lemma natalia_prod_01 : forall (x y : R), 0 <= x <= 1 -> 0 <= y <= 1 -> 0 <= natalia_prod x y <= 1.
Proof. by move => x y; rewrite /natalia_prod; nra. Qed.

Lemma natalia_prod_seq_01 (T : eqType) (f : T -> R) (l0 : seq T) :
  (forall i, i \in l0 -> 0 <= f i <= 1) -> (0 <= \big[natalia_prod/0]_(i <- l0) f i <= 1).
Proof.
elim: l0.
- by rewrite big_nil lexx ler01.
- move=> a l0 IH h.
  rewrite big_cons natalia_prod_01 ?h ?mem_head//.
  apply: IH => i il0; apply: h.
  by rewrite in_cons il0 orbT.
Qed.

Lemma natalia_prod_inv (x y : R) :
  (0 <= x <= 1) -> (0 <= y <= 1) ->
    reflect (x = 1 \/ y = 1) (natalia_prod x y == 1).
Proof.
move=> x01 y01; apply: (iffP eqP); rewrite /natalia_prod; nra.
Qed.

Lemma natalia_prod_inv0 (x y : R) :
  (0 <= x <= 1) -> (0 <= y <= 1) ->
    reflect (x = 0 /\ y = 0) (natalia_prod x y == 0).
Proof.
move=> x01 y01; apply: (iffP eqP); rewrite /natalia_prod; nra.
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

End natalia_prod.

Inductive DL := Lukasiewicz | Yager | Godel | product.

Section type_translation.
Context {R : realType}.

Definition type_translation (t:  simple_type) : Type:=
  match t with
  | Bool_T => R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

Definition bool_type_translation (t : simple_type) : Type:=
  match t with
  | Bool_T => bool
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
  end.

Definition dl2_type_translation (t : simple_type) : Type:=
  match t with
  | Bool_T => \bar R (* TODO: this should b [-oo,0] *)
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

Definition stl_type_translation (t : simple_type) : Type:=
  match t with
  | Bool_T => \bar R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

End type_translation.

Section bool_translation.
Context {R : realType}.
Local Open Scope ring_scope.

Fixpoint bool_translation t (e : @expr R t) : bool_type_translation t :=
  match e in expr t return bool_type_translation t with
  | Bool x => x
  | Real r => r%R
  | Index n i => i
  | Vector n t => t

  | and_E Es => foldr andb true (map (@bool_translation Bool_T) Es)
  | or_E Es => foldr orb false (map (@bool_translation Bool_T) Es)
  | impl_E e1 e2 => << e1 >> ==> << e2 >>
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

Lemma bool_translation_andE (Es : seq (expr Bool_T)) :
  bool_translation (and_E Es) = \big[andb/true]_(x <- Es) bool_translation x.
Proof. by rewrite /= foldrE big_map. Qed.

End bool_translation.

Notation "[[ e ]]b" := (bool_translation e).

Section goedel_translation.
Context {R : realType}.
Local Open Scope ring_scope.
Variables (l : DL) (p : R).

Locate "[".

Fixpoint translation t (e: @expr R t) {struct e} : type_translation t :=
    match e in expr t return type_translation t with
    | Bool true => (1%R : type_translation Bool_T)
    | Bool false => (0%R : type_translation Bool_T)
    | Real r => r%R
    | Index n i => i
    | Vector n t => t

    | and_E Es =>
        match l with
        | Lukasiewicz => maxr (sumR (map (@translation _) Es)- (size Es)%:R+1) 0
        | Yager => maxr (1 - ((sumR (map (fun E => (1 - ({[ E ]}: type_translation Bool_T))`^p)%R Es))`^p^-1)) 0
        | Godel => minR (map (@translation _) Es)
        | product => prodR (map (@translation _) Es)
        end
    | or_E Es =>
        match l with
        | Lukasiewicz => minr (sumR (map (@translation _) Es)) 1
        | Yager => minr ((sumR (map (fun E => ({[ E ]} : type_translation Bool_T)`^p) Es))`^p^-1) 1
        | Godel => maxR (map (@translation _) Es)
        | product => natalia_prodR (map (@translation _) Es)
        end
    | impl_E E1 E2 =>
        match l with
        | Lukasiewicz => minr (1 - {[ E1 ]} + {[ E2 ]}) 1
        | Yager => minr (((1 - {[ E1 ]}) `^ p + {[ E2 ]} `^ p) `^ (p^-1)) 1
        | Godel => maxr (1 - {[ E1 ]}) {[ E2 ]}
        | product => 1 - {[ E1 ]} + {[ E1 ]} * {[ E2 ]}
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
Context {R : realType}.

Local Open Scope ereal_scope.

Fixpoint dl2_translation t (e : @expr R t) {struct e} : dl2_type_translation t :=
    match e in expr t return dl2_type_translation t with
    | Bool true => 0
    | Bool false => -oo
    | Real r => r
    | Index n i => i
    | Vector n t => t

    | and_E Es => sumE (map (@dl2_translation _) Es)
    | or_E Es => (-1^+(1+length Es)%nat * (sumE (map (@dl2_translation _) Es)))
    | impl_E E1 E2 => (+oo)%E (* FIX: this case is not covered by DL2 *)
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
Context {R : realType}.
Variables (p : R) (nu : R).
Hypothesis p1 : 1 <= p.
Hypothesis nu0 : 0 < nu.

Local Open Scope ereal_scope.

Fixpoint stl_translation t (e: expr t) : stl_type_translation t :=
    match e in expr t return stl_type_translation t with
    | Bool true => +oo
    | Bool false => -oo
    | Real r => r
    | Index n i => i
    | Vector n t => t

    | and_E Es =>
        let A := map (@stl_translation _) Es in
        let a_min: \bar R := foldr mine (+oo) A in
        let a'_i (a_i: \bar R) := (a_i - a_min) * (fine a_min)^-1%:E in
        if a_min < 0 then
          sumE (map (fun a => a_min * expeR (a'_i a) * expeR (nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * a'_i a)) A)))^-1%:E
        else if a_min > 0 then
          sumE (map (fun a => a * expeR (-nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
             else 0
    | or_E Es => (* TODO: double check *)
        let A := map (@stl_translation _) Es in
        let a_max: \bar R := - (foldr maxe (+oo)%E A) in
        let a'_i (a_i: \bar R) := (- a_i - a_max) * (fine a_max)^-1%:E  in
        if a_max < 0 then
          sumE (map (fun a => a_max * expeR (a'_i a) * expeR (nu%:E * a'_i a)) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
        else if a_max > 0 then
          sumE (map (fun a => a * expeR (-nu%:E * (a'_i a))) A) *
          (fine (sumE (map (fun a => expeR (nu%:E * (a'_i a))) A)))^-1%:E
             else 0
    | impl_E E1 E2 => {[ E1 ]} - {[ E2 ]} (*placeholder for now*)

    | `~ E1 => (- {[ E1 ]})%E

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
where "{[ e ]}" := (stl_translation e).

End stl_translation.

Notation "nu .-[[ e ]]_stl" := (stl_translation nu e).
Notation "[[ e ]]_dl2" := (dl2_translation e).

Section translation_lemmas.
Context {R : realType}.
Local Open Scope ring_scope.
Local Open Scope order_scope.
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

Lemma translate_Bool_T_01 dl (e : expr Bool_T) :
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
  + rewrite /natalia_prodR big_map natalia_prod_seq_01=> //i il0.
    by apply: H => //; rewrite -In_in.
- move/List.Forall_forall in H.
  have [il0|il0] := ltP i (size l0).
    rewrite (H (nth (Bool false) l0 i))//.
    by apply/In_in; rewrite mem_nth.
  by rewrite nth_default//= lexx ler01.
- have := IHe1 e1 erefl JMeq_refl.
  have := IHe2 e2 erefl JMeq_refl.
  move: IHe1 IHe2.
  case: dl; rewrite /=; rewrite /minr/maxr; try case: ifP; rewrite ?cprD ?oppr_le0 ?powR_ge0; nra.
- have := IHe e erefl JMeq_refl.
  move: IHe.
  case dl => //=; by lra.
- case: c => /=; case: ifP => ?.
  - by case: ([[e1]]_dl <= [[e2]]_dl)%R; rewrite lexx ler01.
  - by rewrite le_maxr lexx orbT/= le_maxl ler01 gerBl// le_maxr lexx orbT.
  - by case: ([[e1]]_dl == [[e2]]_dl); rewrite lexx ler01.
  - by rewrite le_maxr lexx orbT/= le_maxl ler01 gerBl// normr_ge0 andTb.
Qed.

Lemma nary_inversion_andE1 (Es : seq (expr Bool_T) ) :
  [[ and_E Es ]]_ l = 1 -> (forall i, i < size Es -> [[ nth (Bool false) Es i ]]_ l = 1).
Proof.
have H := translate_Bool_T_01 l. move: H.
case: l => /=; move => H.
- move/eqP. rewrite maxr01 /sumR eq_sym -subr_eq subrr eq_sym subr_eq0.
  move/eqP; rewrite big_map psumr_eqsize.
  + move => h i iEs.
    move: h => /(_ (nth (Bool false) Es i)).
    apply.
    apply/(nthP (Bool false)). 
    by exists i.
  + move => i //=.
    move: (H i). lra.
- move/eqP.
  rewrite maxr01 eq_sym addrC -subr_eq subrr eq_sym oppr_eq0 powR_eq0 invr_eq0 => /andP [+ _].
  + rewrite /sumR big_map psumr_eq0.
    move => /allP h i iEs.
    apply/eqP.
    move: h => /(_ (nth (Bool false) Es i)).
    rewrite implyTb powR_eq0 subr_eq0 eq_sym (gt_eqF (lt_le_trans _ p1))// ?andbT.
    apply.
    apply/(nthP (Bool false)).
    by exists i.
  + move => i //=.
    move: (H i). rewrite  le_pow_01. 
    * lra. 
    * move: (H i). lra.
- move/eqP.
  rewrite /minR big_map=>/bigmin_eqP/= => h i iEs.
  apply/eqP.
  rewrite eq_sym eq_le.
  rewrite ((andP (H _)).2) h//.
  exact: mem_nth.
- move/eqP. rewrite /prodR big_map.
  move => h i iEs.
  apply (@prod1_01 _ (map (@translation R product p (Bool_T)) Es)) => // [e||].
  - by move=> /mapP[x _ ->].
  - by apply/eqP; rewrite big_map.
  - by apply/mapP; eexists; last reflexivity; exact: mem_nth.
Qed.

Lemma nary_inversion_andE0 (Es : seq (expr Bool_T) ) :
  l <> Lukasiewicz -> l <> Yager ->
    [[ and_E Es ]]_ l = 0 -> (exists (i : nat), ([[ nth (Bool false) Es i ]]_ l == 0) && (i < size Es)%nat).
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
  move/(nthP (Bool false)) : eEs => [i iEs ie].
  by exists i; rewrite ie e0 eqxx.
Qed.

Lemma nary_inversion_orE1 Es :
  l <> Lukasiewicz -> l <> Yager ->
    [[ or_E Es ]]_ l = 1 -> (exists i, ([[ nth (Bool false) Es i ]]_ l == 1) && (i < size Es)%nat).
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
  rewrite /natalia_prodR big_map big_seq.
  elim: Es.
  + by rewrite big_nil eq_sym oner_eq0.
  + move=> a l0 IH.
    rewrite -big_seq big_cons {1}/natalia_prod.
    move/natalia_prod_inv => [|||/eqP].
    * exact: H.
    * by apply: natalia_prod_seq_01.
    * by exists 0%nat; rewrite a0 eq_refl ltn0Sn.
    * by rewrite big_seq; move/IH => [x ?]; exists x.+1.
Qed.

Lemma nary_inversion_orE0 Es :
    [[ or_E Es ]]_ l  = 0 -> (forall i, (i < size Es)%nat -> [[ nth (Bool false) Es i ]]_ l = 0).
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
  suff: ([[nth (Bool false) Es i]]_Yager == 0) && (p != 0).
    by move/andP=>[].
  rewrite -powR_eq0.
  apply: (implyP (h (nth (Bool false) Es i) _)).
    by rewrite mem_nth.
  apply/mapP; exists (nth (Bool false) Es i) => //.
    by rewrite mem_nth.
- rewrite /maxR/natalia_prodR.
  elim: Es => [h i|a l0 IH h]; first by rewrite nth_nil.
  elim => /=[_|].
  + move: h.
    rewrite big_cons big_map {1}/maxr.
    case: ifPn => // /[swap] ->.
    have := H a.
    lra.
  + move=> n h' nl0.
    apply: IH => //.
    move: h; rewrite !big_map big_cons {1}/maxr.
    case: ifPn => // /[swap] ->; rewrite -leNgt => bigle0.
    by apply/eqP; rewrite eq_le bigle0 bigmax_idl le_maxr lexx.
- rewrite /natalia_prodR.
  rewrite big_map.
  elim: Es => // a l0 IH.
  rewrite big_cons => /eqP /natalia_prod_inv0 h.
  case => /=[_|i].
  + apply: (h _ _).1 => //.
    exact: natalia_prod_seq_01.
  + rewrite ltnS => isize.
    apply: IH =>//.
    apply: (h _ _).2 => //.
    exact: natalia_prod_seq_01.
Qed.

Lemma inversion_implE1 e1 e2 :
  l <> Lukasiewicz -> l <> Yager ->
    [[ impl_E e1 e2 ]]_ l = 1 -> [[e1]]_ l = 0 \/ [[e2]]_ l = 1.
Proof.
have He1 := translate_Bool_T_01 l e1.
have He2 := translate_Bool_T_01 l e2.
move: He1 He2.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move=> He1; move=> He2.
- rewrite /maxr; case: ifPn; lra.
- nra.
Qed.

Lemma inversion_implE0 e1 e2 :
  [[ impl_E e1 e2 ]]_ l = 0 -> [[e1]]_ l  = 1 /\ [[e2]]_ l = 0.
Proof.
have He1 := translate_Bool_T_01 l e1.
have He2 := translate_Bool_T_01 l e2.
move: He1 He2.
have p0 := lt_le_trans ltr01 p1.
case: l => /=; move=> He1; move=> He2.
- rewrite /minr; case: ifPn; lra.
- rewrite /minr; case: ifPn => _; last lra.
  have [-> /eqP|e11 /eqP] := eqVneq ([[e1]]_Yager) 0.
  + by rewrite subr0 powR1 powR_eq0 paddr_eq0// ?powR_ge0; lra.
    have [->//|e21] := eqVneq ([[e2]]_Yager) 0.
  + rewrite powR0 ?(gt_eqF p0)// addr0.
    rewrite -powRrM divff ?(gt_eqF p0)// powRr1.
    lra. lra.
  + rewrite powR_eq0 (paddr_eq0 (powR_ge0 _ _) (powR_ge0 _ _)) => /andP [].
    rewrite !powR_eq0.
    lra.
- rewrite /maxr; case: ifPn; lra.
- by nra.
Qed.


Lemma soundness e b :
  l <> Lukasiewicz -> l <> Yager ->
    [[ e ]]_ l = [[ Bool b ]]_ l -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind' => ll ly.
- move: b b0 => [] [] //=; lra.
- rewrite List.Forall_forall in H.
  rewrite [ [[Bool b]]_l ]/=.  
  move: b => [].
  + move/nary_inversion_andE1.
    rewrite [bool_translation (and_E l0)]/= foldrE big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (Bool false).
    by apply: H => //; rewrite ?h// -In_in mem_nth.
  + move/nary_inversion_andE0.
    rewrite [bool_translation (and_E l0)]/= foldrE big_map big_all.
    elim=>// i /andP[/eqP i0 isize].
    apply/allPn; exists (nth (Bool false) l0 i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    by rewrite -In_in mem_nth.
- rewrite List.Forall_forall in H.
  rewrite [ [[Bool b]]_l]/=.
  move: b => [].
  + move/nary_inversion_orE1.
    rewrite [bool_translation (or_E l0)]/= foldrE big_map big_has.
    elim=>// i /andP[/eqP i0 isize].
    apply/hasP; exists (nth (Bool false) l0 i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
  + move/nary_inversion_orE0.
    rewrite [bool_translation (or_E l0)]/= foldrE big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (Bool false).
    by apply/negPf; apply: H => //; rewrite ?h// -In_in mem_nth.
- have /orP[isize|isize] := leqVgt (size l0) i.
    by rewrite !nth_default//=; case: b => ///eqP; rewrite lt_eqF ?ltr01.
  rewrite List.Forall_forall in H => h.
  by apply: H => //; rewrite -In_in mem_nth.
- have {} IHe1 := IHe1 e1 erefl JMeq_refl.
  have {} IHe2 := IHe2 e2 erefl JMeq_refl.
  rewrite [ [[Bool b]]_l ]/=. move: b => [].
  + move/(inversion_implE1 ll ly ).
    case; rewrite [bool_translation (e1 `=> e2)]/=.
    by move/(IHe1 false ll ly) => ->.
    by move/(IHe2 true ll ly) => ->; rewrite implybT.
  + move/(inversion_implE0 ).
    case; rewrite [bool_translation (e1 `=> e2)]/=.
    move/(IHe1 true ll ly) => ->.
    by move/(IHe2 false ll ly) => ->.
- rewrite //=.
  have {} IHe := IHe e erefl JMeq_refl.
  case: b => ?.
  have: [[ e ]]_l = 0 by lra.
  by move/(IHe false) => ->.
  have: [[ e ]]_l = 1 by lra.
  by move/(IHe true) => ->.
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
    * move=> _ ?.
      have : `|(t1 - t2) / (t1 + t2)| == 0 by lra.
      rewrite normr_eq0 mulf_eq0 invr_eq0; lra.
    * rewrite subr_lt0 lter_normr.
      have [|t120] := leP (t1+t2) 0.
      rewrite le_eqVlt => /orP [|t120]; first lra.
      rewrite -mulNr !ltr_ndivlMr// !mul1r opprD opprK.
      lra.
      rewrite -mulNr.
      rewrite !ltr_pdivlMr// !mul1r opprD opprK.
      lra.
    * move=> _ ?.
      have : `|(t1 - t2) / (t1 + t2)| == 1 by lra.
      rewrite eqr_norml.
      nra.
Qed.

End translation_lemmas.

(* this is already in MCA master *)
#[global] Hint Extern 0 (Filter (nbhs _^'+)) =>
  (apply: at_right_proper_filter) : typeclass_instances.

#[global] Hint Extern 0 (Filter (nbhs _^'-)) =>
  (apply: at_left_proper_filter) : typeclass_instances.

Section shadow.

Definition row_of_seq {R : numDomainType} (s : seq R) : 'rV[R]_(size s) :=
  (\row_(i < size s) tnth (in_tuple s) i).

Check row_of_seq.
About MatrixFormula.seq_of_rV.

Definition product_and {R : fieldType} n (xs : 'rV[R]_n) : R :=
  \prod_(x < n) xs ord0 x.

Print MatrixFormula.seq_of_rV.
Print fgraph.


Definition shadow_lifting {R : realType} (f : forall n, 'rV_n -> R) := 
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

Print BSide.
Print itv_bound.

(* this lemma is in MCA master *)
Lemma nonincreasing_at_right_cvgr {R : realType} (f : R -> R) a :
    {in `]a, +oo[, nonincreasing_fun f} ->
    has_ubound (f @` `]a, +oo[) ->
  f x @[x --> a ^'+] --> sup (f @` `]a, +oo[).
Admitted.

From mathcomp Require Import signed.

Lemma nonincreasing_at_right_cvgr_itv {R : realType} (f : R -> R) a b : a < b ->
    {in `]a, +oo[, nonincreasing_fun f} ->
    has_ubound (f @` `]a, b[) ->
  f x @[x --> a ^'+] --> sup (f @` `]a, b[).
Proof.
move=> ab lef ubf; set M := sup _.
have supf : has_sup [set f x | x in `]a, b[].
  split => //; exists (f (a + (b - a)/2)), (a + (b - a)/2) => //=.
  rewrite in_itv/= ltr_addl divr_gt0/= ?subr_gt0 ?ltr0n//.
  by rewrite -ltr_subr_addl ltr_pdivrMr ?ltr0n// ltr_pMr ?subr_gt0// ltr1n.
apply/(@cvgrPdist_le _ [pseudoMetricNormedZmodType R of R^o]) => _/posnumP[e].
have [p ap Mefp] : exists2 p, a < p & M - e%:num <= f p.
  have [_ -[p ap] <- /ltW efp] := sup_adherent (gt0 e) supf.
  exists p; last by rewrite efp.
  by move: ap; rewrite /= in_itv/= => /andP[].
near=> n.
rewrite ler_distl; apply/andP; split; last first.
  rewrite -ler_subl_addr (le_trans Mefp)// lef//.
    by rewrite in_itv/= andbT; near: n; exact: nbhs_right_gt.
  by near: n; exact: nbhs_right_le.
have : f n <= M.
  apply: sup_ub => //=; exists n => //; rewrite in_itv/=; apply/andP; split.
    by near: n; apply: nbhs_right_gt.
  by near: n; apply: nbhs_right_lt.
by apply: le_trans; rewrite ler_subl_addr ler_addl.
Unshelve. all: by end_near. Qed.
(* TODO: generalize nonincreasing_at_right_cvgr *)

(* this lemma is in MCA master *)
Lemma nondecreasing_at_right_cvgr {R : realType} (f : R -> R) a :
    {in `]a, +oo[, nondecreasing_fun f} ->
    has_lbound (f @` `]a, +oo[) ->
  f x @[x --> a ^'+] --> inf (f @` `]a, +oo[).
Admitted.

(* looks doable *)
Lemma monotonous_bounded_is_cvg {R : realType} (f : R -> R) b x y :
  monotonous ([set` Interval (BSide b x) y]) f ->
  has_ubound (f @` setT) ->
  has_lbound (f @` setT) ->
  cvg (f x @[x --> x^'+]).
Proof.
move=> [inc uf lf|dec uf lf].
  apply/cvg_ex.
  exists (sup (f @` [set` Interval (BSide b x) y])).
  admit.
apply/cvg_ex.
exists (inf (f @` [set` Interval (BSide b x) y])).
Admitted.

Lemma shadow_lifting_product_and {R : realType} : @shadow_lifting R product_and.
Proof.
move=> Es i Es01.
rewrite lt_neqAle; apply/andP; split; last first.
  apply: limr_ge.
  - apply: (@monotonous_bounded_is_cvg _ _ false 0 (BRight 1) (* `]0, 1] *)).
    + rewrite {1}/row_of_seq /err_vec.
      admit.
    + admit.
    + admit.
      (* rewrite -int_lbound_has_minimum.  *)
  - near=> x.
    rewrite mulr_ge0//.
    + by rewrite invr_ge0.
    + rewrite subr_ge0 /product_and ler_prod// => j _.
(*      rewrite !ffunE !mxE; apply/andP; split.
      * rewrite /tnth (set_nth_default (0:R))//.
        by have /andP[/ltW] := Es01 j.
      * by rewrite lerDl// mulr_ge0.*) admit.
rewrite /partial.
(*   rewrite /(-all_0_product_partial _).  *)
admit.
Admitted.


End shadow.

Section Lukasiewicz_lemmas.
Context {R : realType}.
Variables (p : R).

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Lukasiewicz_andC e1 e2 :
  [[ e1 /\ e2 ]]_Lukasiewicz = [[ e2 /\ e1 ]]_Lukasiewicz.
Proof.
rewrite /=/sumR ?big_cons ?big_nil.
by rewrite addr0 addr0 (addrC (_ e1)).
Qed.

Lemma Lukasiewicz_orC e1 e2 :
  [[ e1 \/ e2 ]]_Lukasiewicz = [[ e2 \/ e1 ]]_Lukasiewicz.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
by rewrite /= addr0 addr0 (addrC (_ e1)).
Qed.

Lemma Lukasiewicz_orA e1 e2 e3 :
  [[ (e1 \/ (e2 \/ e3)) ]]_Lukasiewicz = [[ ((e1 \/ e2) \/ e3) ]]_Lukasiewicz.
Proof.
have := translate_Bool_T_01 p Lukasiewicz e1.
have := translate_Bool_T_01 p Lukasiewicz e2.
have := translate_Bool_T_01 p Lukasiewicz e3.
rewrite /=/sumR/minR?big_cons ?big_nil.
rewrite /minr.
by repeat case: ifP; lra.
Qed. 

Theorem Lukasiewicz_andA e1 e2 e3 : (0 < p) ->
  [[ (e1 /\ e2) /\ e3]]_Lukasiewicz = [[ e1 /\ (e2 /\ e3) ]]_Lukasiewicz.
Proof.
have := translate_Bool_T_01 p Lukasiewicz e1.
have := translate_Bool_T_01 p Lukasiewicz e2.
have := translate_Bool_T_01 p Lukasiewicz e3. 
rewrite /=/sumR/maxR/minR/natalia_prodR ?big_cons ?big_nil.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
rewrite /maxr.
by repeat case: ifP; lra.
Qed.

End Lukasiewicz_lemmas.

Section Yager_lemmas.
Context {R : realType}.
Variables (p : R).
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Yager_andC e1 e2 :
  [[ e1 /\ e2 ]]_Yager = [[ e2 /\ e1 ]]_Yager.
Proof.
rewrite /=/sumR ?big_cons ?big_nil.
by rewrite /= addr0 addr0 (addrC (_ `^ _)).
Qed.

Lemma Yager_orC e1 e2 :
  [[ e1 \/ e2 ]]_Yager = [[ e2 \/ e1 ]]_Yager.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
by rewrite /= addr0 addr0 (addrC (_ `^ _)).
Qed.

Lemma Yager_orA e1 e2 e3 :
  [[ (e1 \/ (e2 \/ e3)) ]]_Yager = [[ ((e1 \/ e2) \/ e3) ]]_Yager.
Proof.
have p0 : 0 < p by rewrite (lt_le_trans ltr01).
have ? : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 p Yager e1.
have := translate_Bool_T_01 p Yager e2.
have := translate_Bool_T_01 p Yager e3.
rewrite /=/sumR/maxR/minR/natalia_prodR ?big_cons ?big_nil.
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

Theorem Yager_andA e1 e2 e3 : (0 < p) ->
  [[ (e1 /\ e2) /\ e3]]_Yager = [[ e1 /\ (e2 /\ e3) ]]_Yager.
Proof.
move=> p0.
have pneq0 : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 p Yager e1.
have := translate_Bool_T_01 p Yager e2.
have := translate_Bool_T_01 p Yager e3.
rewrite /=/sumR/maxR/minR/natalia_prodR ?big_cons ?big_nil.
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
Context {R : realType}.
Variables (p : R).

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Godel_andC e1 e2 :
  [[ e1 /\ e2 ]]_Godel = [[ e2 /\ e1 ]]_Godel.
Proof.
rewrite /=/minR ?big_cons ?big_nil.
by rewrite /=/minr; repeat case: ifP; lra. 
Qed.

Lemma Godel_orC e1 e2 :
  [[ e1 \/ e2 ]]_Godel = [[ e2 \/ e1 ]]_Godel.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
rewrite /=/maxr; repeat case: ifP; lra.
Qed.

Lemma Godel_orA e1 e2 e3 :
  [[ (e1 \/ (e2 \/ e3)) ]]_Godel = [[ ((e1 \/ e2) \/ e3) ]]_Godel.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil. 
rewrite /maxr.
by repeat case: ifPn => //; lra.
Qed.

Theorem Godel_andA e1 e2 e3 : (0 < p) ->
  [[ (e1 /\ e2) /\ e3]]_Godel = [[ e1 /\ (e2 /\ e3) ]]_Godel.
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
Context {R : realType}.
Variables (p : R).

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma product_andC e1 e2 :
  [[ e1 /\ e2 ]]_product = [[ e2 /\ e1 ]]_product.
Proof. 
rewrite /=/prodR ?big_cons ?big_nil.
by rewrite /= mulr1 mulr1 mulrC. 
Qed.

Lemma product_orC e1 e2 :
  [[ e1 \/ e2 ]]_product = [[ e2 \/ e1 ]]_product.
Proof.
rewrite /=/sumR/maxR/natalia_prodR ?big_cons ?big_nil.
by rewrite /=/natalia_prod addr0 addr0 mulr0 mulr0 subr0 subr0 mulrC -(addrC (_ e2)).
Qed.

Lemma product_orA e1 e2 e3 :
  [[ (e1 \/ (e2 \/ e3)) ]]_product = [[ ((e1 \/ e2) \/ e3) ]]_product.
Proof.
rewrite /=/sumR/natalia_prodR ?big_cons ?big_nil.
rewrite /natalia_prod !addr0 !mulr0 !subr0.
lra.
Qed.

Theorem product_andA e1 e2 e3 : (0 < p) ->
  [[ (e1 /\ e2) /\ e3]]_product = [[ e1 /\ (e2 /\ e3) ]]_product.
Proof.
rewrite /=/sumR/maxR/minR/natalia_prodR ?big_cons ?big_nil.

set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
rewrite /prodR/= !big_cons !big_nil.
lra.
Qed.

End product_lemmas.

Section dl2_lemmas.
Context {R : realType}.
Variables (p : R).

Local Notation "[[ e ]]_dl2" := (@dl2_translation R _ e).

Lemma dl2_andC e1 e2 :
 [[ e1 /\ e2 ]]_dl2 = [[ e2 /\ e1 ]]_dl2.
Proof.
  rewrite /=/sumE ?big_cons ?big_nil.
  by rewrite /= adde0 adde0 addeC. 
Qed. 

End dl2_lemmas.



(* 
Section stl_lemmas.

Lemma andC_stl nu e1 e2 :
  nu.-[[e1 /\ e2]]_stl = nu.-[[e2 /\ e1]]_stl.
Proof.
rewrite /=. case: ifPn.
- rewrite /mine; repeat case: ifPn; intros . 
(*TO DO IN ONE LINE PREFERABLY BECAUSE THIS IS 48 CASES*)

Admitted.  

End stl_lemmas.*)
