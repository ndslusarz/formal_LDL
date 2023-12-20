Require Import Coq.Program.Equality.

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder. 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.

Reserved Notation "[[ e ]]" (format "[[  e  ]]").

Section hyperbolic_function.

Variable R : realType.
Local Open Scope ring_scope.


Definition sinh (x : R) := (expR x - expR (- x)) / 2.
Definition cosh (x : R) := (expR x + expR (- x)) / 2.
Definition tanh (x : R) := sinh x / cosh x.

End hyperbolic_function.

Local Open Scope ring_scope.

(*move to a separate file*)
Lemma sum_01{R : numDomainType} (I : eqType) (s : seq I) (f : I -> R) :
  (forall i, i \in s -> f i <= 1) -> \sum_(i <- s) f i <= (size s)%:R.
Proof.
move=> s01; rewrite -sum1_size natr_sum big_seq [leRHS]big_seq.
by rewrite ler_sum// => r /s01 /andP[].
Qed. 

Lemma In_in (I : eqType) (s : seq I) e : e \in s <-> List.In e s.
Proof.
elim: s => //= h t ih; split=> [|[<-|/ih] ].
- by rewrite inE => /predU1P[->|/ih]; [left|right].
- by rewrite mem_head.
- by rewrite inE => ->; rewrite orbT.
Qed.

Lemma maxr01 {R : realType} (x : R) : (maxr x 0 == 1) = (x == 1).
Proof. rewrite/maxr; case: ifP=>//; lra. Qed.

Lemma minr10 {R : realType} (x : R) : (minr x 1 == 0) = (x == 0).
Proof. rewrite /minr; case: ifP=>//; lra. Qed.

Lemma prod1 {R : realType} (e1 e2 : R) :
  0 <= e1 <= 1 -> 0 <= e2 <= 1 -> (e1 * e2 == 1) = ((e1 == 1) && (e2 == 1)).
Proof.
nra.
Qed.

Lemma prod01 {R : realType} [s : seq R] : 
  (forall e, e \in s -> 0 <= e <= 1) -> (0 <= \prod_(j <- s) j <= 1).
Proof.
elim: s => [_|e0].
- by rewrite big_nil ler01 lexx.
- move=> s IH es01.
  rewrite big_cons.
  have h0 : (0 <= \prod_(j <- s) j <= 1)%R.
    by apply: IH => e es; apply: es01; rewrite in_cons es orbT.
  have : (0 <= e0 <= 1)%R.
    by apply: es01; rewrite in_cons eq_refl.
  nra.
Qed.


Lemma psumr_eqsize {R : realType} :
  forall (I : eqType) (r : seq I) [F : I -> R],
  (forall i : I, F i <= 1)%R ->
  (\sum_(i <- r) F i = (size r)%:R) <-> forall i, i \in r -> (F i = 1).
Proof.
move => I r F h1.
elim: r.
- by rewrite big_nil.
- move => a s IH.
  split.
  + have : (\sum_(i <- s) F i <= (size s)%:R)%R.  
      by apply: sum_01 => i _.
    rewrite /= le_eqVlt big_cons => /orP[/eqP h|h].
      rewrite -natr1 addrC h.
      move/addrI => h' i.
      rewrite in_cons => /orP[/eqP ->|ils]; first by rewrite h'.
      exact: IH.1.
    have: F a + \sum_(j <- s) F j < (size (a :: s))%:R.
      rewrite /= -nat1r.
      move: h.
      set x := \sum_(i <- s) F i.
      set y := size s.
      have := h1 a.
      lra.
    set x := F a + \sum_(j <- s) F j.
    set y := ((size (a :: s)))%:R.
    lra.
  + move=> h.
    rewrite /= -nat1r big_cons h.
      by apply: congr1; apply: IH.2 => i ias; apply: h; rewrite in_cons ias orbT.
    by rewrite in_cons eq_refl//.
Qed.

Lemma bigmin_eqP {R : realType}:
  forall (x : R) [I : eqType] (s : seq I) (F : I -> R),
  reflect (forall i : I, i \in s -> (x <= F i)) (\big[minr/x]_(i <- s) F i == x).
Proof.
move => x I s F.
have minrl : forall (x y : R), minr x y <= x => //. (* TODO: this should exist *)
  by move => v w; rewrite /minr; case: ifPn; rewrite ?le_refl -?leNgt.
apply: (iffP eqP) => [<- i|].
- elim: s => // a s IH.
  rewrite in_cons => /orP[/eqP<-|si].
  + by rewrite big_seq big_cons mem_head minrl.
  + by rewrite big_cons minC; apply: le_trans (IH si); exact: minrl.
- elim: s => [h|i l IH h].
  + by rewrite big_nil.
  + rewrite big_cons IH ?min_r ?h ?mem_head// => a al.
    by rewrite h// in_cons al orbT.
Qed.

Lemma le_pow_01 {R : realType} (x p0 : R ):
  0 <= x <= 1 -> (0 <= (1 - x) `^ p0).
Proof.
by rewrite powR_ge0.
Qed.
(*end the move to new document*)

Section partial.
Context {R : realType}.
Variables (n : nat) (f : 'rV[R]_n -> R).

Definition err_vec {R : ringType} n (i : 'I_n) : 'rV[R]_n :=
  \row_(j < n) (i != j)%:R.

Definition partial (i : 'I_n) (a : 'rV[R]_n) :=
  lim (h^-1 * (f (a + h *: err_vec i) - f a) @[h --> (0:R)^'+]).

Search ( (_ <= lim _)%R ). Search ( _ --> _).

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

Variable R : realType.
Section expr.


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
  | comparisons_E : comparisons -> expr Real_T -> expr Real_T -> expr Bool_T
.
End expr.

Canonical expr_Bool_T_eqType := Equality.Pack (@gen_eqMixin (expr Bool_T)).

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

Lemma expr_ind' :
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

Inductive DL := Lukasiewicz | Yager | Godel | product.
Variable (l : DL).
Variable (p : R).
Variable (p1 : 1 <= p).
Variable (nu : R).
Variable (nu0 : 0 < nu).

Definition natalia_prod : R -> R -> R := (fun a1 a2 => a1 + a2 - a1 * a2).

Definition sumR (Es : seq R) : R := \sum_(i <- Es) i.
Definition prodR (Es : seq R) : R := \prod_(i <- Es) i.
Definition natalia_prodR (Es : seq R) : R := \big[natalia_prod/0]_(i <- Es) i.
Definition minR (Es : seq R) : R := \big[minr/1]_(i <- Es) i.
Definition maxR (Es : seq R) : R := \big[maxr/0]_(i <- Es) i.


Fixpoint translation t (e: expr t) {struct e} : type_translation t :=
    match e in expr t return type_translation t with
    | Bool true => (1%R : type_translation Bool_T)
    | Bool false => (0%R : type_translation Bool_T)
    | Real r => r%R
    | Index n i => i
    | Vector n t => t

    | and_E Es =>
        match l with
        | Lukasiewicz => maxr (sumR (map (@translation _) Es)- (size Es)%:R+1) 0
        | Yager => maxr (1 - ((sumR (map (fun E => (1 - ([[ E ]]: type_translation Bool_T))`^p)%R Es))`^p^-1)) 0
        | Godel => minR (map (@translation _) Es)
        | product => prodR (map (@translation _) Es)
        end
    | or_E Es =>
        match l with
        | Lukasiewicz => minr (sumR (map (@translation _) Es)) 1
        | Yager => minr ((sumR (map (fun E => ([[ E ]] : type_translation Bool_T)`^p) Es))`^p^-1) 1
        | Godel => maxR (map (@translation _) Es)
        | product => natalia_prodR (map (@translation _) Es)
        end
    | impl_E E1 E2 =>
        match l with
        | Lukasiewicz => minr (1 - [[ E1 ]] + [[ E2 ]]) 1
        | Yager => minr (((1 - [[ E1 ]]) `^ p + [[ E2 ]] `^ p) `^ (p^-1)) 1
        | Godel => maxr (1 - [[ E1 ]]) [[ E2 ]]
        | product => 1 - [[ E1 ]] + [[ E1 ]] * [[ E2 ]]
        end

    | `~ E1 => 1 - [[ E1 ]]

    (*simple arithmetic*)
    | E1 `+ E2 => [[ E1 ]] + [[ E2 ]]
    | E1 `* E2 => [[ E1 ]] * [[ E2 ]]
    | `- E1 => - [[ E1 ]]

    (*comparisons*)
    | E1 `== E2 => if [[ E1 ]] == -[[ E2 ]] then ([[ E1 ]] == [[ E2 ]])%:R else maxr (1 - `|([[ E1 ]] - [[ E2 ]]) / ([[ E1 ]] + [[ E2 ]])|) 0
    | E1 `<= E2 => if [[ E1 ]] == -[[ E2 ]] then ([[ E1 ]] <= [[ E2 ]])%R%:R else maxr (1 - maxr (([[ E1 ]] - [[ E2 ]]) / `|[[ E1 ]] + [[ E2 ]]|) 0) 0

    | net n m f => f
    | app_net n m f v => (translation f) (translation v)
    | lookup_E n v i => tnth (translation v) (translation i)
    end
where "[[ e ]]" := (translation e).

Definition sumE (Es : seq \bar R) : \bar R := \sum_(i <- Es) i.

Definition dl2_type_translation (t: simple_type) : Type:=
  match t with
  | Bool_T => \bar R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

Open Scope ereal_scope.

Reserved Notation "[[ e ]]".
Fixpoint dl2_translation t (e: expr t) {struct e} : dl2_type_translation t :=
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
    | E1 `+ E2 => ([[ E1 ]] + [[ E2 ]])%R
    | E1 `* E2 => ([[ E1 ]] * [[ E2 ]])%R
    | `- E1 => (- [[ E1 ]])%R

    (*comparisons*)
    | E1 `== E2 => (- `| [[ E1 ]] - [[ E2 ]]|)%:E
    | E1 `<= E2 => (- maxr ([[ E1 ]] - [[ E2 ]]) 0)%:E

    | net n m f => f
    | app_net n m f v => [[ f ]] [[ v ]]
    | lookup_E n v i => tnth [[ v ]] [[ i ]]
    end
where "[[ e ]]" := (dl2_translation e). 

Definition stl_type_translation (t: simple_type) : Type:=
  match t with
  | Bool_T => \bar R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
end.

Definition expeR (x : \bar R) := 
  match x with 
  | EFin r => (expR r)%:E
  | +oo => +oo
  | -oo => 0
  end.

Reserved Notation "[[ e ]]".
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
    | impl_E E1 E2 => [[ E1 ]] - [[ E2 ]] (*placeholder for now*)

    | `~ E1 => (- [[ E1 ]])%E

    (*simple arithmetic*)
    | E1 `+ E2 => ([[ E1 ]] + [[ E2 ]])%R
    | E1 `* E2 => ([[ E1 ]] * [[ E2 ]])%R
    | `- E1 => (- [[ E1 ]])%R

    (*comparisons*)
    | E1 `== E2 => (- `| [[ E1 ]] - [[ E2 ]]|)%:E
    | E1 `<= E2 => (- maxr ([[ E1 ]] - [[ E2 ]]) 0)%:E

    | net n m f => f
    | app_net n m f v => [[ f ]] [[ v ]]
    | lookup_E n v i => tnth [[ v ]] [[ i ]]
    end
where "[[ e ]]" := (stl_translation e).

Definition bool_type_translation (t: simple_type) : Type:=
  match t with
  | Bool_T => bool
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Network_T n m => n.-tuple R -> m.-tuple R
  end.


Local Open Scope ring_scope.

Reserved Notation "<< e >>".
Fixpoint bool_translation t (e: expr t) : bool_type_translation t :=
  match e in expr t return bool_type_translation t with
  | Bool x => x
  | Real r => r%R
  | Index n i => i
  | Vector n t => t

  | and_E Es => foldr ( andb ) true (map (@bool_translation Bool_T) Es)
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

End translation_def.

Reserved Notation "[[ e ]]_ l" (at level 10, format "[[ e ]]_ l").
Reserved Notation "nu .-[[ e ]]_stl" (at level 10, format "nu .-[[ e ]]_stl").
Reserved Notation "[[ e ]]_dl2" (at level 10, format "[[ e ]]_dl2").

Section translation_lemmas.
Local Open Scope ring_scope.
Local Open Scope order_scope.

Variable (l : DL).
Variable (p : R).
Variable (p1 : 1 <= p).

Local Notation "[[ e ]]_ l" := (translation l p e).
Local Notation "<< e >>_ l" := (bool_translation e) (at level 10, format "<< e >>_ l").
Local Notation "nu .-[[ e ]]_stl" := (stl_translation nu e) (at level 10).
Local Notation "[[ e ]]_dl2" := (dl2_translation e) (at level 10, format "[[ e ]]_dl2").

Lemma translations_Network_coincide:
  forall n m (e : expr (Network_T n m)),
    [[ e ]]_l = << e >>_l.
Proof.
dependent induction e => //=.
Qed.

Lemma translations_Vector_coincide: forall n (e : expr (Vector_T n)),
  [[ e ]]_l = << e >>_l.
Proof.
dependent induction e => //=.
by rewrite translations_Network_coincide (IHe2 p1 _ e2 erefl JMeq_refl).
Qed.

Lemma translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_l = << e >>_l.
Proof.
dependent induction e => //=.
Qed.

Lemma translations_Real_coincide (e : expr Real_T):
  [[ e ]]_l = << e >>_l.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite translations_Vector_coincide translations_Index_coincide.
Qed.

(* NB(rei): this lemma exists in MathComp-Analysis but maybe in a slightly
   different form depending on your version, might be removed at to some point
   but no hurry *)
Lemma gt0_ltr_powR (r : R) : 0 < r ->
  {in `[0, +oo[ &, {homo (@powR R) ^~ r : x y / x < y >-> x < y}}.
Proof.
move=> r0 x y; rewrite !in_itv/= !andbT !le_eqVlt => /predU1P[<-|x0].
  move=> /predU1P[<-|y0 _]; first by rewrite ltxx//.
  by rewrite powR0 ?(gt_eqF r0)// powR_gt0.
move=> /predU1P[<-|y0]; first rewrite ltNge ltW//.
by rewrite /powR !gt_eqF// ltr_expR ltr_pmul2l// ltr_ln.
Qed.

Lemma prod1_01 :
  forall [s : seq R], (forall e, e \in s -> 0 <= e <= 1) ->
    (\prod_(j <- s) j = 1 <-> (forall e, e \in s -> e = (1:R))).
Proof.
elim.
- by rewrite big_nil.
- move=> e s IH h.
  rewrite big_cons.
  split.
  + move/eqP.
    rewrite prod1; last 2 first.
      by apply: h; rewrite in_cons eq_refl.
      by apply: prod01 => e0 e0s; apply: h; rewrite in_cons e0s orbT.
    move/andP => [/eqP e1] /eqP.
    rewrite IH; last first.
      by move=> e0 e0s; apply: h; rewrite in_cons e0s orbT.
    move=> h' e0.
    rewrite in_cons => /orP [/eqP -> //|].
    apply: h'.
  + move=> es1. 
    apply /eqP. 
    rewrite prod1; last 2 first.
    - by apply: h; rewrite in_cons eq_refl.
    - by apply: prod01 => e0 e0s; apply: h; rewrite in_cons e0s orbT.
    apply/andP; split. 
    - by apply/eqP; apply: es1; rewrite in_cons eq_refl.
    - apply/eqP; rewrite IH => e0 e0s.
        by apply es1; rewrite in_cons e0s orbT.
      by apply: h; rewrite in_cons e0s orbT.
Qed.

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

Lemma help (x r : R) : 0 <= x -> 0 < r -> (1 - x `^ r^-1 < 0) -> (1 < x).
Proof.
have {1}->: 1 = 1 `^ r^-1 by rewrite powR1.
rewrite subr_lt0 => x0 r0.
move/(@gt0_ltr_powR _ r0 _).
rewrite !in_itv/= !andbT !powR_ge0 -!powRrM 
!mulVf ?neq_lt ?r0 ?orbT// powR1 powRr1//.
by apply.
Qed.

Lemma help' (x r : R) : 0 <= x -> 0 < r -> ~~ (1 - x `^ r^-1 < 0) -> x <= 1.
Proof.
have {1}->: 1 = 1 `^ r^-1 by rewrite powR1.
rewrite subr_lt0 -leNgt => x0 r0.
move/(@gt0_ler_powR _ r (ltW r0)). 
rewrite nnegrE. 
rewrite !powR_ge0 -!powRrM !mulVf ?neq_lt ?r0 ?orbT// powR1 powRr1//.
apply. 
  exact.
  by rewrite nnegrE.
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
  apply (@prod1_01 (map (@translation product p (Bool_T)) Es)) => // [e||].
  - by move=> /mapP[x _ ->].
  - by apply/eqP; rewrite big_map.
  - by apply/mapP; eexists; last reflexivity; exact: mem_nth.
Qed.

Lemma nary_inversion_andE0 (Es : seq (expr Bool_T) ) :
  l <> Lukasiewicz -> l <> Yager ->
    [[ and_E Es ]]_ l = 0 -> (exists i, [[ nth (Bool false) Es i ]]_ l = 0).
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
    case: ifPn => _; first by exists 0%nat => /=; apply/eqP.
    move/IH => [i i0].
    by exists i.+1.
- move=> l1 l2 /eqP.
  rewrite /prodR big_map prodf_seq_eq0 => /hasP[e eEs/= /eqP e0].
  move/(nthP (Bool false)) : eEs => [i iEs ie].
  by exists i; rewrite ie.
Qed.

Lemma natalia_prod_inv (x y : R) :
  (0 <= x <= 1) -> (0 <= y <= 1) ->
    reflect (x = 1 \/ y = 1) (natalia_prod x y == 1).
Proof.
move=> x01 y01; apply: (iffP eqP); rewrite /natalia_prod; nra.
Qed.

Lemma nary_inversion_orE1 Es :
  l <> Lukasiewicz -> l <> Yager ->
    [[ or_E Es ]]_ l = 1 -> (exists i, [[ nth (Bool false) Es i ]]_ l = 1).
Proof.
have H := translate_Bool_T_01 l. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move => l1 l2; move/eqP.
  rewrite /maxR big_map.
  elim: Es.
  + by rewrite big_nil eq_sym oner_eq0.
  + move=> a l0 IH.
    rewrite big_cons {1}/maxr.
    case: ifPn => _; last by exists 0%nat => /=; apply/eqP.
    move/IH => [i i1].
    by exists i.+1.
- move => l1 l2 /eqP.
  rewrite /natalia_prodR big_map.
  elim: Es.
  + by rewrite big_nil eq_sym oner_eq0.
  + move=> a l0 IH.
    rewrite big_cons {1}/natalia_prod.
    move/natalia_prod_inv => [|||/eqP].
    * exact: H.
    * exact: natalia_prod_seq_01.
    * by exists 0%nat.
    * by move/IH => [x ?]; exists x.+1.
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

Lemma nary_inversion_orE0 Es :
    [[ or_E Es ]]_ l  = 0 -> (forall i, (i < size Es)%nat -> [[ nth (Bool false) Es i ]]_ l = 0).
Proof.
have H := translate_Bool_T_01 l. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move/eqP. rewrite minr10 /sumR.
  rewrite big_map.
  rewrite (@bigsum_0x _ _ Es) => h i.
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
    move: h.
    rewrite !big_map big_cons {1}/maxr.
    case: ifPn => // /[swap] ->.
    rewrite -leNgt.
    admit.
- rewrite /natalia_prodR. admit.
Admitted.


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
    [[ e ]]_ l = [[ Bool b ]]_ l -> << e >>_ l = b.
Proof.
dependent induction e using expr_ind' => ll ly.
- move: b b0 => [] [] //=; lra.
- move: H.
  rewrite List.Forall_forall. move => H.
  rewrite [ [[Bool b]]_l ]/=.  
  move: b => [].
  + move/ nary_inversion_andE1. 
    rewrite [bool_translation (and_E l0)]/=.
    (* rewrite bool_translation.
    rewrite foldrE. Search "big" (_ = true). *)
    admit.
  + admit.
- admit.
- admit.
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

Admitted.

(* End translation_lemmas. *)

Section shadow.


Definition row_of_seq (s : seq R) : 'rV[R]_(size s) :=
  (\row_(i < size s) tnth (in_tuple s) i).

Check row_of_seq.
About MatrixFormula.seq_of_rV.


Definition product_and n (xs: 'rV[R]_n) : R := 
  \prod_(x <- (MatrixFormula.seq_of_rV xs)) x.

Print MatrixFormula.seq_of_rV.
Print fgraph.


Definition shadow_lifting (f : forall n, 'rV_n -> R) := 
  forall Es : seq R, forall i : 'I_(size Es),
    (* (forall i, nth 0 Es i != 0) -> *)
    (forall i, 0 < nth 0 Es i <= 1) ->
    partial (f (size Es)) i (row_of_seq Es) > 0.

Lemma all_0_product_partial (Es : seq R) (i : 'I_(size Es)) :
  partial 0 i (row_of_seq Es) = 0.
(*I'm not sure if I don't need an additional assumption here*)
Proof.
apply/cvg_lim; first exact: Rhausdorff.
rewrite [X in X @ _ --> _](_ : _ = 0); first exact: (@cvg_cst R).
by apply/funext => r/=; rewrite /GRing.zero/=(*NB: I shouldn't do that*) subrr mulr0.
Qed.

Print BSide.
Print itv_bound.


Lemma monotonous_bounded_is_cvg (f : R -> R) x a b:
  monotonous ([set` Interval (BSide b x) a]) f ->
  (* has_ubound (f @` setT) ->  *)
  has_lbound (f @` setT (*isn't this too restrictive?*) ) ->
  cvg (f x @[x --> (x)^'+]).
Proof.
rewrite /monotonous/has_lbound.
Search "lbound" "cvg".
Admitted. 

Notation "'nondecreasing_fun' f" := ({homo f : n m / (n <= m)%O >-> (n <= m)%O})
  (at level 10).
Notation "'nonincreasing_fun' f" := ({homo f : n m / (n <= m)%O >-> (n >= m)%O})
  (at level 10).
Notation "'increasing_fun' f" := ({mono f : n m / (n <= m)%O >-> (n <= m)%O})
  (at level 10).
Notation "'decreasing_fun' f" := ({mono f : n m / (n <= m)%O >-> (n >= m)%O})
  (at level 10).


Lemma shadow_lifting_product_and : shadow_lifting product_and.
Proof.
move=> Es i Es01.
rewrite lt_neqAle; apply/andP; split; last first.
+ apply: limr_ge.
  - apply: (monotonous_bounded_is_cvg _ _ ).
    * rewrite /monotonous. admit.
    * rewrite /has_lbound.  Search "lbound".
      (* rewrite -int_lbound_has_minimum.  *)
      admit.
  - near=> x.
    rewrite mulr_ge0//.
    + by rewrite invr_ge0.
    + rewrite subr_ge0 /product_and !big_map/= ler_prod// => j _.
      rewrite !ffunE !mxE; apply/andP; split.
      - rewrite /tnth (set_nth_default (0:R))//.
        by have /andP[/ltW] := Es01 j.
      - by rewrite ler_addl// mulr_ge0.
+ rewrite /partial.
(*   rewrite /(-all_0_product_partial _).  *)
  admit. 
Admitted.


End shadow.

Section Lukasiewicz_lemmas.


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
have := translate_Bool_T_01 Lukasiewicz e1.
have := translate_Bool_T_01 Lukasiewicz e2.
have := translate_Bool_T_01 Lukasiewicz e3.
rewrite /=/sumR/minR?big_cons ?big_nil.
rewrite /minr.
by repeat case: ifP; lra.
Qed. 

Theorem Lukasiewicz_andA e1 e2 e3 : (0 < p) ->
  [[ (e1 /\ e2) /\ e3]]_Lukasiewicz = [[ e1 /\ (e2 /\ e3) ]]_Lukasiewicz.
Proof.
have := translate_Bool_T_01 Lukasiewicz e1.
have := translate_Bool_T_01 Lukasiewicz e2.
have := translate_Bool_T_01 Lukasiewicz e3. 
rewrite /=/sumR/maxR/minR/natalia_prodR ?big_cons ?big_nil.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
rewrite /maxr.
by repeat case: ifP; lra.
Qed.

End Lukasiewicz_lemmas.

Section Yager_lemmas.

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
have := translate_Bool_T_01 Yager e1.
have := translate_Bool_T_01 Yager e2.
have := translate_Bool_T_01 Yager e3.
rewrite /=/sumR/maxR/minR/natalia_prodR ?big_cons ?big_nil.
rewrite ![in _ `^ p + _]addr0.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
move => ht3 ht2 ht1.
rewrite {2}/minr. 
case: ifPn => h1.
+ rewrite -powRrM mulVf ?p0 ?powRr1 ?addr_ge0 ?powR_ge0//.
  rewrite {1}/minr.
  case: ifPn => h2.
  * rewrite {2}/minr.
    case: ifPn => h3.
    - rewrite {1}/minr.
      case: ifPn => h4. 
      + by rewrite -{1}powRrM mulVf ?powRr1 ?addr_ge0 ?powR_ge0 ?addrA ?addr0.
      + rewrite addrA; move: h2; rewrite addrA; move: h4;
        rewrite -{1}powRrM mulVf ?powRr1 ?addr_ge0 ?powR_ge0//. 
        rewrite !addr0 -leNgt.
        set a := (t1 `^ p + t2 `^ p + t3 `^ p) `^ p^-1.
        lra.
    - rewrite {1}/minr.
      suff: (t1 `^ p + (t2 `^ p + t3 `^ p)) `^ p^-1 >=
            (t1 `^ p + t2 `^ p) `^ p^-1.
      
      admit.
      (* + case: ifP.
        * rewrite addr0. 
          set a1 := (t1 `^ p + (t2 `^ p + t3 `^ p)) `^ p^-1.
          set a2 := (1 `^ p + t3 `^ p) `^ p^-1 . *)
          (* lra. *)
      (* + rewrite addr0. rewrite powr1. lra.
      +
           admit. (* by lra. *) *)
      rewrite gt0_ler_powR//.
      + by rewrite invr_ge0 ltW.
      + by rewrite nnegrE addr_ge0// powR_ge0. 
      + by rewrite nnegrE !addr_ge0// powR_ge0.
      + by rewrite lerD// lerDl powR_ge0.
  * rewrite {2}/minr.
    case: ifPn => h3.
    - rewrite -{1}powRrM mulVf// powRr1 ?addr_ge0 ?powR_ge0//.
      rewrite {1}/minr.
      case: ifPn => //.
      move: h2 => /[swap]. by rewrite !addr0 !addrA => ->.
    - rewrite {1}/minr.
      case: ifPn => //.
      have: (1 `^ p + t3 `^ p) `^ p^-1 >= 1.
        have {1}->: 1 = 1 `^ p^-1 by rewrite powR1.
        rewrite gt0_ler_powR//.
        + by rewrite invr_ge0 ltW.
        + by rewrite nnegrE .
        + by rewrite nnegrE addr_ge0// powR_ge0. 
        by rewrite powR1 lerDl powR_ge0.
      rewrite addr0.
      set a := (1 `^ p + t3 `^ p) `^ p^-1.
      move => /le_lt_trans /[apply]. 
      by rewrite ltxx.
  + rewrite {1}/minr.
    case: ifPn => // h2.
    - have: (t1 `^ p + 1 `^ p) `^ p^-1 >= 1.
        have {1}->: 1 = 1`^p^-1 by rewrite powR1.
        rewrite gt0_ler_powR//.
        + by rewrite invr_ge0 ltW.
        + by rewrite nnegrE .
        + by rewrite nnegrE addr_ge0// powR_ge0.
        by rewrite powR1 lerDr powR_ge0.
      move: h2.
      set a := (t1 `^ p + 1 `^ p) `^ p^-1. lra.
    * rewrite {2}/minr.
      case: ifPn => h3.
      - rewrite {1}/minr.
        case: ifPn => //.
        rewrite -powRrM mulVf// powRr1.
        move=> h4.
        have h5: (t1 `^ p + t2 `^ p + t3 `^ p) `^ p^-1 >= (t2 `^ p + t3 `^ p) `^ p^-1.
        rewrite gt0_ler_powR//.
        + by rewrite invr_ge0 ltW.
        + by rewrite nnegrE addr_ge0// powR_ge0. 
        + by rewrite nnegrE !addr_ge0// powR_ge0.
        by rewrite lerD// lerDr powR_ge0.
        move: h4. rewrite !addr0. 
        (* rewrite lt_neqAle.  *)
        set a := (t1 `^ p + t2 `^ p + t3 `^ p) `^ p^-1.
         
        admit. (* lra. *)
        by rewrite addr_ge0 ?powR_ge0 ?addr0 ?powR_ge0. (* by rewrite addr_ge0 ?powR_ge0. *)
      - rewrite {1}/minr.
        case: ifPn => //.
        have: (1 `^ p + t3 `^ p) `^ p^-1 >= 1.
        - have {1}->: 1 = 1`^p^-1 by rewrite powR1.
          rewrite gt0_ler_powR//.
          + by rewrite invr_ge0 ltW.
          + by rewrite nnegrE .
          + by rewrite nnegrE addr_ge0// powR_ge0.
          by rewrite powR1 lerDl powR_ge0. 
          + rewrite powR1 addr0. 
          move => h4 h5. admit.
Admitted.


Theorem Yager_andA e1 e2 e3 : (0 < p) ->
  [[ (e1 /\ e2) /\ e3]]_Yager = [[ e1 /\ (e2 /\ e3) ]]_Yager.
Proof.
move=> p0.
have pneq0 : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 Yager e1.
have := translate_Bool_T_01 Yager e2.
have := translate_Bool_T_01 Yager e3.
rewrite /=/sumR/maxR/minR/natalia_prodR ?big_cons ?big_nil.
set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  set a1 := (1 - t1)`^p.
  set a2 := (1 - t2)`^p.
  set a3 := (1 - t3)`^p.
  have se_ge0 r := @addr_ge0 R _ _ (@powR_ge0 _ _ r) (@powR_ge0 _ _ r).
  rewrite {2}/maxr=> ht3 ht2 ht1.
  case: ifPn; rewrite addr0.
  + move/(help (se_ge0 _ _ _) p0).
    rewrite subr0 {1}/maxr -/a1 -/a2 => h1.
    case: ifPn; rewrite addr0.
    * move/(help (se_ge0 _ _ _) p0).
      rewrite {2}/maxr -/a3 powR1 ltrDl => h2.
      case: ifPn.
      - move/(help (se_ge0 _ _ _) p0).
        rewrite /maxr -/a2 -/a3 => h3.
        case: ifPn => //.
        rewrite subr0 powR1 addr0.
        move/(help' (addr_ge0 (powR_ge0 _ _) (ltW ltr01)) p0).
        rewrite -/a1 gerDr => h4.
        have h5: 0 <= a1 by apply powR_ge0.
        have ->: a1 = 0 by lra.
        by rewrite add0r powR1 subrr.
      - move/(help' (se_ge0 _ _ _) p0).
        rewrite -/a2 -/a3 => h3.
        rewrite {1}/maxr.
        case: ifPn => //; rewrite addr0.
        move/(help' (se_ge0 _ _ _) p0).
        rewrite -/a1.
        rewrite opprD opprK addrA subrr add0r -powRrM mulVf// powRr1.
          nra.
        by rewrite addr_ge0 /a2 /a3// powR_ge0.
    * move/(help' (se_ge0 _ _ _) p0).
      rewrite powR1 addr0 gerDl -/a3 => h2.
      have ->: a3 = 0 by have := powR_ge0 _ _ : 0 <= a3; lra.
      rewrite !addr0 powR1 subrr.
      rewrite {2}/maxr.
      case: ifPn.
      - move/(help (powR_ge0 _ _) p0).
        rewrite -/a2 {1}/maxr => h3.
        case: ifPn => //.
        move/(help' (se_ge0 _ _ _) p0).
        rewrite -/a1 subr0 powR1 gerDr => h4.
        have ->: a1 = 0 by have := powR_ge0 _ _ : 0 <= a1; lra.
        by rewrite add0r powR1 subrr.
      - move/(help' (powR_ge0 _ _) p0).
        rewrite -/a2 => h3.
        rewrite {1}/maxr.
        case: ifPn => //.
        move/(help' (se_ge0 _ _ _) p0).
        rewrite -/a1.
        rewrite opprD opprK addrA subrr add0r -powRrM mulVf// powRr1.
          lra.
        by rewrite /a2 powR_ge0.
  + move/(help' (se_ge0 _ _ _) p0).
    rewrite -/a1 -/a2 => h1.
    rewrite {1}/maxr.
    case: ifPn; rewrite addr0.
    * move/(help (se_ge0 _ _ _) p0).
      rewrite -/a3 opprD opprK addrA.
      rewrite {2}/maxr.
      case: ifPn.
      - move/(help (se_ge0 _ _ _) p0).
        rewrite -/a2 -/a3 => h3.
        rewrite subr0 powR1.
        rewrite {1}/maxr.
        case: ifPn => //.
        rewrite addr0.
        move/(help' (addr_ge0 (powR_ge0 _ _) (ltW ltr01)) p0).
        rewrite -/a1 gerDr => h4.
        have ->: a1 = 0 by have := powR_ge0 _ _ : 0 <= a1; lra.
        by rewrite add0r add0r powR1 subrr.
      - move/(help' (se_ge0 _ _ _) p0).
        rewrite -/a2 -/a3 => h3.
        rewrite {1}/maxr.
        case: ifPn => //.
        rewrite addr0.
        move/(help' (se_ge0 _ _ _) p0).
        rewrite opprD opprK. rewrite -> addrA.
        rewrite subrr add0r -/a1 -powRrM mulVf// ?powRr1.
        + rewrite !addrA subrr add0r.
          rewrite -powRrM mulVf// powRr1.
          * move => ? ?.
          exfalso.
          lra.
          * by rewrite addr_ge0 ?powR_ge0.
        + by rewrite addr_ge0 ?powR_ge0.
    * move/(help' (se_ge0 _ _ _) p0).
      rewrite -/a3 opprD opprK addrA addr0.
      rewrite {2}/maxr.
      case: ifPn.
      - move/(help (se_ge0 _ _ _) p0).
        rewrite -/a1 -/a2 -/a3 subr0 powR1 => h3.
        rewrite {1}/maxr.
        case: ifPn.
        + move/(help (addr_ge0 (powR_ge0 _ _) (ltW ltr01)) p0).
          rewrite -/a1 ltrDr => h4.
          rewrite addrA subrr. 
          rewrite ( addrC 0 ((a1 + a2) `^ p^-1)) addr0.
          move => h5. 
          apply /eqP. 
          rewrite subr_eq addrC addr0.
          (* rewrite -(subr0_eq (1 - (((1 + (-1 + (a1 + a2) `^ p^-1)) `^ p + a3) `^ p^-1) = 0)).  *)
          admit. (* lra. *)
        + move/(help' (addr_ge0 (powR_ge0 _ _) (ltW ltr01)) p0).
          rewrite -/a1 gerDr => h4.
          have : a1 = 0 by have := powR_ge0 _ _ : 0 <= a1; lra.
          move => h5.
          rewrite addrA subrr.
          rewrite ( addrC 0 ((a1 + a2) `^ p^-1)) addr0.
          move => h6. rewrite h5.
          rewrite (addrC 0 a2) addr0 (addrC 0 1) addr0.
          rewrite powR1 subrr. apply /eqP. 
          rewrite subr_eq addrC addr0.
          move: h6. rewrite h5 (addrC 0 a2) addr0.
          move => h6.
        
          (* lra. *)
          admit. (* lra. *)
      - move/(help' (se_ge0 _ _ _) p0).
        rewrite -/a2 -/a3 => h3.
        rewrite {1}/maxr.
        case: ifPn.
        + move/(help (se_ge0 _ _ _) p0).
          rewrite -/a1 opprD.
          rewrite opprK.
          rewrite [in X in X -> _ -> _]addrA.
          rewrite subrr add0r -powRrM mulVf// ?powRr1 ?(addr_ge0 (powR_ge0 _ _) (powR_ge0 _ _))// => h4.
          rewrite addrA subrr.
        
          admit. (* lra. *)
        move => _.
       admit.
Admitted.

End Yager_lemmas.

Section Godel_lemmas.

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
  admit. (* by repeat case: ifP; lra.  *)(*currently times out, but no error*)
(*product*)
Admitted.

Theorem Godel_andA e1 e2 e3 : (0 < p) ->
  [[ (e1 /\ e2) /\ e3]]_Godel = [[ e1 /\ (e2 /\ e3) ]]_Godel.
Proof.
rewrite /=/sumR/minR !big_cons !big_nil.
have := translate_Bool_T_01 Godel e1.
have := translate_Bool_T_01 Godel e2.
have := translate_Bool_T_01 Godel e3.
set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
move => h1 h2 h3 p0.
rewrite /minr. 

(* by repeat case: ifP; lra. *) (*gets stuck*)
  admit.
Admitted.

End Godel_lemmas.

Section product_lemmas.

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
  

End translation_lemmas.

