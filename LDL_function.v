Require Import Coq.Program.Equality.

From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import order seq.
From mathcomp Require Import sequences reals ereal exp hoelder.
From mathcomp Require Import functions classical_sets functions measure lebesgue_measure lebesgue_integral boolp .

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.

Reserved Notation "[[ e ]]" (format "[[  e  ]]").

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

  (*quantifiers - left for later consideration*)
  (*| forall_E: forall t, expr t -> expr Bool_T
    | exists_E: forall t, expr t -> expr Bool_T*)

  (* networks and applications *)
  | net : forall n m : nat, (n.-tuple R -> m.-tuple R) -> expr (Network_T n m)
  | app_net : forall n m : nat, expr (Network_T n m) -> expr (Vector_T n) -> expr (Vector_T m)
  | lookup_E n: expr (Vector_T n) -> expr (Index_T n) -> expr Real_T

  (*comparisons*)
  | comparisons_E : comparisons -> expr Real_T -> expr Real_T -> expr Bool_T
.
  (*other - needed for DL translations*)
  (*| identity_E : expr Real_T -> expr Real_T -> expr Real_T.*)
End expr.

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

Definition sumR (Es : seq R) : R := foldr ( +%R ) 0 Es. 

Fixpoint translation t (e: expr t) {struct e} : type_translation t :=
    match e in expr t return type_translation t with
    | Bool true => (1%R : type_translation Bool_T)
    | Bool false => (0%R : type_translation Bool_T)
    | Real r => r%R
    | Index n i => i
    | Vector n t => t

    | and_E Es =>
        match l with
        | Lukasiewicz => maxr (sumR (map (@translation _) Es)- (length Es)%:R) 0
        | Yager => maxr (1 - ((sumR (map (fun E => (1 - ([[ E ]]: type_translation Bool_T))`^p)%R Es))`^p^-1)) 0
        | Godel => foldr minr 1 (map (@translation _) Es)
        | product => foldr ( *%R ) 1 (map (@translation _) Es)
        end
    | or_E Es =>
        match l with
        | Lukasiewicz => minr (sumR (map (@translation _) Es)) 1
        | Yager => minr ((sumR (map (fun E => ([[ E ]] : type_translation Bool_T)`^p) Es))`^p^-1) 1
        | Godel => foldr maxr 0 (map (@translation _) Es)
        | product => foldr (fun a1 a2 => a1 + a2 - a1 * a2) 0 (map (@translation _) Es)
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

Definition sumE (Es : seq \bar R) : \bar R := foldr ( +%E ) 0%E Es. 

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

About sumE.

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

Definition bool_translation_binop op x y :=
  match op with
  | and_E => x && y
  | or_E => x || y
  | impl_E => x ==> y
  end.

Reserved Notation "<< e >>".
Fixpoint bool_translation t (e: expr t) : bool_type_translation t :=
  match e in expr t return bool_type_translation t with
  | Bool x => x
  | Real r => r%R
  | Index n i => i
  | Vector n t => t

  | binary_logical_E op E1 E2 => bool_translation_binop op << E1 >> << E2 >>
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

Section translation_lemmas.
Local Open Scope ring_scope.
Local Open Scope order_scope.

Variable (l : DL).
Variable (p : R).
Variable (p1 : 1 <= p).

Local Notation "[[ e ]]_ l" := (translation l p e) (at level 10).
Local Notation "<< e >>_ l" := (bool_translation e) (at level 10).

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

Lemma translate_Bool_T_01 (e : expr Bool_T) :
  0 <= [[ e ]]_l <= 1.
Proof.
dependent induction e => //=.
- by case: ifPn => //; lra.
- have := IHe1 e1 erefl JMeq_refl.
  have := IHe2 e2 erefl JMeq_refl.
  set t1 := _ e1.
  set t2 := _ e2.
  case: l; case: b; rewrite /=/minr/maxr; try case: ifP; rewrite ?cprD ?oppr_le0 ?powR_ge0; nra.
- have := IHe e erefl JMeq_refl.
  set t := _ e.
  by lra.
- set t1 := _ e1.
  set t2 := _ e2.
  case: c; rewrite /maxr; case: ifP => [/eqP ->|?].
  + have [] := leP (-t2) t2; lra.
  + case: ifP; first lra.
    case: ifP; first lra.
    lra.
  + have [] := eqVneq (-t2) t2; lra.
  + case: ifP; first lra.
    have := normr_ge0 ((t1 - t2) / (t1 + t2)).
    lra.
Qed.

Lemma gt0_ltr_powR (r : R) : 0 < r ->
  {in `[0, +oo[ &, {homo (@powR R) ^~ r : x y / x < y >-> x < y}}.
Proof.
move=> r0 x y; rewrite !in_itv/= !andbT !le_eqVlt => /predU1P[<-|x0].
  move=> /predU1P[<-|y0 _]; first by rewrite ltxx//.
  by rewrite powR0 ?(gt_eqF r0)// powR_gt0.
move=> /predU1P[<-|y0]; first rewrite ltNge ltW//.
by rewrite /powR !gt_eqF// ltr_expR ltr_pmul2l// ltr_ln.
Qed.

Lemma help (x r : R) : 0 <= x -> 0 < r -> (1 - x `^ r^-1 < 0) -> (1 < x).
Proof.
have {1}->: 1 = 1 `^ r^-1 by rewrite powR1.
rewrite subr_lt0 => x0 r0.
move/(@gt0_ltr_powR _ r0 _).
rewrite !in_itv/= !andbT !powR_ge0 -!powRrM !mulVf ?neq_lt ?r0 ?orbT// powR1 powRr1//.
by apply.
Qed.

Lemma help' (x r : R) : 0 <= x -> 0 < r -> ~~ (1 - x `^ r^-1 < 0) -> x <= 1.
Proof.
have {1}->: 1 = 1 `^ r^-1 by rewrite powR1.
rewrite subr_lt0 -leNgt => x0 r0.
move/(@gt0_ler_powR _ r (ltW r0)).
rewrite !in_itv/= !andbT !powR_ge0 -!powRrM !mulVf ?neq_lt ?r0 ?orbT// powR1 powRr1//.
by apply.
Qed.

Lemma inversion_andE1 e1 e2 :
  0 <= e1 <= 1 -> 0 <= e2 <= 1 ->
    translation_binop l p and_E e1 e2 = 1 -> e1 = 1 /\ e2 = 1.
Proof.
have p0 := lt_le_trans ltr01 p1.
move=> he1 he2.
case: l => /=.
- rewrite /maxr; case: ifPn; lra.
- rewrite /maxr; case: ifPn. lra.
  move=> _.
  have [->|e11 /eqP] := eqVneq e1 1.
  have [->//|e21 /eqP] := eqVneq e2 1.
  + rewrite subrr powR0 ?(gt_eqF p0)// add0r.
    rewrite eq_sym addrC -subr_eq subrr eq_sym oppr_eq0. (* FIXME *)
    rewrite -powRrM divff ?(gt_eqF p0)// powRr1.
    lra. lra.
  + rewrite eq_sym addrC -subr_eq subrr eq_sym oppr_eq0. (* FIXME *)
    rewrite powR_eq0 (paddr_eq0 (powR_ge0 _ _) (powR_ge0 _ _)) => /andP [].
    rewrite powR_eq0.
    lra.
- rewrite /minr; case: ifPn; lra.
- by nra.
Qed.

Lemma inversion_andE0 e1 e2 :
  0 <= e1 <= 1 -> 0 <= e2 <= 1 -> l <> Lukasiewicz -> l <> Yager ->
    translation_binop l p and_E e1 e2 = 0 -> e1 = 0 \/ e2 = 0.
Proof.
have p0 := lt_le_trans ltr01 p1.
move=> he1 he2.
case: l => //=.
- rewrite /minr; case: ifPn; lra.
- nra.
Qed.

Lemma inversion_orE1 e1 e2 :
  0 <= e1 <= 1 -> 0 <= e2 <= 1 -> l <> Lukasiewicz -> l <> Yager ->
    translation_binop l p or_E e1 e2 = 1 -> e1 = 1 \/ e2 = 1.
Proof.
have p0 := lt_le_trans ltr01 p1.
move=> he1 he2.
case: l => //=.
- rewrite /maxr; case: ifPn; lra.
- nra.
Qed.

Lemma inversion_orE0 e1 e2 :
  0 <= e1 <= 1 -> 0 <= e2 <= 1 ->
    translation_binop l p or_E e1 e2 = 0 -> e1 = 0 /\ e2 = 0.
Proof.
have p0 := lt_le_trans ltr01 p1.
move=> he1 he2.
case: l => /=.
- rewrite /minr; case: ifPn; lra.
- rewrite /minr; case: ifPn => _; last lra.
  have [->|e11 /eqP] := eqVneq e1 0.
  have [->//|e21 /eqP] := eqVneq e2 0.
  + rewrite powR0 ?(gt_eqF p0)// add0r.
    rewrite -powRrM divff ?(gt_eqF p0)// powRr1.
    lra. lra.
  + rewrite powR_eq0 (paddr_eq0 (powR_ge0 _ _) (powR_ge0 _ _)) => /andP [].
    rewrite powR_eq0.
    lra.
- rewrite /maxr; case: ifPn; lra.
- by nra.
Qed.

Lemma inversion_implE1 e1 e2 :
  0 <= e1 <= 1 -> 0 <= e2 <= 1 -> l <> Lukasiewicz -> l <> Yager ->
    translation_binop l p impl_E e1 e2 = 1 -> e1 = 0 \/ e2 = 1.
Proof.
have p0 := lt_le_trans ltr01 p1.
move=> he1 he2.
case: l => //=.
- rewrite /maxr; case: ifPn; lra.
- nra.
Qed.

Lemma inversion_implE0 e1 e2 :
  0 <= e1 <= 1 -> 0 <= e2 <= 1 ->
    translation_binop l p impl_E e1 e2 = 0 -> e1 = 1 /\ e2 = 0.
Proof.
have p0 := lt_le_trans ltr01 p1.
move=> he1 he2.
case: l => /=.
- rewrite /minr; case: ifPn; lra.
- rewrite /minr; case: ifPn => _; last lra.
  have [-> /eqP|e11 /eqP] := eqVneq e1 0.
  + by rewrite subr0 powR1 powR_eq0 paddr_eq0// ?powR_ge0; lra.
  have [->//|e21] := eqVneq e2 0.
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
    [[ e ]]_l = [[ Bool b ]]_l -> << e >>_l = b.
Proof.
dependent induction e => ll ly //=.
- move: b b0 => [] [] //; lra.
- have {} IHe1 := IHe1 e1 erefl JMeq_refl.
  have {} IHe2 := IHe2 e2 erefl JMeq_refl.
  move: b b0 => [] [] //=.
  + move/(inversion_andE1 (translate_Bool_T_01 _) (translate_Bool_T_01 _)).
    case.
    move/(IHe1 true ll ly) => ->.
    by move/(IHe2 true) => ->.
  + move/(inversion_andE0 (translate_Bool_T_01 _) (translate_Bool_T_01 _) ll ly).
    case.
    by move/(IHe1 false ll ly) => ->.
    by move/(IHe2 false ll ly) => ->; rewrite andbF.
  + move/(inversion_orE1 (translate_Bool_T_01 _) (translate_Bool_T_01 _) ll ly).
    case.
    by move/(IHe1 true ll ly) => ->.
    by move/(IHe2 true ll ly) => ->; rewrite orbT.
  + move/(inversion_orE0 (translate_Bool_T_01 _) (translate_Bool_T_01 _)).
    case.
    move/(IHe1 false ll ly) => ->.
    by move/(IHe2 false) => ->.
  + move/(inversion_implE1 (translate_Bool_T_01 _) (translate_Bool_T_01 _) ll ly).
    case.
    by move/(IHe1 false ll ly) => ->.
    by move/(IHe2 true ll ly) => ->; rewrite implybT.
  + move/(inversion_implE0 (translate_Bool_T_01 _) (translate_Bool_T_01 _)).
    case.
    move/(IHe1 true ll ly) => ->.
    by move/(IHe2 false) => ->.
- have {} IHe := IHe e erefl JMeq_refl.
  case: b => ?.
  have: [[ e ]]_l = 0 by lra.
  by move/(IHe false) => ->.
  have: [[ e ]]_l = 1 by lra.
  by move/(IHe true) => ->.
- case: c; rewrite -!translations_Real_coincide;
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
      Search (`| _ | == _).
      rewrite eqr_norml.
      nra.
Qed.

Lemma andC e1 e2 :
  [[ e1 /\ e2 ]]_l = [[ e2 /\ e1 ]]_l.
Proof.
case: l.
- by rewrite /= (addrC (_ e1)).
- by rewrite /= (addrC (_ `^ _)).
- by rewrite /=/minr; repeat case: ifP; lra.
- by rewrite /= mulrC.
Qed.

Lemma orC e1 e2 :
  [[ e1 \/ e2 ]]_l = [[ e2 \/ e1 ]]_l.
Proof.
case: l.
- by rewrite /= (addrC (_ e1)).
- by rewrite /= (addrC (_ `^ _)).
- by rewrite /=/maxr; repeat case: ifP; lra.
- by rewrite /= mulrC -(addrC (_ e2)).
Qed.

Lemma orA e1 e2 e3 :
  [[ (e1 \/ (e2 \/ e3)) ]]_l = [[ ((e1 \/ e2) \/ e3) ]]_l.
Proof.
have p0 : 0 < p by rewrite (lt_le_trans ltr01).
have ? : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 e1.
have := translate_Bool_T_01 e2.
have := translate_Bool_T_01 e3.
(*Łukasiewicz*)
case: l => /=.
- set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  rewrite /minr.
  by repeat case: ifP; lra.
(*Yager*)
- set t1 := _ e1.
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
          by rewrite -{1}powRrM mulVf ?powRr1 ?addr_ge0 ?powR_ge0 ?addrA.
        rewrite addrA; move: h2; rewrite addrA; move: h4;
        rewrite -{1}powRrM mulVf ?powRr1 ?addr_ge0 ?powR_ge0//;
        lra.
      - rewrite {1}/minr.
        suff: (t1 `^ p + (t2 `^ p + t3 `^ p)) `^ p^-1 >=
              (t1 `^ p + t2 `^ p) `^ p^-1 by lra.
        rewrite gt0_ler_powR//.
        + by rewrite invr_ge0 ltW.
        + by rewrite in_itv /= andbT addr_ge0// powR_ge0.
        + by rewrite in_itv /= andbT !addr_ge0// powR_ge0.
        + by rewrite lerD// lerDl powR_ge0.
    * rewrite {2}/minr.
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
  + rewrite {1}/minr.
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
(*Godel*)
- set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  rewrite /maxr.
  by repeat case: ifP; lra.
(*product*)
- set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  lra.
Qed.

Theorem andA e1 e2 e3 : (0 < p) ->
  [[ (e1 /\ e2) /\ e3]]_l = [[ e1 /\ (e2 /\ e3) ]]_l.
Proof.
move=> p0.
have pneq0 : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 e1.
have := translate_Bool_T_01 e2.
have := translate_Bool_T_01 e3.
case: l => /=.
+ set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  rewrite /maxr.
  by repeat case: ifP; lra.
(*Yager*)
+ set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  set a1 := (1 - t1)`^p.
  set a2 := (1 - t2)`^p.
  set a3 := (1 - t3)`^p.
  have se_ge0 r := @addr_ge0 R _ _ (@powR_ge0 _ _ r) (@powR_ge0 _ _ r).
  rewrite {2}/maxr=> ht3 ht2 ht1.
  case: ifPn.
  {
    move/(help (se_ge0 _ _ _) p0).
    rewrite subr0 {1}/maxr -/a1 -/a2 => h1.
    case: ifPn.
    {
      move/(help (se_ge0 _ _ _) p0).
      rewrite {2}/maxr -/a3 powR1 ltrDl => h2.
      case: ifPn.
      {
        move/(help (se_ge0 _ _ _) p0).
        rewrite /maxr -/a2 -/a3 => h3.
        case: ifPn => //.
        rewrite subr0 powR1.
        move/(help' (addr_ge0 (powR_ge0 _ _) (ltW ltr01)) p0).
        rewrite -/a1 gerDr => h4.
        have h5: 0 <= a1 by apply powR_ge0.
        have ->: a1 = 0 by lra.
        by rewrite add0r powR1 subrr.
      }
      move/(help' (se_ge0 _ _ _) p0).
      rewrite -/a2 -/a3 => h3.
      {
        rewrite {1}/maxr.
        case: ifPn => //.
        move/(help' (se_ge0 _ _ _) p0).
        rewrite -/a1.
        rewrite opprD opprK addrA subrr add0r -powRrM mulVf// powRr1.
        nra.
        by rewrite addr_ge0 /a2 /a3// powR_ge0.
      }
    }
    move/(help' (se_ge0 _ _ _) p0).
    rewrite powR1 gerDl -/a3 => h2.
    have ->: a3 = 0 by have := powR_ge0 _ _ : 0 <= a3; lra.
    rewrite !addr0 powR1 subrr.
    {
      rewrite {2}/maxr.
      case: ifPn.
      {
        move/(help (powR_ge0 _ _) p0).
        rewrite -/a2 {1}/maxr => h3.
        case: ifPn => //.
        move/(help' (se_ge0 _ _ _) p0).
        rewrite -/a1 subr0 powR1 gerDr => h4.
        have ->: a1 = 0 by have := powR_ge0 _ _ : 0 <= a1; lra.
        by rewrite add0r powR1 subrr.
      }
      move/(help' (powR_ge0 _ _) p0).
      rewrite -/a2 => h3.
      {
        rewrite {1}/maxr.
        case: ifPn => //.
        move/(help' (se_ge0 _ _ _) p0).
        rewrite -/a1.
        rewrite opprD opprK addrA subrr add0r -powRrM mulVf// powRr1.
        lra.
        by rewrite /a2 powR_ge0.
      }
    }
  }
  move/(help' (se_ge0 _ _ _) p0).
  rewrite -/a1 -/a2 => h1.
  {
    rewrite {1}/maxr.
    case: ifPn.
    move/(help (se_ge0 _ _ _) p0).
    rewrite -/a3 opprD opprK addrA subrr add0r -powRrM mulVf// /a1 /a2 (powRr1 (addr_ge0 (powR_ge0 _ _) (powR_ge0 _ _))) -/a1 -/a2 => h2.
    {
      rewrite {2}/maxr.
      case: ifPn.
      move/(help (se_ge0 _ _ _) p0).
      rewrite -/a2 -/a3 => h3.
      {
        rewrite subr0 powR1.
        rewrite {1}/maxr.
        case: ifPn => //.
        move/(help' (addr_ge0 (powR_ge0 _ _) (ltW ltr01)) p0).
        rewrite -/a1 gerDr => h4.
        have ->: a1 = 0 by have := powR_ge0 _ _ : 0 <= a1; lra.
        by rewrite add0r powR1 subrr.
      }
      move/(help' (se_ge0 _ _ _) p0).
      rewrite -/a2 -/a3 => h3.
      {
        rewrite {1}/maxr.
        case: ifPn => //.
        move/(help' (se_ge0 _ _ _) p0).
        rewrite opprD opprK addrA subrr add0r -/a1 -powRrM mulVf// ?powRr1.
        lra.
        by rewrite addr_ge0 ?powR_ge0.
      }
    }
    move/(help' (se_ge0 _ _ _) p0).
    rewrite -/a3 opprD opprK addrA subrr add0r -powRrM mulVf ?powRr1 ?(addr_ge0 (powR_ge0 _ _) (powR_ge0 _ _)) => //h2.
    {
      rewrite {2}/maxr.
      case: ifPn.
      move/(help (se_ge0 _ _ _) p0).
      rewrite -/a1 -/a2 -/a3 subr0 powR1 => h3.
      {
        rewrite {1}/maxr.
        case: ifPn.
        move/(help (addr_ge0 (powR_ge0 _ _) (ltW ltr01)) p0).
        rewrite -/a1 ltrDr => h4.
        lra.
        move/(help' (addr_ge0 (powR_ge0 _ _) (ltW ltr01)) p0).
        rewrite -/a1 gerDr => h4.
        have : a1 = 0 by have := powR_ge0 _ _ : 0 <= a1; lra.
        lra.
      }
      move/(help' (se_ge0 _ _ _) p0).
      rewrite -/a2 -/a3 => h3.
      {
        rewrite {1}/maxr.
        case: ifPn.
        move/(help (se_ge0 _ _ _) p0).
        rewrite -/a1 opprD opprK addrA subrr add0r -powRrM mulVf// ?powRr1 ?(addr_ge0 (powR_ge0 _ _) (powR_ge0 _ _))// => h4.
        lra.
        move => _.
        by rewrite -/a1 opprD opprK addrA subrr add0r -powRrM mulVf ?pneq0 ?powRr1 ?(addr_ge0 (powR_ge0 _ _) (powR_ge0 _ _)) ?addrA.
      }
    }
  }
(*Godel*)
+ set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  rewrite /minr.
  by repeat case: ifP; lra.
(*product*)
- set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
  lra.
Qed.
End translation_lemmas.
