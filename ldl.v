From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
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
(* - `ereal_type_translation`: same as before, but maps 
     `Bool_T` to $\bar{\mathbb R}}$                                           *)
(* - `bool_type_translation`: type translation for the boolean interpretation;*)
(*   maps `Bool_T` to `bool`                                                  *)
(* - `bool_translation`: maps an LDL-formula to a Boolean formula, with the   *)
(*   obvious interpretation                                                   *)
(* - `translation`: maps an LDL-formula to its fuzzy interpretation;    *)
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

(* Polarity of formulas: undef does not allow negation, while def allows negation *)
Inductive flag := def | undef.

Inductive ldl_type :=
| Bool_T of flag
| Index_T of nat
| Real_T
| Vector_T of nat
| Fun_T of nat & nat.

Definition Bool_T_undef := Bool_T undef.
Definition Bool_T_def := Bool_T def.

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
  | ldl_not : expr Bool_T_def-> expr Bool_T_def
  (* comparisons *)
  | ldl_cmp : forall x, comparison -> expr Real_T -> expr Real_T -> expr (Bool_T x)
  (* networks and applications *)
  | ldl_fun : forall n m, (n.-tuple R -> m.-tuple R) -> expr (Fun_T n m)
  | ldl_app : forall n m, expr (Fun_T n m) -> expr (Vector_T n) -> expr (Vector_T m)
  | ldl_lookup : forall n, expr (Vector_T n) -> expr (Index_T n) -> expr Real_T.

End expr.

HB.instance Definition _ (R : realType) b :=
  @gen_eqMixin (@expr R (Bool_T b)).
HB.instance Definition _ (R : realType) b := 
  @gen_choiceMixin (@expr R (Bool_T b)). 

Declare Scope ldl_scope.

Notation "a `/\ b" := (ldl_and [:: a; b]) (at level 45).
Notation "a `\/ b" := (ldl_or [:: a; b]) (at level 45).
Notation "a `=> b" := (ldl_or [:: (ldl_not a); b]) (at level 55).
Notation "`~ a"    := (ldl_not a) (at level 75).
Definition ldl_add {R : realType} := ldl_fun (fun (t : 2.-tuple R) => [tuple [tnth t 0] + [tnth t 1] ])%R.
Definition ldl_mul {R : realType} := ldl_fun (fun (t : 2.-tuple R) => [tuple [tnth t 0] * [tnth t 1] ])%R.
Definition ldl_sub {R : realType} := ldl_fun (fun (t : 2.-tuple R) => [tuple [tnth t 0] - [tnth t 1] ])%R.
Definition ldl_opp {R : realType}  := ldl_fun (fun (t : 1.-tuple R) => [tuple -[tnth t 0] ])%R.
Notation "a `+ b"  := (ldl_lookup (ldl_app ldl_add [tuple a; b]) 0) (at level 50).
Notation "a `- b"  := (ldl_lookup (ldl_app ldl_sub [tuple a; b]) 0) (at level 45).
Notation "a `* b"  := (ldl_lookup (ldl_app ldl_mul [tuple a; b]) 0) (at level 40).
Notation "`- a"    := (ldl_lookup (ldl_app ldl_opp [tuple a]) 0) (at level 45).

Local Open Scope ldl_scope.

Notation "a `<= b" := (ldl_cmp _ cmp_le a b) (at level 70).
Notation "a `== b" := (ldl_cmp _ cmp_eq a b) (at level 70).
Notation "a `!= b" := (`~ (a == b)) (at level 70).
Notation "a `< b"  := (a `<= b /\ a `!= b) (at level 70).
Notation "a `>= b" := (b `<= a) (at level 70).
Notation "a `> b"  := (b `< a) (at level 70).

Lemma expr_ind' (R : realType) :
  forall P : forall s : ldl_type, expr s -> Prop,
    (forall s : R, P Real_T (ldl_real s)) ->
    (forall (b : bool) p, P (Bool_T p) (ldl_bool p b)) ->
    (forall n (o : 'I_n), P (Index_T n) (ldl_idx o)) ->
    (forall n (t : n.-tuple R), P (Vector_T n) (ldl_vec t)) ->
    (forall b (l : seq (expr (Bool_T b))), List.Forall (fun x => P (Bool_T b) x) l -> P (Bool_T b) (ldl_and l)) ->
    (forall b (l : seq (expr (Bool_T b))), List.Forall (fun x => P (Bool_T b) x) l -> P (Bool_T b) (ldl_or l)) ->
    (forall e : expr Bool_T_def, P Bool_T_def e -> P Bool_T_def (`~ e)) ->
    (forall (n m : nat) (t : n.-tuple R -> m.-tuple R), P (Fun_T n m) (ldl_fun t)) ->
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
Context {R : realType}.

Definition type_translation (t : ldl_type) : Type:=
  match t with
  | Bool_T x => R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
end.

Definition bool_type_translation (t : ldl_type) : Type:=
  match t with
  | Bool_T x => bool
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
  end.

Definition ereal_type_translation (t : ldl_type) : Type :=
  match t with
  | Bool_T x => \bar R
  | Real_T => R
  | Vector_T n => n.-tuple R
  | Index_T n => 'I_n
  | Fun_T n m => n.-tuple R -> m.-tuple R
end.

End type_translation.

Section bool_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope mset_scope. 
Context {R : realType}.

Fixpoint bool_translation {t} (e : @expr R t) : bool_type_translation t :=
  match e in expr t return bool_type_translation t with
  | ldl_bool b x => x
  | ldl_real r => r%R
  | ldl_idx n i => i
  | ldl_vec n t => t

  | ldl_and b Es => \big[andb/true]_(i <- map bool_translation Es) i
  | ldl_or b Es => \big[orb/false]_(i <- map bool_translation Es) i
  | `~ E1 => ~~ << E1 >>

  | E1 `== E2 => << E1 >> == << E2 >>
  | E1 `<= E2 => << E1 >> <= << E2 >>

  | ldl_fun n m f => f
  | ldl_app n m f v => << f >> << v >>
  | ldl_lookup n v i => tnth << v >> << i >>
  end
where "<< e >>" := (bool_translation e).

Reserved Notation "Q |= P" (no associativity, at level 61).
Reserved Notation "Q |- P" (no associativity, at level 61).

Inductive seq_calc_bool_ms : {mset (@expr R Bool_T_def)}
  -> {mset (@expr R Bool_T_def)} -> Prop :=
| init : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def),
     a +` Q |= a +` P
| bot : forall (Q P : {mset (@expr R Bool_T_def)}),
    (ldl_bool def false) +` Q |= P
| top : forall (Q P : {mset (@expr R Bool_T_def)}),
    Q |= (ldl_bool def true) +` P
| and_R : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    Q |= a +` P  ->  Q |= ( b) +` P ->
      Q |=  (a `/\ b) +` P
| andL1 :  forall (Q P : {mset (@expr R Bool_T_def)}) (a b : @expr R Bool_T_def),
    a +` Q  |= P ->
      (a `/\ b) +` Q |= P
| andL2 :  forall (Q P : {mset (@expr R Bool_T_def)}) (a b : @expr R Bool_T_def),
    b +` Q  |= P ->
      (a `/\ b) +` Q |= P
| orR1 : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    Q |=  a +` P ->
      Q |=  (a `\/ b) +` P
| orR2 : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    Q |=  b +` P ->
      Q |=  (a `\/ b) +` P
| orL :  forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    a+`Q  |= P ->  b +` Q |= P ->
      (a `\/ b)+`Q |= P
(*not in lnguage for now, may add for fuzzy logic because of residuums*)
(*| implR : forall (Q P : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
     a+`Q |= b +`P ->
      Q |= (a `=> b) +` P
| implL : forall (Q P S : {mset (@expr R Bool_T_def)}) (a : @expr R Bool_T_def)
                 (b : (@expr R Bool_T_def)),
    Q |= a +` P ->   b+`Q |= S ->
      (a `=> b)+`Q |=  P `+` S
| negR : forall Q P a,
    a +`Q  |= P ->
      Q |= (`~ a) +` P*)
| negL : forall Q P a,
    Q |= a +` P ->
      (`~ a)+`Q|= P
where "Q |= P" := (seq_calc_bool_ms Q P).

Context {K : choiceType}.
Implicit Types  (A : {mset K}) (s : seq K).

Proposition sc_bool_consistent_weak : ~ (mset0 |= [mset ldl_bool def false]).
Proof.

(*have H3 := ms_non0 a Q. by [].*)
admit. (*probably not useful need a stronger version?*)
Admitted.

Proposition sc_bool_consistent (Q P : {mset expr Bool_T_def}): 
  Q |= P ->
  (forall (q : expr Bool_T_def), q \in Q -> <<q>> = <<ldl_bool def true>>) ->
     (forall (p : expr Bool_T_def) , (p \in P) -> <<p>> != <<ldl_bool def false>>).
Proof.
 rewrite //=. move => H0 H. dependent induction H0; move => p p0.
- have H1 := H p. rewrite in_mset1D in H1. (*after i apply H1 I'll have one non-provable case, must be
wrong lemma statement*)

Admitted.


Lemma sound_sc_bool_mseq' (Q P : {mset expr Bool_T_def}) :
Q |= P -> 
(forall (q : expr Bool_T_def), (q \in Q) -> <<q>> = <<ldl_bool def true>>) ->
               exists (p : expr Bool_T_def) , (p \in P) /\ <<p>> = <<ldl_bool def true>>.
Proof.
 rewrite //=. intros. dependent induction H.
- exists a. have H := H0 a. 
  rewrite in_mset1D eq_refl orTb ?andTb.
  move: H; rewrite in_mset1D eq_refl orTb ?andTb//=.
  auto.
- exfalso.  move: H0.
  rewrite//=. apply contrapT. rewrite  not_implyE.
  rewrite not_andE notE. left. 
  rewrite -existsNP.
  exists (ldl_bool def false).
  rewrite in_mset1D eq_refl orTb//=. 
  auto.
- exists (ldl_bool def true).
  by rewrite in_mset1D eq_refl orTb//=. 
- destruct (IHseq_calc_bool_ms1 H1) as [x [IH11 IH12]].
  destruct (IHseq_calc_bool_ms2 H1) as [y [IH21 IH22]].
  rewrite in_mset1D in IH11. move/orP: IH11.
  move => IH11.
  destruct IH11.
    + move/eqP: H2. move/esym => H2. subst. 
      rewrite in_mset1D in IH21. move/orP: IH21.
      move => IH21. destruct IH21. 
      * move/eqP: H2. move/esym => H2.
        subst. 
        exists (x `/\ y). 
        simpl; split; eauto.
        - by rewrite in_mset1D eq_refl orTb.
        - rewrite big_cons big_seq1. 
          by rewrite IH12 IH22.
      * exists y. rewrite IH22 in_mset1D H2 orbT. eauto.
    +  exists x.  rewrite IH12 in_mset1D H2 orbT. eauto.
- have H1 := (H0 (a `/\ b)). 
  rewrite in_mset1D eq_refl orTb in H1.
  simpl in H1.
  rewrite big_cons big_seq1 in H1.
  apply  IHseq_calc_bool_ms.
  intros. rewrite in_mset1D in H2. move/orP: H2.
      move => H2. destruct H2.
      * move/eqP: H2. move => H2.
        subst. apply andb_prop in H1.
        + destruct H1 as [ha hb].
          by apply ha.
        + by [].
      * apply H0. by rewrite in_mset1D H2 orbT.
- have H1 := (H0 (a `/\ b)). 
  rewrite in_mset1D eq_refl orTb in H1.
  simpl in H1.
  rewrite big_cons big_seq1 in H1.
  apply  IHseq_calc_bool_ms.
  intros. rewrite in_mset1D in H2. move/orP: H2.
      move => H2. destruct H2.
      * move/eqP: H2. move => H2.
        subst. apply andb_prop in H1.
        + destruct H1 as [ha hb].
          by apply hb.
        + by [].
      * apply H0. by rewrite in_mset1D H2 orbT.
- destruct (IHseq_calc_bool_ms H0) as [x [IH1 IH2]].
  rewrite in_mset1D in IH1. move/orP: IH1.
  move => IH1.
  destruct IH1.
    + move/eqP: H1. move => H1. subst. 
      exists (a `\/ b).
      rewrite in_mset1D eq_refl orTb//= big_cons big_seq1 IH2. 
      by rewrite orTb//.
    + exists x. 
      by rewrite IH2 in_mset1D H1 orbT//.
- destruct (IHseq_calc_bool_ms H0) as [x [IH1 IH2]].
  rewrite in_mset1D in IH1. move/orP: IH1.
  move => IH1.
  destruct IH1.
    + move/eqP: H1. move => H1. subst. 
      exists (a `\/ b).
      rewrite in_mset1D eq_refl orTb//= big_cons big_seq1 IH2. 
      by rewrite orbT//.
    + exists x. 
      by rewrite IH2 in_mset1D H1 orbT//.
- have H2 := (H1 (a `\/ b)). 
  rewrite in_mset1D eq_refl orTb in H2.
  simpl in H2.
  rewrite big_cons big_seq1 in H2.
  apply Bool.orb_prop in H2; rewrite//=.
  destruct H2 as [ha | hb].
  + apply  IHseq_calc_bool_ms1.
    intros. rewrite in_mset1D in H2. move/orP: H2.
      move => H2. destruct H2.
      * move/eqP: H2. move => H2.
        subst. by apply ha.
      * apply H1. by rewrite in_mset1D H2 orbT.
  + apply  IHseq_calc_bool_ms2.
    intros. rewrite in_mset1D in H2. move/orP: H2.
    move => H2. destruct H2.
    * move/eqP: H2. move => H2.
      subst. by apply hb.
    * apply H1. by rewrite in_mset1D H2 orbT.
- have H1 := H0 (`~ a). 
  rewrite in_mset1D eq_refl orTb in H1.
  destruct IHseq_calc_bool_ms as [x y]. 
  + intros. apply H0.
    by rewrite in_mset1D H2 orbT. 
  + exists x. destruct y as [h1 h2].
    rewrite h2.
    rewrite in_mset1D in h1. move/orP: h1. move => [h1 | h3].
    * move/eqP: h1. move => h1.
      subst. rewrite //= in H1.
      rewrite h2//= in H1.
      exfalso.
      move: H1. by auto.
    * by rewrite h3.
Qed.


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
   | ldl_bool _ true => (1%R : type_translation (Bool_T _))
   | ldl_bool _ false => (0%R : type_translation (Bool_T _))
   | ldl_real r => r%R
   | ldl_idx n i => i
   | ldl_vec n t => t

   | ldl_and _ Es =>
       match l with
       | Lukasiewicz => maxr (sumR (map translation Es) - (size Es)%:R+1) 0
       | Yager => maxr (1 - (sumR (map (fun E => (1 - ({[ E ]} : type_translation (Bool_T _)))`^p) Es))`^p^-1) 0
       | Godel => minR (map translation Es)
       | product => prodR (map translation Es)
       end
   | ldl_or _ Es =>
       match l with
       | Lukasiewicz => minr (sumR (map translation Es)) 1
       | Yager => minr ((sumR (map (fun E => ({[ E ]} : type_translation (Bool_T _))`^p) Es))`^p^-1) 1
       | Godel => maxR (map translation Es)
       | product => product_dl_prod (map translation Es)
       end

    | `~ E1 => 1 - {[ E1 ]}

    | E1 `== E2 => if {[ E1 ]} == -{[ E2 ]} then ({[ E1 ]} == {[ E2 ]})%:R else maxr (1 - `|({[ E1 ]} - {[ E2 ]}) / ({[ E1 ]} + {[ E2 ]})|) 0
    | E1 `<= E2 => if {[ E1 ]} == -{[ E2 ]} then ({[ E1 ]} <= {[ E2 ]})%R%:R else maxr (1 - maxr (({[ E1 ]} - {[ E2 ]}) / `|{[ E1 ]} + {[ E2 ]}|) 0) 0

    | ldl_fun n m f => f
    | ldl_app n m f v => (translation f) (translation v)
    | ldl_lookup n v i => tnth (translation v) (translation i)
    end
where "{[ e ]}" := (translation e).

End fuzzy_translation.

Section hypersequent_godel.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope mset_scope. 
Context {R : realType}.
Context {K : choiceType}.
Implicit Types  (A : {mset K}) (s : seq K).
Variable p : R. 
Local Notation "[[ e ]]_ l" := (translation l p e).

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).
(*entailment as pair (A, B) where A |- B*)


Inductive seq_calc_godel :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}
(*-> {mset (seq {mset (@expr R Bool_T_def)})}*)
      -> Prop :=
| id_g : forall (Q :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})})
                (A : {mset (@expr R Bool_T_def)}),
    seq_calc_godel ( (A |- A) +` Q)
(*structural*)
| ew_g : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_godel Q ->
    seq_calc_godel (Q `+` P) (*correct order*)
| ec_g : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_godel (Q `+` P `+` P) ->
    seq_calc_godel (Q `+` P)
(*this was a single conclusion version*)
(*| comm_hyper_g : forall  Q 
                  (A1 A2 B1 B2 C D: {mset (@expr R Bool_T_def)}),
    seq_calc_godel (((A1 `+` B1) |- C) +` Q) ->
    seq_calc_godel (((A2 `+` B2) |- D) +` Q) ->               
    seq_calc_godel (Q `+` [mset ((A1 `+` A2) |- C)] `+` [mset ((B1 `+` B2) |- D)])*)
| comm_hyper_g : forall  Q 
                  (A1 A2 B1 B2 C1 C2 D1 D2: {mset (@expr R Bool_T_def)}),
    seq_calc_godel (((A1 `+` B1) |- C1 `+` D1) +` Q) ->
    seq_calc_godel (((A2 `+` B2) |- C2 `+` D2) +` Q) ->               
    seq_calc_godel (Q `+` [mset ((A1 `+` A2) |- C1 `+` C2)] `+` [mset ((B1 `+` B2) |- D1 `+` D2)])
| comm_g : forall Q 
                  (A B C : {mset (@expr R Bool_T_def)}),
    seq_calc_godel (((A `+` B `+` B) |- C) +` Q) ->
    seq_calc_godel (((A `+` B) |- C) +` Q)
| weak_g : forall Q 
                  (A B C : {mset (@expr R Bool_T_def)}),
    seq_calc_godel ((A |- C) +` Q ) ->
    seq_calc_godel (((A `+` B) |- C) +` Q )
(*logical*)
| bot_g : forall Q 
                 (A B : {mset (@expr R Bool_T_def)}),
    seq_calc_godel (((ldl_bool def false +` A) |- B) +` Q)
| top_g : forall Q 
                 (A : {mset (@expr R Bool_T_def)}),
    seq_calc_godel ((A |- [mset (ldl_bool def true)]) +` Q )
| andL_g1 : forall Q 
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_godel (((a +` B) |- A) +` Q ) ->
    seq_calc_godel ((((a `/\ b) +` B) |- A) +` Q) 
| andL_g2 : forall Q
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_godel (((b +` B) |- A) +` Q ) ->
    seq_calc_godel ((((a `/\ b) +` B) |- A) +` Q )
| andR_g : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel ( (A |- [mset a]) +` Q ) ->
    seq_calc_godel ( (B |- [mset b]) +` Q) ->
    seq_calc_godel ((A |- [mset (a `/\ b)]) +` Q )
(*| orL_g : forall  Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((b +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset ((a +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset (((a `\/ b) +` B) |- A)])
| orR_g1 : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset a])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (a `\/ b)])])
| orR_g2 : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset b])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (a `\/ b)])])
| negR_g : forall Q
                  (A : {mset (@expr R Bool_T_def)})
                  (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset a])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (`~ a)])])
| negL_g : forall Q
                  (A B: {mset (@expr R Bool_T_def)})
                  (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((a +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset (((`~a) +` B) |- A)])*)

(*cut rule*)
| cut_g : forall Q
                 (A1 A2 B: {mset (@expr R Bool_T_def)})
                 (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((a +` A1) |- B)]) ->
    seq_calc_godel (Q `+` [mset (A2 |-[mset a])]) ->
    seq_calc_godel (Q `+` [mset ((A1 `+` A2) |- B)]).

(*or should it not be equal to 1? greater then something? or just non-equal to zero*)
Lemma sound_godel_1 (Q : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}):
seq_calc_godel Q -> 
exists (q : ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})), q \in Q 
/\ 
       (
         (forall (x : expr (Bool_T def)), x \in (fst q) -> [[x]]_Godel = [[ldl_bool def true]]_Godel) ->
         (exists (y : expr (Bool_T def)), y \in (snd q) /\ [[y]]_Godel = [[ldl_bool def true]]_Godel)

       ).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite in_mset1D eq_refl orTb. split. by [].  
  simpl. intros. exists (ldl_bool def true). rewrite//=. 
  split; first last.  by rewrite//=. 
  have H1 := H (ldl_bool def true). 
  rewrite//= in H1. move: H1.
  
  admit. (*I just need to make erefl work*)
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  exists q. rewrite in_msetD IH1 orTb. 
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_godel as [M [IH1 IH2]].   
  exists M. (*trivial, rearrange*) admit. 
(*the interesting one, communication ruleu*)
- destruct IHseq_calc_godel1 as [q1 [IH11 IH12]]. 
  destruct IHseq_calc_godel2 as [q2 [IH21 IH22]].
  have in_msetD3 : forall (q : K) (Q A B : {mset K}), q \in Q `+` A `+` B =
                         (q \in Q) || (q \in A) || (q \in B). {
    admit. 
  } 
  have h : exists qq, qq = q1 \/ qq = q2. {
  exists q1. left. by apply Logic.eq_refl.}
  destruct h as [qq Hq].
  exists qq. (*I don't think this exists will work*)
  split. 
  + admit.
  +
 admit.
 admit. admit.
- exists (ldl_bool def false +` A |- B).
  rewrite in_mset1D eq_refl orTb. split. by [].
  simpl. intros.
  have H1 := H (ldl_bool def false).
  rewrite//= in H1.
  exfalso. move: H1. apply contrapT. rewrite  not_implyE.
  rewrite not_andE notE. left. 
  rewrite in_mset1D eq_refl orTb//=.
  rewrite  not_implyE. split. by []. 
  
  (*just searching for right lemma, got 1<>0*)
  admit.
- exists ((A |- [mset ldl_bool def true])).
  split. admit. (*obvious, in_mset1D*)
  rewrite//=; move => _. 
  exists (ldl_bool def true). 
  rewrite mset11. split; rewrite//=; by []. 
- destruct IHseq_calc_godel as [Qa [IH1 IH2]].
  exists (a `/\ b +` B |- A).
  split. 
  + admit. (*obvious, belongs*)
  + rewrite//=. intros. 
    have H1 := H0 (a `/\ b).
    have h1 : a `/\ b \in a `/\ b +` B. {
      by  rewrite in_mset1D eq_refl orTb.
      }
    have Hab := H1 h1. rewrite//= in Hab.
    (*from this should be able to get that both a, b = 1 - given the proof of 
      domain consistency that can be borrowed from fuzzy.v*)

admit.
Admitted.


(*
nope, not this one, left as reminder, delete later
Lemma sound_hypersec_godel (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})})
                           (s : ({mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)}) ) :
(forall (q : expr (Bool_T def)), q \in (snd s) ->
                                      [[q]]_Godel = [[ldl_bool def true]]_Godel) ->
                seq_calc_godel (Q `+` [mset s] `+` P) -> (*does not work without P - but P not sufficient*)
                forall (x : expr (Bool_T def)), x \in (fst s) ->
                [[x ]]_Godel = [[ldl_bool def true]]_Godel.
Proof.
Admitted.*)
End hypersequent_godel.

Section hypersequent_lukasiewicz.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Local Open Scope mset_scope. 
Context {R : realType}.
Context {K : choiceType}.
Implicit Types  (A : {mset K}) (s : seq K).
Variable p : R. 
Local Notation "[[ e ]]_ l" := (translation l p e).

Reserved Notation "Q |- P" (no associativity, at level 61).
Notation "Q |- P" := (Q, P).
(*entailment as pair (A, B) where A |- B*)


Inductive seq_calc_luka :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}
(*-> {mset (seq {mset (@expr R Bool_T_def)})}*)
      -> Prop :=
| id_g : forall (Q :  {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})})
                (A : {mset (@expr R Bool_T_def)}),
    seq_calc_luka ( (A |- A) +` Q)
(*structural*)
| ew_g : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_luka Q ->
    seq_calc_luka (Q `+` P) (*correct order*)
| ec_g : forall (Q P : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}),
    seq_calc_luka (Q `+` P `+` P) ->
    seq_calc_luka (Q `+` P)
(*add split and mix rules*)
| comm_g : forall Q 
                  (A B C : {mset (@expr R Bool_T_def)}),
    seq_calc_luka (((A `+` B `+` B) |- C) +` Q) ->
    seq_calc_luka (((A `+` B) |- C) +` Q)
| weak_g : forall Q 
                  (A B C : {mset (@expr R Bool_T_def)}),
    seq_calc_luka ((A |- C) +` Q ) ->
    seq_calc_luka (((A `+` B) |- C) +` Q )
(*logical*)
| bot_g : forall Q 
                 (A B : {mset (@expr R Bool_T_def)}),
    seq_calc_luka (((ldl_bool def false +` A) |- B) +` Q)
| top_g : forall Q 
                 (A : {mset (@expr R Bool_T_def)}),
    seq_calc_luka ((A |- [mset (ldl_bool def true)]) +` Q )
| andL_g1 : forall Q 
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_luka (((a +` B) |- A) +` Q ) ->
    seq_calc_luka ((((a `/\ b) +` B) |- A) +` Q) 
| andL_g2 : forall Q
                   (A B : {mset (@expr R Bool_T_def)})
                   (a b : @expr R Bool_T_def),
    seq_calc_luka (((b +` B) |- A) +` Q ) ->
    seq_calc_luka ((((a `/\ b) +` B) |- A) +` Q )
| andR_g : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_luka ( (A |- [mset a]) +` Q ) ->
    seq_calc_luka ( (B |- [mset b]) +` Q) ->
    seq_calc_luka ((A |- [mset (a `/\ b)]) +` Q )
(*| orL_g : forall  Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((b +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset ((a +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset (((a `\/ b) +` B) |- A)])
| orR_g1 : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset a])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (a `\/ b)])])
| orR_g2 : forall Q
                  (A B : {mset (@expr R Bool_T_def)})
                  (a b : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset b])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (a `\/ b)])])
| negR_g : forall Q
                  (A : {mset (@expr R Bool_T_def)})
                  (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset (A |- [mset a])]) ->
    seq_calc_godel (Q `+` [mset (A |- [mset (`~ a)])])
| negL_g : forall Q
                  (A B: {mset (@expr R Bool_T_def)})
                  (a : @expr R Bool_T_def),
    seq_calc_godel (Q `+` [mset ((a +` B) |- A)]) ->
    seq_calc_godel (Q `+` [mset (((`~a) +` B) |- A)])*).

Define 

Lemma sound_luka_1 (Q : {mset ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})}):
seq_calc_godel Q -> 
exists (q : ( {mset (@expr R Bool_T_def)} * {mset (@expr R Bool_T_def)})), q \in Q 
/\ 
       (
         (forall (x : expr (Bool_T def)), x \in (fst q) -> [[x]]_Godel = [[ldl_bool def true]]_Godel) ->
         (exists (y : expr (Bool_T def)), y \in (snd q) /\ [[y]]_Godel = [[ldl_bool def true]]_Godel)

       ).
Proof.
intros; rewrite//=. dependent induction H.
- exists (A |- A). rewrite in_mset1D eq_refl orTb. split. by [].  
  simpl. intros. exists (ldl_bool def true). rewrite//=. 
  split; first last.  by rewrite//=. 
  have H1 := H (ldl_bool def true). 
  rewrite//= in H1. move: H1.
  
  admit. (*I just need to make erefl work*)
- destruct IHseq_calc_godel as [q [IH1 IH2]].
  exists q. rewrite in_msetD IH1 orTb. 
  split. by []. 
  by apply IH2.
- destruct IHseq_calc_godel as [M [IH1 IH2]].   
  exists M. (*trivial, rearrange*) admit. 
(*the interesting one, communication ruleu*)
- destruct IHseq_calc_godel1 as [q1 [IH11 IH12]]. 
  destruct IHseq_calc_godel2 as [q2 [IH21 IH22]].
  have in_msetD3 : forall (q : K) (Q A B : {mset K}), q \in Q `+` A `+` B =
                         (q \in Q) || (q \in A) || (q \in B). {
    admit. 
  } 
  have h : exists qq, qq = q1 \/ qq = q2. {
  exists q1. left. by apply Logic.eq_refl.}
  destruct h as [qq Hq].
  exists qq. (*I don't think this exists will work*)
  split. 
  + admit.
  +
 admit.
 admit. admit.
- exists (ldl_bool def false +` A |- B).
  rewrite in_mset1D eq_refl orTb. split. by [].
  simpl. intros.
  have H1 := H (ldl_bool def false).
  rewrite//= in H1.
  exfalso. move: H1. apply contrapT. rewrite  not_implyE.
  rewrite not_andE notE. left. 
  rewrite in_mset1D eq_refl orTb//=.
  rewrite  not_implyE. split. by []. 
  
  (*just searching for right lemma, got 1<>0*)
  admit.
- exists ((A |- [mset ldl_bool def true])).
  split. admit. (*obvious, in_mset1D*)
  rewrite//=; move => _. 
  exists (ldl_bool def true). 
  rewrite mset11. split; rewrite//=; by []. 
- destruct IHseq_calc_godel as [Qa [IH1 IH2]].
  exists (a `/\ b +` B |- A).
  split. 
  + admit. (*obvious, belongs*)
  + rewrite//=. intros. 
    have H1 := H0 (a `/\ b).
    have h1 : a `/\ b \in a `/\ b +` B. {
      by  rewrite in_mset1D eq_refl orTb.
      }
    have Hab := H1 h1. rewrite//= in Hab.


admit.
Admitted.

End hypersequent_lukasiewicz.


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

Let bigmine (s : seq (\bar R)) := \big[mine/+oo]_(i <- s) i.
Let bigmaxe (s : seq (\bar R)) := \big[maxe/-oo]_(i <- s) i.

Fixpoint stl_ereal_translation {t} (e : expr t) : ereal_type_translation t :=
  match e in expr t return ereal_type_translation t with
  | ldl_bool _ true => +oo
  | ldl_bool _ false => -oo
  | ldl_real r => r
  | ldl_idx n i => i
  | ldl_vec n t => t

  | ldl_and _ Es =>
      let A := map stl_ereal_translation Es in
      let a_min : \bar R := bigmine A in
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
      let a_max : \bar R := bigmaxe A in
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

Section min_max_dev.
Context {R : realType}.

Definition min_dev (x : R) (s : seq R) : R :=
  let r := \big[minr/x]_(i <- s) i in (x - r) * r^-1.

Lemma min_dev_nseq (p : R) n : min_dev p (nseq n.+1 p) = 0%R.
Proof. by rewrite /min_dev big_nseq iter_minr// subrr mul0r. Qed.

Definition max_dev {R : realType} (x : R) (s : seq R) : R :=
  let r := \big[maxr/x]_(i <- s) i in (r - x) * r^-1.

End min_max_dev.

Section stl_translation.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (p : R) (nu : R).
Hypothesis p1 : 1 <= p.
Hypothesis nu0 : 0 < nu.

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
      stl_and a_min a0 A
  | ldl_or _ [::] => -1
  | ldl_or _ (e0 :: s) =>
      let A := map stl_translation s in
      let a0 := stl_translation e0 in
      let a_max: R := \big[maxr/a0]_(i <- A) i in
      stl_or a_max a0 A
  | `~ E1 => - {[ E1 ]}

  | E1 `== E2 => - `| {[ E1 ]} - {[ E2 ]}|
  | E1 `<= E2 => {[ E2 ]} - {[ E1 ]}

  | ldl_fun n m f => f
  | ldl_app n m f v => {[ f ]} {[ v ]}
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

Section example_eps_delta_robust.
Local Open Scope ldl_scope.
Context {R : realType}.

Let ldl_norm_infty (n : nat) : @expr R (Fun_T n.+1 1) := ldl_fun (fun (t : (n.+1).-tuple R) =>
   [tuple \big[maxr/[tnth t 0] ]_(i <- t) i ])%R.

Let ldl_vec_sub (n : nat) : @expr R (Vector_T n) -> @expr R (Vector_T n) -> @expr R (Vector_T n).
Proof.
elim.
- move=> r. apply.
- move=> p b. apply.
- move=> m i. apply.
- move=> m t1.
  elim.
  + move=> r. exact: (ldl_real 0).
  + move=> p b. exact: (ldl_bool _ true).
  + move=> l i. exact: (ldl_idx i).
  + move=> l t2. exact: (ldl_vec [tuple nth 0 t1 i - nth 0 t2 i | i < l])%R.
  + move=> p s. exact: (ldl_bool _ true).
  + move=> p s. exact: (ldl_bool _ true).
  + move=> e1 e2. exact: e1.
  + move=> p c e1 e2 e3 e4. exact: (ldl_bool _ true).
  + move=> l k f. exact: ldl_fun f.
  + move=> l k e1 e2 v1 v2. exact: (ldl_vec [tuple 0 | i < k])%R.
  + move=> l v1 v2 i1 i2. exact: (ldl_real 0).
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p c e f1 e1 f2 e2. exact: e2.
- move=> m l f e. exact: e.
- move=> m l e1 f1 e2 f2. exact.
- move=> m e1 f1 e2 f2. exact.
Defined.

Context (n m : nat) (eps delta : @expr R Real_T) (f : @expr R (Fun_T (n.+1) (m.+1)))
  (v : @expr R (Vector_T (n.+1))) (x : @expr R (Vector_T (n.+1))).

Definition eps_delta_robust :=
    (((ldl_lookup (ldl_app (ldl_norm_infty n) (ldl_vec_sub x v)) (ldl_idx ord0)) `<= eps)
       `=> ((ldl_lookup (ldl_app (ldl_norm_infty m) (ldl_vec_sub (ldl_app f x) (ldl_app f v))) (ldl_idx ord0))
       `<= delta)).

End example_eps_delta_robust.

Section example_hierarchichal.
Local Open Scope ldl_scope.
Context {R : realType}.

Let ldl_sum_real : @expr R Real_T -> @expr R Real_T -> @expr R Real_T.
Proof.
elim.
- move=> r. apply.
- move=> p b. apply.
- move=> m i. apply.
- move=> m t1.
  elim.
  + move=> r. exact: (ldl_real 0).
  + move=> p b. exact: (ldl_bool _ true).
  + move=> l i. exact: (ldl_idx i).
  + move=> l t2. exact: (ldl_vec [tuple nth 0 t1 i - nth 0 t2 i | i < l])%R.
  + move=> p s. exact: (ldl_bool _ true).
  + move=> p s. exact: (ldl_bool _ true).
  + move=> e1 e2. exact: e1.
  + move=> p c e1 e2 e3 e4. exact: (ldl_bool _ true).
  + move=> l k f. exact: ldl_fun f.
  + move=> l k e1 e2 v1 v2. exact: (ldl_vec [tuple 0 | i < k])%R.
  + move=> l v1 v2 i1 i2. exact: (ldl_real 0).
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p c e f1 e1 f2 e2. exact: e2.
- move=> m l f e. exact: e.
- move=> m l e1 f1 e2 f2. exact.
- move=> m e1 f1 e2 f2. exact.
Defined.

Let ldl_real_sub : @expr R Real_T -> @expr R Real_T -> @expr R Real_T.
Proof.
elim.
- move=> r. apply.
- move=> p b. apply.
- move=> m i. apply.
- move=> m t1.
  elim.
  + move=> r. exact: (ldl_real 0).
  + move=> p b. exact: (ldl_bool _ true).
  + move=> l i. exact: (ldl_idx i).
  + move=> l t2. exact: (ldl_vec [tuple nth 0 t1 i - nth 0 t2 i | i < l])%R.
  + move=> p s. exact: (ldl_bool _ true).
  + move=> p s. exact: (ldl_bool _ true).
  + move=> e1 e2. exact: e1.
  + move=> p c e1 e2 e3 e4. exact: (ldl_bool _ true).
  + move=> l k f. exact: ldl_fun f.
  + move=> l k e1 e2 v1 v2. exact: (ldl_vec [tuple 0 | i < k])%R.
  + move=> l v1 v2 i1 i2. exact: (ldl_real 0).
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p s e. exact: e.
- move=> p c e f1 e1 f2 e2. exact: e2.
- move=> m l f e. exact: e.
- move=> m l e1 f1 e2 f2. exact.
- move=> m e1 f1 e2 f2. exact.
Defined.

Fixpoint ldl_sum_vec (x : seq (@expr R Real_T)) :=
  \big[ldl_sum_real/ldl_real 0]_(i <- x) i.


Definition prob_group (n m : nat)
  (f : @expr R (Fun_T (n.+1) (m.+1)))
  (x : @expr R (Vector_T (n.+1)))
  (gs : seq (@expr R (Index_T (m.+1)))) :=
  
  ldl_sum_vec (map (ldl_lookup (ldl_app f x)) gs).

Context (n m : nat)
  (eps : @expr R Real_T)
  (f : @expr R (Fun_T (n.+1) (m.+1)))
  (x : @expr R (Vector_T (n.+1)))
  (Gs : seq (seq (@expr R (Index_T (m.+1)))))
  (r : flag).

(*Let fancy_or (eps p: @expr R Real_T) : expr (Bool_T r) :=
      (*(p `<= eps) `\/ ((ldl_real_sub (ldl_real 1%R) p) `<= eps).*)
      
     (* (p `<= eps) `\/ ((ldl_real 1%R `- p) `<= eps).*)


 (*(ldl_cmp r cmp_le p eps) `\/ (ldl_cmp r cmp_le (ldl_real_sub (ldl_real 1%R) p) eps).*)*)


(*Definition group_similiarity :=
  ldl_and (map (fancy_or r eps) (map (prob_group f x) Gs)).*)


End example_hierarchichal.
