From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import util ldl.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Section stl_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (nu : R).
Hypothesis nu0 : 0 < nu.

Lemma andI_stl (e : expr Bool_N) :
  nu.-[[e `/\ e]]_stl' = nu.-[[e]]_stl'.
Proof.
rewrite /=/sumR !big_cons !big_nil/=.
set a_min := minr (nu.-[[e]]_stl') (nu.-[[e]]_stl').
set a := ((nu.-[[e]]_stl' - a_min) * a_min^-1).
have a_min_e : a_min = nu.-[[e]]_stl'.
  by rewrite /a_min /minr; repeat case: ifPn => //; rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0.
  by rewrite /a a_min_e subrr ?mul0r.
rewrite !addr0 !mulr0 expR0 !mulr1/= a_min_e.
have -> : ((nu.-[[e]]_stl' + nu.-[[e]]_stl') * (1 + 1)^-1) = nu.-[[e]]_stl'.
  have -> : 1 + 1 = (2 : R) by lra.
  by rewrite mulrDl -splitr.
case: ifPn => //h1.
case: ifPn => //h2.
by apply le_anti; rewrite !leNgt h1 h2.
Qed.

Lemma andC_stl (e1 e2 : expr Bool_N) :
  nu.-[[e1 `/\ e2]]_stl' = nu.-[[e2 `/\ e1]]_stl'.
Proof.
rewrite /=/sumR !big_cons !big_nil/= !addr0.
set a_min := minr (nu.-[[e1]]_stl') (nu.-[[e2]]_stl').
have -> : (minr (nu.-[[e2]]_stl') (nu.-[[e1]]_stl')) = a_min.
  by rewrite /a_min/minr; case: ifPn => h1; case: ifPn => h2//; lra.
set a1 := ((nu.-[[e1]]_stl' - a_min) * a_min^-1).
set a2 := ((nu.-[[e2]]_stl' - a_min) * a_min^-1).
set d1 := (expR (nu * a1) + expR (nu * a2))%R.
have -> : (expR (nu * a2) + expR (nu * a1))%R = d1.
  by rewrite addrC.
case: ifPn; first by rewrite addrC.
by case: ifPn; first by rewrite addrC.
Qed.

Lemma orI_stl (e : expr Bool_N) :
  nu.-[[e `\/ e]]_stl' = nu.-[[e]]_stl'.
Proof.
rewrite /=/sumR !big_cons !big_nil/= !addr0.
set a_max := maxr (nu.-[[e]]_stl') (nu.-[[e]]_stl').
set a :=  ((a_max - nu.-[[e]]_stl') / a_max).
have a_max_e : a_max = nu.-[[e]]_stl'.
  by rewrite /a_max /maxr; repeat case: ifPn => //; rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0.
  by rewrite /a a_max_e subrr ?mul0r.
rewrite !mulr0 expR0 !mulr1/= a_max_e.
have -> : ((nu.-[[e]]_stl' + nu.-[[e]]_stl') * (1 + 1)^-1) = nu.-[[e]]_stl'.
  have -> : 1 + 1 = (2 : R) by lra.
  by rewrite mulrDl -splitr.
case: ifPn => //h1.
case: ifPn => //h2.
by apply le_anti; rewrite !leNgt h1 h2.
Qed.

Lemma orC_stl (e1 e2 : expr Bool_N) :
  nu.-[[e1 `\/ e2]]_stl'  = nu.-[[e2 `\/ e1]]_stl'.
Proof.
rewrite /=/sumR !big_cons !big_nil/= !addr0.
set a_max := maxr (nu.-[[e2]]_stl') (nu.-[[e1]]_stl').
have -> : maxr (nu.-[[e1]]_stl') (nu.-[[e2]]_stl') = a_max.
  by rewrite /a_max/maxr; case: ifPn => //; case: ifPn => //; lra.
set a1 := ((a_max - nu.-[[e1]]_stl') * a_max^-1).
set a2 := ((a_max - nu.-[[e2]]_stl') * a_max^-1).
set d1 := (expR (nu * a1) + expR (nu * a2))%R.
have -> : (expR (nu * a2) + expR (nu * a1))%R = d1.
  by rewrite addrC.
case: ifPn; first by rewrite addrC.
by case: ifPn; first by rewrite addrC.
Qed.

Lemma stl_translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  nu.-[[ e ]]_stl' = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ _ e2 erefl JMeq_refl).
Qed.

Lemma stl_translations_Index_coincide: forall n (e : expr (Index_T n)),
  nu.-[[ e ]]_stl' = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma stl_translations_Real_coincide (e : expr Real_T):
  nu.-[[ e ]]_stl' = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite stl_translations_Vector_coincide stl_translations_Index_coincide.
Qed.

Definition is_stl b (x : R) := (if b then x >= 0 else x < 0).

Lemma sumr_lt0:
  forall [R : realType] [I : eqType] [r : seq I] 
    [P : pred I] [F : I -> R],
  (forall i : I, i \in r -> P i -> (F i < 0%R)) ->
  ((\sum_(i <- r | P i) F i)%R < 0%R).
Admitted.

Lemma sumr_gt0:
  forall [R : realType] [I : eqType] [r : seq I] 
    [P : pred I] [F : I -> R],
  (forall i : I, i \in r -> P i -> (0 < F i)) ->
  (0 < \sum_(i <- r | P i) F i).
Admitted.

Lemma stl_nary_inversion_andE1 (Es : seq (expr Bool_P) ) :
  is_stl true (nu.-[[ and_E Es ]]_stl') -> (forall i, (i < size Es)%N -> is_stl true (nu.-[[ nth (Bool false false) Es i ]]_stl')).
Proof.
case: Es => // a l.
rewrite/is_stl/= foldrE big_map.
set a_min := \big[minr/nu.-[[a]]_stl']_(j <- l) nu.-[[j]]_stl'.
case: ifPn=>[hminlt0|].
  rewrite/sumR leNgt !big_cons !big_map pmulr_llt0 ?invr_gt0; last first.
    set x := _ + _.
    suff : 0 < x. lra.
    by rewrite /x -{1}(addr0 0) ltrD// ?expR_gt0// sumr_gt0// => i _ _; rewrite expR_gt0.
  set x := _ + _.
  suff : x < 0. lra.
  rewrite /x -{2}(addr0 0) ltrD//.
    by rewrite mulr_lt0 lt_eqF nmulr_rlt0 ?gt_eqF//= ?expR_gt0// ?(ltNge (expR _)) ?expR_ge0.
  apply sumr_lt0 => i _ _.
  by rewrite mulr_lt0 lt_eqF nmulr_rlt0 ?gt_eqF//= ?expR_gt0// ?(ltNge (expR _)) ?expR_ge0.
rewrite -leNgt => hminge0.
Admitted.

Lemma stl_nary_inversion_andE0 (Es : seq (expr Bool_P) ) :
  is_stl false (nu.-[[ and_E Es ]]_stl') -> (exists (i : nat), is_stl false (nu.-[[ nth (Bool false false) Es i ]]_stl') && (i < size Es)%nat).
Admitted.

Lemma stl_nary_inversion_orE1 (Es : seq (expr Bool_P) ) :
  is_stl true (nu.-[[ or_E Es ]]_stl') -> (exists i, is_stl true (nu.-[[ nth (Bool _ false) Es i ]]_stl') && (i < size Es)%nat).
Admitted.

Lemma stl_nary_inversion_orE0 (Es : seq (expr Bool_P) ) :
    is_stl false (nu.-[[ or_E Es ]]_stl') -> (forall i, (i < size Es)%nat -> is_stl false (nu.-[[ nth (Bool false false) Es i ]]_stl')).
Admitted.

Lemma stl_soundness (e : expr Bool_P) b :
  is_stl b (nu.-[[ e ]]_stl') -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind'.
- by move: b b0 => [] [] //=; rewrite ?leNgt ?ltrN10 ?ltr10.
- rewrite List.Forall_forall in H.
  move: b => []. rewrite /is_stl.
  + move/stl_nary_inversion_andE1.
    rewrite [bool_translation (and_E l)]/= foldrE big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (Bool _ false).
    by apply: H => //; rewrite ?h// -In_in mem_nth.
  + move/stl_nary_inversion_andE0.
    rewrite [bool_translation (and_E l)]/= foldrE big_map big_all.
    elim=>// i /andP[i0 isize].
    apply/allPn; exists (nth (Bool _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    by rewrite -In_in mem_nth.
- rewrite List.Forall_forall in H.
  move: b => [|].
  + move/stl_nary_inversion_orE1.
    rewrite [bool_translation (or_E l)]/= foldrE big_map big_has.
    elim=>// i /andP[i0 isize].
    apply/hasP; exists (nth (Bool _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
  + move/stl_nary_inversion_orE0.
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

(* Ale: disabled for now
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
*)
