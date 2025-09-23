From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals ereal interval_inference.
From mathcomp Require Import topology derive.
From mathcomp Require Import normedtype sequences exp measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra ldl.

(**md**************************************************************************)
(* # Properties of fuzzy DLs:                                                 *)
(*   Lukaseiwicz, Yager, Godel and product                                    *)
(*                                                                            *)
(*  grouped by DL, unless generic enough to apply to all fuzzy DLs            *)
(*                                                                            *)
(*                                                                            *)
(* ## Adequacy                                                                *)
(* - translations_Fun_coincide == shows that the Boolean translation          *)
(*   and the fuzzy translation coincide on expressions of type Fun_T          *)
(* - translations_Vector_coincide == shows that the Boolean translation       *)
(*   and the fuzzy translation coincide on expressions of type Vector_T       *)
(* - translations_Index_coincide == shows that the Boolean translation        *)
(*   and the fuzzy translation coincide on expressions of type Index_T        *)
(* - translations_Real_coincide == shows that the Boolean translation and     *)
(* - translate_boolT_01 == invariant for the translation: all values are in  *)
(*                          the range $[-1, 0]$                               *)
(* - nary_inversion_andE1 == inversion lemma for conjunction/true             *)
(* - nary_inversion_andE0 == inversion lemma for conjuntion/false             *)
(* - nary_inversion_orE1 == inversion lemma for disjunction/true              *)
(* - nary_inversion_orE0 == inversion lemma for disjunction/false             *)
(*   the fuzzy translation coincide on expressions of type Real_T             *)
(* - adequacy == final adequacy result for Godel and product                  *)
(*                                                                            *)
(* ## Structural properties for Lukasiewicz                                   *)
(* - Lukasiewicz_mandC_nary == n-ary commutativity of monoidal conjunction    *)
(* - Lukasiewicz_mandC == commutativity of monoidal conjunction               *)
(* - Lukasiewicz_morC_nary == n-ary commutativity of monoidal disjunction     *)
(* - Lukasiewicz_morC_ == commutativity of monoidal disjunction               *)
(* - Lukasiewicz_morA == associativity of monoidal disjunction                *)
(* - Lukasiewicz_mandA == associativity of monoidal conjunction               *)
(* - Lukasiewicz_mand_unit == unit element monoidal conjunction               *)
(* - Lukasiewicz_mor_unit == unit element monoidal disjunction                *)
(* - Lukasiewicz_residuation == residuation                                   *)
(* - Lukasiewicz_prelinearity == prealineartiy                                *)
(* - Lukasiewicz_involution == involution of negation                         *)
(* - Lukasiewicz_demorgan_mand == de Morgan 1, monoidal connectives           *)
(* - Lukasiewicz_demorgan_mord == de Morgan 1, monoidal connectives           *)
(*                                                                            *)
(* ## Structural properties for Yager                                         *)
(* - Yager_mandC_nary == n-ary commutativity of conjunction                   *)
(* - Yager_mandC == commutativity of conjunction                              *)
(* - Yager_morC_nary == n-ary commutativity of disjunction                    *)
(* - Yager_morC_ == commutativity of disjunction                              *)
(* - Yager_morA == associativity of disjunction                               *)
(* - Yager_mandA == associativity of conjunction                              *)
(* - Yager_mand_unit == unit element conjunction                              *)
(* - Yager_mor_unit == unit element monoidal disjunction                      *)
(* - Yager_involution == involution of negation                               *)
(*                                                                            *)
(* ## Structural properties for Godel                                         *)
(* - Godel_mandI == idempotence of conjunction                                *)
(* - Godel_morI == idempotence of disjunction                                 *)
(* - Godel_mandC_nary == n-ary commutativity of conjunction                   *)
(* - Godel_mandC == commutativity of conjunction                              *)
(* - Godel_morC_nary == n-ary commutativity of disjunction                    *)
(* - Godel_morC_ == commutativity of disjunction                              *)
(* - Godel_morA == associativity of disjunction                               *)
(* - Godel_mandA == associativity of conjunction                              *)
(* - Godel_mand_unit == unit element conjunction                              *)
(* - Godel_mor_unit == unit element monoidal disjunction                      *)
(* - Godel_residuation == residuation                                         *)
(* - Godel_prelinearity == prealineartiy                                      *)
(* - Godel_demorgan_mand == de Morgan 1, monoidal connectives                 *)
(* - Godel_demorgan_mord == de Morgan 1, monoidal connectives                 *)
(*                                                                            *)
(* ## Structural properties for product                                       *)
(* - product_mandC_nary == n-ary commutativity of conjunction                 *)
(* - product_mandC == commutativity of conjunction                            *)
(* - product_morC_nary == n-ary commutativity of disjunction                  *)
(* - product_morC_ == commutativity of disjunction                            *)
(* - product_morA == associativity of disjunction                             *)
(* - product_mandA == associativity of conjunction                            *)
(* - product_mand_unit == unit element conjunction                            *)
(* - product_mor_unit == unit element monoidal disjunction                    *)
(* - product_residuation == residuation                                       *)
(* - product_prelinearity == prealineartiy                                    *)
(* - product_demorgan_mand == de Morgan 1, monoidal connectives               *)
(* - product_demorgan_mord == de Morgan 1, monoidal connectives               *)
(*                                                                            *)
(* ## Shared structural properties                                            *)
(* - fuzzy_and_abs == absorption of lattice conjunction                       *)
(* - fuzzy_or_abs == absorption of lattice disjunction                        *)
(* - fuzzy_landI == idempotence of lattice conjunction                        *)
(* - fuzzy_lorI == aidempotencebsorption of lattice disjunction               *)
(* - fuzzy_orC_nary == n-ary commutativity of lattice disjunction             *)
(* - fuzzy_orC_ == commutativity of lattice disjunction                       *)
(* - fuzzy_orA == associativity of lattice disjunction                        *)
(* - fuzzy_andA == associativity of lattice conjunction                       *)
(* - fuzzy_and_distr == distributivity                                        *)
(* - fuzzy_and_distr2 == distributivity                                       *)
(* - fuzzy_demorgan_mand == de Morgan 1, lattice connectives                  *)
(* - fuzzy_demorgan_mord == de Morgan 1, lattice connectives                  *)
(*                                                                            *)
(* ## Shadow-lifting                                                          *)
(* - product_and v == $\product_{i < n} v_i$                                  *)
(* - shadowlifting_product_andE == shadow-lifting for product                 *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

HB.instance Definition _ (R : realType) x y z v :=
  @gen_eqMixin (@expr R (boolT x y z v)).

Section translation_lemmas.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (l : DL) (p : R).
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (@translation R l p _ e).

Lemma translations_coincide t (e : @expr R t) n m j :
  (t = realT \/ t = vectorT n \/ t = indexT n \/ t = funT n m \/ t = fun2T n m j) ->
  [[ e ]]_l ~= [[ e ]]_B.
Proof.
dependent induction e using expr_ind' => //=; move=> [|[|[|[|]]]]t0//.
- rewrite (JMeq_eq (IHe1 n m j _)); last by (right; right; right; left).
  by rewrite (JMeq_eq (IHe2 n m j _)); last by (right; left).
- rewrite (JMeq_eq (IHe1 n m l0 _)); last by (right; right; right; right).
  rewrite (JMeq_eq (IHe2 n m l0 _)); last by (right; left).
  by rewrite (JMeq_eq (IHe3 m n l0 _)); last by (right; left).
- rewrite (JMeq_eq (IHe1 n m j _)); last by (right; left).
  by rewrite (JMeq_eq (IHe2 n m j _)); last by (right; right; left).
Qed.

Lemma translations_Fun_coincide:
  forall n m (e : expr (funT n m)), [[ e ]]_l = [[ e ]]_B.
Proof.
by move=> n m e; apply/JMeq_eq/(translations_coincide _ _ n m 0); right;right;right;left.
Qed.

Lemma translations_Vector_coincide: forall n (e : @expr R (vectorT n)),
  [[ e ]]_l = [[ e ]]_B.
Proof.
by move=> n e; apply/JMeq_eq/(translations_coincide _ _ n 0 0); right;left.
Qed.

Lemma translations_Index_coincide: forall n (e : expr (indexT n)),
  [[ e ]]_l = [[ e ]]_B.
Proof.
by move=> n e; apply/JMeq_eq/(translations_coincide _ _ n 0 0); right;right;left.
Qed.

Lemma translations_Real_coincide (e : expr realT):
  [[ e ]]_l = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(translations_coincide _ _ 0 0 0); left.
Qed.

(*move to analysis/mathcomp*)
Lemma powRpinv (r : R) :r > 0 -> 1 = 1 `^ r.
Proof. by rewrite powR1. Qed.

Lemma powR_le1 (x r : R) : r > 0 -> 0 <= x ->  x <= 1 -> x `^ r <= 1.
Proof.
move=> r0 x0 x1. rewrite (powRpinv r)//=.
apply ge0_ler_powR; rewrite ?nnegrE ?invr_ge0//=. lra.
Qed.

Lemma pow_le01 (x r : R) : r > 0 -> 0 <= x <= 1 -> 0 <= x `^ r <= 1.
Proof.
move => r0 H.
apply /andP; split; first by rewrite powR_ge0.
apply powR_le1; rewrite//=; lra.
Qed.

Lemma translate_boolT_01 dl f1 f2 f3 (e : expr (boolT_def f1 f2 f3)) :
  0 <= [[ e ]]_ dl <= 1.
Proof.
dependent induction e using expr_ind'.
- rewrite /=; case b; lra.
- apply/andP => /=; split.
  * rewrite /minR big_seq.
    rewrite le_bigmin => //=i _.
    exact: (andP (@H _ _ _ _ _ _ _ _ _)).1.
  * rewrite /minR big_seq bigmin_idl.
    suff : forall (x y : R), minr x y <= x => // x y.
    by rewrite /minr; case: ifPn; lra.
- apply/andP => /=; split.
  * rewrite /maxR bigmax_idl.
    suff : forall (x y : R), x <= maxr x y => // x y.
    by rewrite /maxr; case: ifPn; lra.
  * rewrite /maxR bigmax_le ?ler01// => i il0.
    exact: (andP (H _ _ _ _ _ _ _ _ _)).2.
- move: IHe => /(_ _ _ _ _ _ e erefl JMeq_refl).
  have h' : forall (x : R), 0 <= x <= 1 ->
           0 <= 1 - x <= 1 by intros; lra.
  case dl => //=; move => h; apply h in p1; set (a := [[e]]_ _) in *; apply h' in p1;
  rewrite//=. 
  + case: ifP; lra.
  + case: ifP; lra.
- move: IHe1 => /(_ _ _ _ _ _ e1 erefl JMeq_refl).
  move: IHe2 => /(_ _ _ _ _ _  e2 erefl JMeq_refl).
  case: dl; rewrite /=; move => H1 H2.
  + rewrite /minr. case: ifPn; last by lra.
    intros.
    have h : forall (a b: R), (0 <= a <= 1) ->
                              0 <= b <= 1 ->
                              0 <= ((1 - a)%R + b)%E. intros. lra.
    have h' := @h ([[e1]]_Lukasiewicz) ([[e2]]_Lukasiewicz) (H2 _ p1) (H1 _ p1). lra.
  + rewrite /minr. repeat case: ifP; first by lra.
    have p0 : 0 <= p by rewrite (le_trans ler01 p1).
    move => /negP/negP h. rewrite ltNge Bool.negb_involutive in h.
    have powRpinv : 1 = 1 `^ p^-1.
      by rewrite powR1.
    have powRle1 : forall x, 0 <= x ->  x <= 1 -> x `^ p^-1 <= 1.
      move=> x x0; rewrite {2}powRpinv.
      move => hh.
      apply ge0_ler_powR; rewrite ?nnegrE ?invr_ge0//=. 
    apply /andP; split.
    * have H2' := H2 p p1. 
      have H1' := H1 p p1.
      rewrite subr_gte0 powRle1 ?powR_ge0//=.
      - have he12 : 1 - [[e2]]_Yager >= 1 - [[e1]]_Yager by lra.
        rewrite subr_ge0; apply ge0_ler_powR; rewrite ?nnegrE//=. 
        + lra.
        + lra.
      - have H1e : 0 <= (1 - [[e1]]_Yager) <= 1. lra.
        have H2e : 0 <= (1 - [[e2]]_Yager) <= 1. lra.
        have p0' : p > 0. clear -p1. 
          have ltr_le_trans : forall (x y z : R), x < y -> y <= z -> x < z. intros; lra.
          by rewrite (ltr_le_trans _ 1)//=.
        apply (pow_le01 _ p p0') in H2e.
        apply (pow_le01 _ p p0') in H1e. lra.
    *  by rewrite gerBl powR_ge0.
  + case: ifP; intros; apply H1 in p1; rewrite ?(H2 _ p1)//=; lra.
  + case: ifPn; have H1' := (H2 _ p1); have H2' := (H1 _ p1); intros; 
    rewrite ?divr_ge0 ?ler_pdivrMr //= ?mul1r; try lra. 
  + rewrite /maxr;  case: ifPn; move => _; 
    have H1' := (H2 _ p1); have H2' := (H1 _ p1); rewrite//=. 
    have h : forall (a : R), 0 <= a <= 1 ->
                               0 <= 1 - a <= 1. intros; lra.
    have h' := @h ([[e1]]_GodelS) (H2 _ p1); rewrite//=.
  + have h : forall (a : R), 0 <= a <= 1 ->
                               0 <= 1 - a <= 1. intros; lra.
    have h1 : forall (a b : R), 0 <= a <= 1 ->
                              0 <= b <= 1 ->
                              0 <= a  * b <= 1. intros; nra.
    have h' := @h ([[e2]]_productS) (H1 _ p1). 
    have h1' := h1 _ _ h' (H2 _ p1).
    have H := h _ h1'. rewrite//=.
- move: H; case: dl => /= H.
  + rewrite /maxr. case: ifP.
    * by lra.
    * move=> /negbT; rewrite -leNgt => -> /=.
      rewrite -lerBrDr subrr subr_le0 sum_01// => i.
      exact: (andP (H i _ _ _ _ _ _ _ _)).2.
  + rewrite /maxr. case: ifP.
    * by lra.
    * move=> /negbT; rewrite -leNgt => -> /=.
      by rewrite gerBl ?powR_ge0.
  + apply/andP; split.
    * rewrite /minR le_bigmin// => i _.
      by apply: (andP (@H _ _ _ _ _ _ _ _ _)).1 => //.
    * rewrite /minR bigmin_idl.
      suff : forall (x y : R), minr x y <= x => // x y.
      by rewrite /minr; case: ifPn; lra.
  + apply: prod01 => i.
    by apply: H _ _ _ _ _ => //.
  + apply/andP; split.
    * rewrite /minR big_seq.
      rewrite le_bigmin// => i _.
      exact: (andP (@H _ _ _ _ _ _ _ _ _)).1 => //=.
    * rewrite /minR  bigmin_idl.
      suff : forall (x y : R), minr x y <= x => // x y.
      by rewrite /minr; case: ifPn; lra.
  + apply: prod01 => i.
    exact: H.
- move: H. case: dl => /= H.
  + rewrite /minr. case: ifP.
    * move=> /ltW ->.
      rewrite andbT sumr_ge0// => i _.
      exact: ((andP (H i _ _ _ _ _ _ _ _)).1).
    * by lra.
  + rewrite /minr. case: ifP.
    * move=> /ltW ->.
      by rewrite andbT powR_ge0.
    * by lra.
  + rewrite /maxR.
    apply/andP; split.
    * rewrite bigmax_idl.
      suff : forall (x y : R), x <= maxr x y => // x y.
      by rewrite /maxr; case: ifPn; lra.
    * rewrite bigmax_le ?ler01// => i il0.
      exact: (andP (H _ _ _ _ _ _ _ _ _)).2.
  + rewrite /product_dl_prod product_dl_mul_seq_01=> //i il0.
    exact: H.
  + rewrite /maxR.
    apply/andP; split.
    * rewrite bigmax_idl.
      suff : forall (x y : R), x <= maxr x y => // x y.
      by rewrite /maxr; case: ifPn; lra.
    * rewrite bigmax_le ?ler01// => i il0.
      exact: (andP (H  _ _ _ _ _ _ _ _ _)).2.
  + rewrite /product_dl_prod product_dl_mul_seq_01=> //i il0.
    exact: H.
- case: c => /=; case: ifP => ?.
  - by case: ([[e1]]_dl <= [[e2]]_dl)%R; rewrite lexx ler01.
  - by rewrite le_max lexx orbT/= ge_max ler01 gerBl// le_max lexx orbT.
  - by case: ([[e1]]_dl == [[e2]]_dl); rewrite lexx ler01.
  - by rewrite le_max lexx orbT/= ge_max ler01 gerBl// normr_ge0 andTb.
Qed.

Lemma nary_inversion_mandE1 f1 f2 n (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ @ldl_mand R _ _ _ n s ]]_ l = 1 -> forall i, [[ s i ]]_ l = 1.
Proof.
have := translate_boolT_01 l.
case: l => /= H.
- move/eqP. rewrite maxr01 eq_sym -subr_eq subrr eq_sym subr_eq0.
  move/eqP; rewrite psumr_eqsize//.
  move => i //=.
  by move: (H _ _ _ (s i)); set a := [[s i]]_ _; lra.
- move/eqP.
  rewrite maxr01 eq_sym addrC -subr_eq subrr eq_sym oppr_eq0 powR_eq0 invr_eq0 => /andP [+ _].
  rewrite psumr_eq0//=; last by move=> i _; rewrite powR_ge0.
  move=> /allP h i.
  have h' := @pfsumr_eq0 R 'I_n setT (fun i => 1 - [[ s i ]]_Yager) finite_finset _ _ i.
  apply/eqP.
  rewrite eq_sym -subr_eq0 h'//; first by move=> j _; rewrite subr_ge0 (andP (H _ _ _ _)).2.
  apply/eqP. rewrite psumr_eq0//=; last by move=> j _; rewrite subr_ge0 (andP (H _ _ _ _)).2.
  apply/allP => /=j _.
  suff: (1 - [[s j]]_Yager) `^ p == 0.
    by rewrite powR_eq0 (@gt_eqF _ _ p 0) ?(lt_le_trans _ p1)//= andbT.
  by rewrite h// mem_index_enum.
- move/eqP.
  rewrite /minR => /bigmin_eqP/= h i.
  apply/eqP.
  rewrite eq_sym eq_le.
  rewrite ((andP (H _ _ _ _)).2) h //.
  exact: mem_index_enum.
- by move/prod1_01; apply => i; exact: H.
- move/eqP.
  rewrite /minR => /bigmin_eqP/= h i.
  apply/eqP.
  rewrite eq_sym eq_le ((andP (H _ _ _ _)).2) h //.
  exact: mem_index_enum.
- move/prod1_01; apply => i. exact: H.
Qed.

Lemma nary_inversion_mandE0 f1 f2 n (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  l <> Lukasiewicz -> l <> Yager -> [[ @ldl_mand R _ _ _ n s ]]_ l = 0 ->
   exists i, [[ s i ]]_ l = 0.
Proof.
have H := translate_boolT_01. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move => l1 l2; move/eqP. move: s.
  rewrite /minR.
  elim: n => [s|n ih s].
  + by rewrite big_ord0 oner_eq0.
  + rewrite big_ord_recl {1}/minr.
    case: ifPn => [_ /eqP ?|_ h1]; first by exists ord0.
    have /= [i h2] := (ih (s \o (lift ord0)) h1).
    by exists (lift ord0 i).
- move=> l1 l2 /eqP.
  rewrite prodf_seq_eq0 => /hasP[i _/= /eqP si0].
  by exists i; rewrite si0.
- move => l1 l2; move/eqP.
  rewrite /minR.
  move: s; elim: n => [s|n ih s].
  + by rewrite big_ord0 oner_eq0.
  + rewrite big_ord_recl {1}/minr.
    case: ifPn => [_ /eqP ?|_]; first by exists 0.
    by move/ih => [i i0]; exists (lift ord0 i).
- move=> l1 l2 /eqP.
  rewrite prodf_seq_eq0 => /hasP[e eEs/= /eqP e0].
  by exists e => //; rewrite e0.
Qed.

Lemma nary_inversion_morE1 f1 f2 n (Es : 'I_n -> expr (boolT_def f1 m_def f2)) :
  l <> Lukasiewicz -> l <> Yager -> [[ ldl_mor Es ]]_ l = 1 ->
    exists i, [[ Es i ]]_ l = 1.
Proof.
have H := translate_boolT_01 l. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move: Es; elim: n => [Es l0 l1|n ih Es l0 l1] /eqP; rewrite /maxR.
  + by rewrite big_ord0 eq_sym oner_eq0.
  + rewrite big_ord_recl {1}/maxr => /eqP.
    case: ifPn => [_|_ a1]; last by exists ord0.
    move/(ih _ l0 l1) => [i h].
    by exists (lift ord0 i).
- move: Es; elim: n => [Es l1 l2| n ih Es l1 l2] /eqP; rewrite /product_dl_prod.
  + by rewrite big_ord0 eq_sym oner_eq0.
  + rewrite big_ord_recl {1}/product_dl_mul.
    move/product_dl_mul_inv => [|||/eqP].
    * exact: H.
    * by apply: product_dl_mul_seq_01.
    * by exists ord0.
    * by move/eqP/(ih _ l1 l2) => [i h]; exists (lift ord0 i).
- move: Es; elim: n => [Es l1 l2 | n ih Es l1 l2] /eqP; rewrite /maxR.
  + by rewrite big_ord0 eq_sym oner_eq0.
  + rewrite big_ord_recl {1}/maxr.
    case: ifPn => [_|_] /eqP; last by exists ord0.
    move/(ih _ l1 l2) => [i h].
    by exists (lift ord0 i).
- move: Es; elim: n => [Es l1 l2 | n ih Es l1 l2] /eqP; rewrite /product_dl_prod.
  + by rewrite big_ord0 eq_sym oner_eq0.
  + rewrite big_ord_recl {1}/product_dl_mul.
    move/product_dl_mul_inv => [|||].
    * exact: H.
    * by apply: product_dl_mul_seq_01.
    * by exists ord0.
    * by move/(ih _ l1 l2) => [i h]; exists (lift ord0 i).
Qed.

Lemma nary_inversion_morE0 f1 f2 n (Es : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ ldl_mor Es ]]_ l = 0 -> forall i, [[ Es i ]]_ l = 0.
Proof.
have H := translate_boolT_01 l. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move/eqP; rewrite minr10 => /eqP.
  move=> /psumr_eq0P => h i.
  by apply: h => // j _; apply (andP (H _ _ _ _)).1.
- move/eqP; rewrite minr10 powR_eq0.
  move/andP => [].
  rewrite (@gt_eqF _ _ (p^-1)) ?invr_gt0//=.
  rewrite psumr_eq0=>[|i]; last by rewrite powR_ge0.
  move/allP => h _ i.
  apply/eqP.
  suff: ([[Es i]]_Yager == 0) && (p != 0).
    by move/andP=>[].
  rewrite -powR_eq0.
  exact/h/mem_index_enum.
- rewrite /maxR/product_dl_prod.
  move: Es; elim: n => [Es h|n ih Es h i]; first by case.
  have := h; rewrite big_ord_recl {1}/maxr.
  case: ifPn => // /[swap] ->; first by move: (H _ _ _ (Es ord0)); lra.
  rewrite -leNgt => bigle0.
  have /eqP : \big[maxr/0]_(i < n) [[Es (lift ord0 i)]]_Godel == 0.
    by rewrite eq_le bigle0 bigmax_idl le_max lexx.
  case: (unliftP ord0 i) => /= [j ->|-> _].
    by move/(ih (fun i => Es (lift ord0 i))).
  move: h => /eqP; rewrite eq_le => /andP [].
  move=> /bigmax_leP => [ [_ /=] + _ ]; move=> /(_ ord0) h.
  by apply/eqP; rewrite eq_le h//= (andP (H _ _ _ _)).1.
- rewrite /product_dl_prod.
  move: Es; elim: n => [Es h | n ih Es]; first by case.
  rewrite big_ord_recl => /eqP /product_dl_prod_inv0 h i.
  case: (unliftP ord0 i) => [/=j ->| ->].
  + apply/(ih (fun i => Es (lift ord0 i)))/(h _ _).2 => //.
    exact: product_dl_mul_seq_01.
  + apply/eqP; rewrite (h _ _).1//.
    exact: product_dl_mul_seq_01.
- rewrite /maxR/product_dl_prod.
  move: Es; elim: n => [Es h|n ih Es h i]; first by case.
  case: (unliftP ord0 i) => [j ->|->].
  + apply/(ih (fun i => Es (lift ord0 i))).
    apply/eqP. rewrite eq_le. apply/andP; split.
      apply/bigmax_leP; split => //; move => k.
      by move: h => /eqP; rewrite eq_le => /andP [] /bigmax_leP [_ /(_ (lift ord0 k)) +_].
    exact/bigmax_ge_id.
  + apply/eqP. rewrite eq_le. apply/andP; split.
      by move: h => /eqP; rewrite eq_le => /andP [] /bigmax_leP [_ /(_ ord0) +_]; apply.
    exact/(andP (H _ _ _ _)).1.
- rewrite /product_dl_prod.
  move: Es; elim: n => [Es h|n ih Es h i]; first by case.
  move: h; rewrite big_ord_recl=> /eqP/product_dl_prod_inv0 => h.
  case: (unliftP ord0 i) => [j ->|->].
  + apply/(ih (fun i => Es (lift ord0 i)))/(h _ _).2 => //.
    exact: product_dl_mul_seq_01.
  + apply/(h _ _).1 => //.
    exact: product_dl_mul_seq_01.
Qed.

Lemma inversion_implE1 f1 f2 (E1 E2 : expr (boolT_def impl_def f1 f2)) :
  l <> Lukasiewicz -> l <> Yager -> l <> Godel -> l <> product ->
  (*((l = GodelS) \/ (l = productS)) ->*)
  [[  E1 `=> E2 ]]_ l = 1 ->
     ([[ E1 ]]_ l == 0) || ([[ E2 ]]_ l == 1).
Proof.
case: l => //=; move => _ _ _ _.
- rewrite /maxr; case: ifP; move => h; move/eqP => he2; first by rewrite he2 orbT//=.
  have h' : 1 - [[E1]]_GodelS == 1 -> [[E1]]_GodelS == 0. intros; lra.
  by rewrite (h' he2) orTb.
- have H1 := translate_boolT_01 productS _ _ _ E1.
  have H2 := translate_boolT_01 productS _ _ _ E2.
  move/eqP => h.
  have h' : forall (a : R), 1 - a == 1 -> a == 0. intros; lra.
  apply h' in h.
  rewrite mulf_eq0 in h.
  by move/orP: h => [/eqP|/eqP]; move=> h; try apply subr0_eq in h;
  rewrite h eq_refl ?orTb ?orbT.
Qed.

Lemma inversion_implE0  f1 f2 (E1 E2 : expr (boolT_def impl_def f1 f2)) :
  l <> Lukasiewicz -> l <> Yager -> l <> Godel -> l <> product ->
  [[  E1 `=> E2 ]]_ l = 0 ->
     ([[ E1 ]]_ l == 1) && ([[ E2 ]]_ l == 0).
Proof.
case: l => //=; move =>  _ _ _ _.
- rewrite /maxr; case: ifP; move => h; move/eqP => he2.
  + rewrite he2 andbT. have H := translate_boolT_01 GodelS _ _ _ E1.
    exfalso.
    have h' : [[E2]]_GodelS == 0 ->
              1 - [[E1]]_GodelS < [[E2]]_GodelS ->
              0 <= [[E1]]_GodelS <= 1 -> False. intros. lra.
    apply (h' he2 h H).
  + move: he2. move /eqP => he2; apply subr0_eq in he2.
    rewrite he2 eq_refl andTb.
    have H := translate_boolT_01 GodelS _ _ _ E2.
    rewrite -he2 in h.
    have h' : (1 - 1 < [[E2]]_GodelS) = false ->
              0 <= [[E2]]_GodelS <= 1 ->
              [[E2]]_GodelS == 0. intros; lra.
    by rewrite (h' h H).
- move/eqP => h.
  have H1 := translate_boolT_01 productS _ _ _ E1.
  have H2 := translate_boolT_01 productS _ _ _ E2.
  have h' : forall (a : R), 1 - a == 0 -> a == 1. intros; lra.
  apply h' in h.
  have mul01 : forall (a b : R), 0 <=  a <= 1 -> 0 <= b <= 1 ->
                                 (1 - a) * b == 1 ->
                                 (b == 1) && (a == 0). intros; nra.
  by rewrite (mul01 _ _ H2 H1 h).
Qed.

Lemma nary_inversion_andE1 f1 f2 n (s : 'I_n -> (expr (boolT_def f1 f2 l_def))) dl :
  [[ ldl_and s ]]_ dl = 1 -> forall i, [[ s i ]]_ dl = 1.
Proof.
have /= H := translate_boolT_01 dl.
move/eqP.
rewrite /minR => /bigmin_eqP/= h i.
apply/eqP.
rewrite eq_sym eq_le.
rewrite ((andP (H _ _ _ _)).2) h //.
exact: mem_index_enum.
Qed.

Lemma nary_inversion_andE0 f1 f2 n (s : 'I_n -> (expr (boolT_def f1 f2 l_def))) :
   [[ ldl_and s ]]_ l = 0 -> exists i, ([[ s i ]]_ l == 0).
Proof.
have H := translate_boolT_01. move: H.
have p0 := lt_le_trans ltr01 p1.
move => /= H.
move/eqP.
rewrite /minR.
move: s; elim: n => [h|n ih s]; first by rewrite big_ord0 oner_eq0.
rewrite big_ord_recl {1}/minr.
case: ifPn => [_ ?|_]; first by exists ord0.
by move/ih => [i i0]; exists (lift ord0 i).
Qed.

Lemma nary_inversion_orE1 f1 f2 n (Es : 'I_n -> (expr (boolT_def f1 f2 l_def))) dl:
  [[ ldl_or Es ]]_ dl = 1 -> exists i, ([[ Es i ]]_ dl == 1) .
Proof.
have H := translate_boolT_01 dl. move: H.
have p0 := lt_le_trans ltr01 p1.
move => /= H.
move/eqP.
rewrite /maxR.
move: Es; elim: n => [Es|n ih Es]; first by rewrite big_ord0 eq_sym oner_eq0.
rewrite big_ord_recl {1}/maxr.
case: ifPn => [_|_ a1]; last by exists ord0.
move/ih => [i h].
by exists (lift ord0 i).
Qed.

Lemma nary_inversion_orE0 f1 f2 n (Es : 'I_n -> (expr (boolT_def f1 f2 l_def))) :
  [[ ldl_or Es ]]_ l = 0 -> forall i, [[ Es i ]]_ l = 0.
Proof.
have H := translate_boolT_01 l. move: H.
have p0 := lt_le_trans ltr01 p1.
 move =>/= H.
rewrite /maxR/product_dl_prod.
move: Es; elim: n => [Es h|n ih Es h i]; first by case.
move: h => /eqP. rewrite big_ord_recl eq_le => /andP[+_].
rewrite {1}bigmax_idl ge_max => /andP[h0].
rewrite ge_max => /andP[_ h].
case: (unliftP ord0 i) => /=[j ->|->].
- apply/(ih (fun i => Es (lift ord0 i))).
  apply/eqP; rewrite eq_le h/=.
  by apply/bigmax_geP; left.
by apply/eqP; rewrite eq_le h0 (andP (H _ _ _ _)).1.
Qed.

Definition b2R (b : bool) : R := (PeanoNat.Nat.b2n b)%:R.

Definition eq_x1 b (x : R) := if b then x = 1 else x < 1.

Lemma adequacy'_Luka (e : expr (boolT_def impl_def m_def l_def)) b :
  eq_x1 b ([[ e ]]_Lukasiewicz) -> [[ e ]]_B = b.
Proof.
rewrite /eq_x1.
dependent induction e  using expr_ind'.
- case: b0 => /=; case: b => //=.
  + by move => /eqP; rewrite eq_sym oner_eq0.
  + by rewrite ltxx.
- case: b. 
  + move/nary_inversion_andE1 => h.
    rewrite /=big_andE; apply/forallP => /=i.
    exact/H.
  + have := translate_boolT_01.
    have p0 := lt_le_trans ltr01 p1.
    move => /= H'.
    move/eqP.
    rewrite /minR.
    move: l0 H; elim: n => [h|n ih s].
    * rewrite big_ord0 lt_neqAle => _ /eqP/andP [hh _]. lra. 
    * rewrite big_ord_recl {1}/minr.
      case: ifPn => [h1 IH| h1 IH]. 
      - move => /eqP hh.
        have IHf := IH _ _ _ _ false hh. 
        rewrite big_ord_recl (IHf ord0)//=.
      - move => /eqP hh.
        have IHf := IH _ _ _ _ false.
        rewrite big_ord_recl. rewrite ih//= ?andbF ?hh//=.
   admit.
- case: b. 
  + move/(nary_inversion_orE1 _ _ _ _) => /=[i /eqP h].
    rewrite big_orE; apply/existsP; exists i => /=.
    exact/H.
  + admit.
- case: b; rewrite//= => eh.
  + have h0 : [[e]]_Lukasiewicz = 0. lra.
    rewrite Bool.negb_true_iff (IHe _ _ _ false) ?h0//=.
  + admit. (*also problematic*)



- case: b => /=. 
  + rewrite //=/minr; case: ifP.
    * by move => /[swap] => -> ; rewrite ltxx.
    *  move => e12 _.
       have H : [[e1]]_Lukasiewicz = [[e2]]_Lukasiewicz. admit.
       have /andP [_ ] := translate_boolT_01 Lukasiewicz _ _ _ e1.
       rewrite le_eqVlt => /orP [/eqP He1 | He1]. 
       - rewrite He1 in H. symmetry in H.
         by rewrite (IHe1 e1 _ _ true He1)//= (IHe2 e2 _ _ true H)//=.
       - by rewrite (IHe1 e1 _ _ false He1)//=.
  + rewrite //=/minr; case: ifPn.
    * move => h _. 
      have H : [[e1]]_Lukasiewicz > [[e2]]_Lukasiewicz. lra.
      have /andP [_ ] := translate_boolT_01 Lukasiewicz _ _ _ e1.
       rewrite le_eqVlt => /orP [/eqP He1 | He1]. rewrite He1 in H.
       - by rewrite Bool.implb_false_iff (IHe1 e1 _ _ true He1)//= (IHe2 e2 _ _ false H)//=.
       - admit. (*this is where the issue is - I don't think this is provable*)
    * rewrite ltxx//=.
Admitted.

Lemma bool_le1_luka (e : expr (boolT_def impl_def m_def l_def)) :
  [[e]]_Lukasiewicz < 1 -> [[e]]_B = false.
Proof.
dependent induction e using expr_ind'.
- admit.
- admit.
- admit.
-admit.
- rewrite /= /minr; case: ifPn . Abort.

Lemma bool_le1 (e : @expr R (boolT_def impl_def m_def l_def)) :
  ([[e]]_B <= 1)%N.
Proof.
dependent induction e using expr_ind'.
Admitted.

Lemma order_luka (e1 e2 : expr (boolT_def impl_def m_def l_def)) :
  [[e2]]_Lukasiewicz <= [[e1]]_Lukasiewicz -> (([[e2]]_B) <=([[e1]]_B))%N.
Proof.
dependent induction e1 using expr_ind'.
- case: b => /= h. by rewrite bool_le1.
  dependent induction e2 using expr_ind'.
  + case: b h => //=. lra.
  + rewrite//= big_andE. rewrite  H.
dependent induction e2 using expr_ind'.
- case: b; case: b0 => //=. lra.
- case: b H => /= H.
  + 



(*have /andP [_ ] := translate_boolT_01 Lukasiewicz _ _ _ e1.
rewrite le_eqVlt => /orP [/eqP He1 | He1].
- admit.
- have /andP [_ ] := translate_boolT_01 Lukasiewicz _ _ _ e2.
  rewrite le_eqVlt => /orP [/eqP He2 | He2].
  + admit.
  + *)

(*Lemma Luka_impl_adeq (e1 e2 : expr (boolT_def impl_def m_def l_def)) b:
  (forall e : expr (boolT_def impl_def m_def l_def), forall (b0 : bool),
      eq_x1 b0 ([[ e ]]_Lukasiewicz) -> [[ e ]]_B = b0) ->
  eq_x1 b ([[ e1 `=> e2 ]]_Lukasiewicz) -> [[ e1 `=> e2 ]]_B = b.
Proof.
rewrite /eq_x1 => h.
case: b => /=. 
+ rewrite //=/minr; case: ifP.
  * by move => /[swap] => -> ; rewrite ltxx.
  *  move => e12 _.
     have H : [[e1]]_Lukasiewicz = [[e2]]_Lukasiewicz. admit.
     have /andP [_ ] := translate_boolT_01 Lukasiewicz _ _ _ e1.
     rewrite le_eqVlt => /orP [/eqP He1 | He1]. 
     - rewrite He1 in H. symmetry in H.
       by rewrite (h e1 true He1) (h e2 true H)//=.
       by rewrite (h e1 false He1)//=.
+ rewrite //=/minr; case: ifP.
   * admit.
   * rewrite ltxx//=.
Admitted.*)


Lemma adequacy (e : expr (boolT_def impl_def m_def l_def)) b :
  [[ e ]]_ l = [[ ldl_bool _ _ _ _ b ]]_ l -> [[ e ]]_B = b.
Proof.
dependent induction e using expr_ind'.
- move: b b0 => [] [] //=; lra.
- rewrite [ [[ldl_bool _ _ _ _ b]]_l ]/=.
  move: b => [].
  + move/nary_inversion_andE1 => h.
    rewrite /=big_andE; apply/forallP => /=i.
    exact/H.
  + move/(nary_inversion_andE0 _ _ _ _) => [i /eqP h].
    rewrite /=big_andE; apply /forallP => /= /(_ i).
    by have /=/(_ _ _ h) -> := (H i (l0 i) _ _ false).
- rewrite [ [[ldl_bool _ _ _ _ b]]_l]/=.
  move: b => [].
  + move/(nary_inversion_orE1 _ _ _ _) => /=[i /eqP h].
    rewrite big_orE; apply/existsP; exists i => /=.
    exact/H.
  + move/nary_inversion_orE0 => h /=.
    rewrite big_orE; apply/existsPn => /= i.
    exact/Bool.negb_true_iff/H.
- move=>/=h; rewrite (IHe e erefl JMeq_refl (~~ b)) ?negbK//.
  move: h; case: l; rewrite//=;case: b => //=; try lra. admit. admit. admit. admit. 
  (*like impl, use the advanced adequacy for all*)
- rewrite [ [[ldl_bool _ _ _ _ b]]_l]/=.
  have := inversion_implE1. have := inversion_implE0.
  case: l IHe1 IHe2 => IHe1 IHe2 inv0 inv1.
  + have := adequacy'_Luka (e1 `=> e2) b.
    move: b => []; first by rewrite /eq_x1.
    rewrite /eq_x1 => H eq0. rewrite eq0 in H.
    by rewrite H.
  admit. admit. admit. (*need to do same as Luka*)
  + move: b => []; have temp : GodelS <> Lukasiewicz ->
    GodelS <> Yager ->
    GodelS <> Godel ->
    GodelS <> product by rewrite //=. 
    * move/(inv1); rewrite//= => //= H. apply H in temp; rewrite//=; move: temp. 
      move/orP => [/eqP H1 |/eqP H2].
      - rewrite implybE. rewrite //= in IHe1. rewrite (IHe1 e1 erefl JMeq_refl (false) H1).
        have tf : ~~ false = true. by rewrite//=.
        rewrite tf orTb//=.
      - rewrite implybE. rewrite //= in IHe2. 
        by rewrite (IHe2 e2 erefl JMeq_refl (true) H2) orbT.
    * move/(inv0); rewrite//= => //= H. apply H in temp; rewrite//=; move: temp.
      move/andP => [/eqP H1  /eqP H2].
      rewrite implybE Bool.orb_false_intro//=. 
      - rewrite //= in IHe1. by rewrite (IHe1 e1 erefl JMeq_refl (true) H1)//=.
      - rewrite //= in IHe2. by rewrite (IHe2 e2 erefl JMeq_refl (false) H2)//=.
  + move: b => []; have temp : productS <> Lukasiewicz ->
    productS <> Yager ->
    productS <> Godel ->
    productS <> product by rewrite //=. 
    * move/(inv1); rewrite//= => //= H. apply H in temp; rewrite//=; move: temp. 
      move/orP => [/eqP H1 |/eqP H2].
      - rewrite implybE. rewrite //= in IHe1. rewrite (IHe1 e1 erefl JMeq_refl (false) H1).
        have tf : ~~ false = true. by rewrite//=.
        rewrite tf orTb//=.
      - rewrite implybE. rewrite //= in IHe2. 
        by rewrite (IHe2 e2 erefl JMeq_refl (true) H2) orbT.
    * move/(inv0); rewrite//= => //= H. apply H in temp; rewrite//=; move: temp.
      move/andP => [/eqP H1  /eqP H2].
      rewrite implybE Bool.orb_false_intro//=. 
      - rewrite //= in IHe1. by rewrite (IHe1 e1 erefl JMeq_refl (true) H1)//=.
      - rewrite //= in IHe2. by rewrite (IHe2 e2 erefl JMeq_refl (false) H2)//=.
- rewrite [ [[ldl_bool _ _ _ _ b]]_l ]/=.
  move: b => [].
  + move/nary_inversion_mandE1 => h /=.
    rewrite big_andE; apply/forallP => /= i.
    exact/H.
  + have := nary_inversion_mandE0.
    case: l H => H inv0. 
    admit. admit. (*advanced adequacy*)
    * have H' : Godel <> Lukasiewicz -> Godel <> Yager by []. 
      move/(inv0); rewrite//= => //= h'. apply h' in H'; rewrite//=; move: H' => [i h]/=.
      rewrite big_andE; apply/forallPn => /=; exists i.
      exact/Bool.negb_true_iff/H.
    * have H' : product <> Lukasiewicz -> product <> Yager by []. 
      move/(inv0); rewrite//= => //= h'. apply h' in H'; rewrite//=; move: H' => [i h]/=.
      rewrite big_andE; apply/forallPn => /=; exists i.
      exact/Bool.negb_true_iff/H.
    * have H' : GodelS <> Lukasiewicz -> GodelS <> Yager by []. 
      move/(inv0); rewrite//= => //= h'. apply h' in H'; rewrite//=; move: H' => [i h]/=.
      rewrite big_andE; apply/forallPn => /=; exists i.
      exact/Bool.negb_true_iff/H.
    * have H' : productS <> Lukasiewicz -> productS <> Yager by []. 
      move/(inv0); rewrite//= => //= h'. apply h' in H'; rewrite//=; move: H' => [i h]/=.
      rewrite big_andE; apply/forallPn => /=; exists i.
      exact/Bool.negb_true_iff/H.
- rewrite [ [[ldl_bool _ _ _ _ b]]_l]/=.
  move: b => [].
  + have := nary_inversion_morE1.
    case: l H => H inv. 
    admit. admit. (*advanced adequacy*)
    * have H' : Godel <> Lukasiewicz -> Godel <> Yager by []. 
      move/(inv); rewrite//= => //= h'. apply h' in H'; rewrite//=; move: H' => [i h]/=.
      rewrite big_orE; apply/existsP => /=; exists i.
      exact/H.
    * have H' : product <> Lukasiewicz -> product <> Yager by []. 
      move/(inv); rewrite//= => //= h'. apply h' in H'; rewrite//=; move: H' => [i h]/=.
      rewrite big_orE; apply/existsP => /=; exists i.
      exact/H.
    * have H' : GodelS <> Lukasiewicz -> GodelS <> Yager by []. 
      move/(inv); rewrite//= => //= h'. apply h' in H'; rewrite//=; move: H' => [i h]/=.
      rewrite big_orE; apply/existsP => /=; exists i.
      exact/H.
    * have H' : productS <> Lukasiewicz -> productS <> Yager by []. 
      move/(inv); rewrite//= => //= h'. apply h' in H'; rewrite//=; move: H' => [i h]/=.
      rewrite big_orE; apply/existsP => /=; exists i.
      exact/H.
  + move/nary_inversion_morE0 => h/=.
    rewrite big_orE; apply/existsPn => i/=.
    exact/Bool.negb_true_iff/H.
- case: c; rewrite //=; rewrite -!translations_Real_coincide;
  set t1 := _ e1; set t2 := _ e2.
  + case: ifPn => [/eqP ->|e12eq].
    have [] := leP (-t2) t2 => /=; case: b; lra.
    rewrite /maxr.
    have ? : 0 < `|t1 + t2| by rewrite normr_gt0 addr_eq0.
    have ? : 0 < `|t1 + t2|^-1 by rewrite invr_gt0.
    case: b; repeat case: ifPn; [lra|lra| | |lra| |lra|]; rewrite -?leNgt.
    * by rewrite pmulr_llt0; lra.
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
      by rewrite eq_sym eqr_norml; lra.
  + case: ifP => [/eqP ->|e12eq].
    have [] := eqVneq (- t2) t2 => /=; case: b; lra.
    rewrite /maxr.
    case: b; case: ifPn; first by lra; rewrite -?leNgt.
    * move=> _ H.
      have : `|(t1 - t2) / (t1 + t2)| == 0.
        clear -H.
        simpl in *.
        lra.
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


(*Lemma adequacy (e : expr (boolT_def impl_def m_def l_def)) b :
  l <> Lukasiewicz -> l <> Yager -> l <> Godel -> l <> product ->
    [[ e ]]_ l = [[ ldl_bool _ _ _ _ b ]]_ l -> [[ e ]]_B = b.
Proof.
dependent induction e using expr_ind' => ll ly lg lp.
- move: b b0 => [] [] //=; lra.
- rewrite [ [[ldl_bool _ _ _ _ b]]_l ]/=.
  move: b => [].
  + move/nary_inversion_andE1 => h.
    rewrite /=big_andE; apply/forallP => /=i.
    exact/H.
  + move/(nary_inversion_andE0 _ _ _ _ ll ly) => [i /eqP h].
    rewrite /=big_andE; apply /forallP => /= /(_ i).
    by have /=/(_ _ _ h) -> := (H i (l0 i) _ _ false ll ly lg lp).
- rewrite [ [[ldl_bool _ _ _ _ b]]_l]/=.
  move: b => [].
  + move/(nary_inversion_orE1 _ _ _ _ ll ly) => /=[i /eqP h].
    rewrite big_orE; apply/existsP; exists i => /=.
    exact/H.
  + move/nary_inversion_orE0 => h /=.
    rewrite big_orE; apply/existsPn => /= i.
    exact/Bool.negb_true_iff/H.
- move=>/=h; rewrite (IHe e erefl JMeq_refl (~~ b) ll ly lg lp) ?negbK//.
  move: ll ly lg lp h; case: l; rewrite//=;case: b => //=; lra.
- rewrite [ [[ldl_bool _ _ _ _ b]]_l]/=.
  move: b => [].
  + move/(inversion_implE1 _ _ _ _ ll ly lg lp); rewrite//=; move/orP => [/eqP H1 |/eqP H2].
    * rewrite implybE. rewrite //= in IHe1. rewrite (IHe1 e1 erefl JMeq_refl (false) ll ly lg lp H1).
      have tf : ~~ false = true. by rewrite//=.
      rewrite tf orTb//=.
    * rewrite implybE. rewrite //= in IHe2. 
      by rewrite (IHe2 e2 erefl JMeq_refl (true) ll ly lg lp H2) orbT.
  + move/(inversion_implE0 _ _ _ _ ll ly lg lp); rewrite//=; move/andP => [/eqP H1  /eqP H2].
    rewrite implybE Bool.orb_false_intro//=. 
    * rewrite //= in IHe1. by rewrite (IHe1 e1 erefl JMeq_refl (true) ll ly lg lp H1)//=.
    * rewrite //= in IHe2. by rewrite (IHe2 e2 erefl JMeq_refl (false) ll ly lg lp H2)//=.
- rewrite [ [[ldl_bool _ _ _ _ b]]_l ]/=.
  move: b => [].
  + move/nary_inversion_mandE1 => h /=.
    rewrite big_andE; apply/forallP => /= i.
    exact/H.
  + move/(nary_inversion_mandE0 _ _ _ _ ll ly) => [i h]/=.
    rewrite big_andE; apply/forallPn => /=; exists i.
    exact/Bool.negb_true_iff/H.
- rewrite [ [[ldl_bool _ _ _ _ b]]_l]/=.
  move: b => [].
  + move/(nary_inversion_morE1 _ _ _ _ ll ly) => [i h]/=.
    rewrite big_orE; apply/existsP => /=; exists i.
    exact/H.
  + move/nary_inversion_morE0 => h/=.
    rewrite big_orE; apply/existsPn => i/=.
    exact/Bool.negb_true_iff/H.
- case: c; rewrite //=; rewrite -!translations_Real_coincide;
  set t1 := _ e1; set t2 := _ e2.
  + case: ifPn => [/eqP ->|e12eq].
    have [] := leP (-t2) t2 => /=; case: b; lra.
    rewrite /maxr.
    have ? : 0 < `|t1 + t2| by rewrite normr_gt0 addr_eq0.
    have ? : 0 < `|t1 + t2|^-1 by rewrite invr_gt0.
    case: b; repeat case: ifPn; [lra|lra| | |lra| |lra|]; rewrite -?leNgt.
    * by rewrite pmulr_llt0; lra.
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
      by rewrite eq_sym eqr_norml; lra.
  + case: ifP => [/eqP ->|e12eq].
    have [] := eqVneq (- t2) t2 => /=; case: b; lra.
    rewrite /maxr.
    case: b; case: ifPn; first by lra; rewrite -?leNgt.
    * move=> _ H.
      have : `|(t1 - t2) / (t1 + t2)| == 0.
        clear -H.
        simpl in *.
        lra.
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
Qed.*)

End translation_lemmas.

Definition product_and {R : fieldType} {n} (u : 'rV[R]_n) : R :=
  \prod_(i < n) u ``_ i.

Section shadow_lifting_product_and.
Context {R : realType}.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Variable M : nat.
Hypothesis M0 : M != 0%N.

Lemma shadowlifting_product_andE p : p > 0 ->
  forall i, ('d (@product_and R M.+1) '/d i) (const_mx p) = p ^+ M.
Proof.
move=> p0 i.
rewrite /partial.
have /cvg_lim : h^-1 * (product_and (const_mx p + h *: err_vec i) -
                        @product_and _ M.+1 (const_mx p))
       @[h --> (0:R)^'] --> p ^+ M.
  rewrite /product_and.
  have H (h : R) : h != 0 ->
      \prod_(x < M.+1) (const_mx p + h *: err_vec i) 0 x -
      \prod_(x < M.+1) const_mx (m:=M.+1) p 0 x = h * p ^+ M.
    move=> h0; rewrite [X in X - _](bigD1 i)//= !mxE eqxx mulr1.
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

Corollary shadow_lifting_product_and : shadow_lifting (@product_and R M.+1).
Proof. by move=> p p0 i; rewrite shadowlifting_product_andE// exprn_gt0. Qed.

End shadow_lifting_product_and.

From mathcomp Require Import perm.

Section Lukasiewicz_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Lukasiewicz_mandC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ldl_mand s]]_Lukasiewicz = [[ldl_mand (s \o pi)]]_Lukasiewicz.
Proof.
rewrite /=; congr maxr; congr +%R; congr +%R.
by rewrite (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma Lukasiewicz_mandC f1 f2 (e1 e2 : (expr (boolT_def f1 m_def f2))) :
  [[ e1 `** e2 ]]_Lukasiewicz = [[ e2 `** e1 ]]_Lukasiewicz.
Proof.
by rewrite /=!big_ord_recl !big_ord0 !tnthS !tnth0 !addr0 (addrC (_ e1)).
Qed.

Lemma Lukasiewicz_morC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ldl_mor s]]_Lukasiewicz = [[ldl_mor (s \o pi)]]_Lukasiewicz.
Proof.
rewrite /=; congr minr.
by rewrite (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma Lukasiewicz_morC f1 f2 (e1 e2 :(expr (boolT_def f1 m_def f2))) :
  [[ e1 `++ e2 ]]_Lukasiewicz = [[ e2 `++ e1 ]]_Lukasiewicz.
Proof.
by rewrite /=!big_ord_recl !big_ord0 !tnthS !tnth0 !addr0 addrC.
Qed.

Lemma Lukasiewicz_morA f1 f2 (e1 e2 e3 :  (expr (boolT_def f1 m_def f2))) :
  [[ (e1 `++ (e2 `++ e3)) ]]_Lukasiewicz = [[ ((e1 `++ e2) `++ e3) ]]_Lukasiewicz.
Proof.
have := translate_boolT_01 p p1 Lukasiewicz _ _ _ e1.
have := translate_boolT_01 p p1 Lukasiewicz _ _ _ e2.
have := translate_boolT_01 p p1 Lukasiewicz _ _ _ e3.
rewrite /=!big_ord_recl !big_ord0 !tnthS !tnth0/= !big_ord_recl !big_ord0 !tnthS !tnth0/= /minr.
repeat case: ifP; set a := [[_]]__; set b := [[_]]__; set c := [[_]]__; lra.
Qed.

Theorem Lukasiewicz_mandA f1 f2 (e1 e2 e3 :  (expr (boolT_def f1 m_def f2))) : (0 < p)%R ->
  [[ (e1 `** e2) `** e3]]_Lukasiewicz = [[ e1 `** (e2 `** e3) ]]_Lukasiewicz.
Proof.
have := translate_boolT_01 p p1 Lukasiewicz _ _ _ e1.
have := translate_boolT_01 p p1 Lukasiewicz _ _ _ e2.
have := translate_boolT_01 p p1 Lukasiewicz _ _ _ e3.
rewrite /= /maxR /minR /product_dl_prod !big_ord_recl !big_ord0 !tnthS !tnth0/= !big_ord_recl !big_ord0 !tnthS !tnth0.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
rewrite /maxr.
by repeat case: ifP; lra.
Qed.

Theorem Lukasiewicz_mand_unit f1 f2 (e :  (expr (boolT_def f1 m_def f2))) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_Lukasiewicz = [[ e ]]_Lukasiewicz.
Proof.
have /=h := translate_boolT_01 p p1 Lukasiewicz _ _ _ e.
rewrite /= !big_ord_recl big_ord0 !tnthS !tnth0 /= addr0 addrAC.
rewrite /maxr; case: ifP; move => he; lra.
Qed.

Theorem Lukasiewicz_mor_unit f1 f2 (e :  (expr (boolT_def f1 m_def f2))) :
  [[ e `++ (ldl_bool _ _ _ _ false) ]]_Lukasiewicz = [[ e ]]_Lukasiewicz.
Proof.
have := translate_boolT_01 p p1 Lukasiewicz _ _ _ e.
rewrite /= !big_ord_recl big_ord0 !addr0.
by rewrite/minr; case: ifP; intros; lra.
Qed.

Lemma Lukasiewicz_prelinearity (e1 e2 e3 : @expr R boolT_fuzzy) :
  [[(e1 `=> e2) `\/ (e2 `=> e1)]]_Lukasiewicz = [[ldl_bool  _ _ _ _ true]]_Lukasiewicz.
Proof.
have := translate_boolT_01 p p1 Lukasiewicz _ _ _ (e1 `=> e2).
have := translate_boolT_01 p p1 Lukasiewicz _ _ _ (e2 `=> e1).
rewrite//= /maxR !big_ord_recl big_ord0 tnthS !tnth0 //= /maxr /minr; repeat case: ifPn; intros; lra.
Qed.

Lemma Lukasiewicz_residuation (e1 e2 e3 : expr boolT_fuzzy) :
  [[e1 `** e2]]_Lukasiewicz <= [[ e3 ]]_Lukasiewicz <-> [[ e2 ]]_Lukasiewicz <= [[e1 `=> e3]]_Lukasiewicz.
Proof.
have h1 := translate_boolT_01 p p1 Lukasiewicz _ _ _ e1.
have h2 := translate_boolT_01 p p1 Lukasiewicz _ _ _ e2.
have h3 := translate_boolT_01 p p1 Lukasiewicz _ _ _ e3.
split; rewrite//= !big_ord_recl big_ord0 addr0 /minr/maxr; repeat case: ifP; intros; lra.
Qed.

Lemma Lukasiewicz_involution (e : expr boolT_fuzzy) :
  [[`~ (`~e)]]_Lukasiewicz = [[ e ]]_Lukasiewicz.
Proof. by rewrite//=; lra. Qed.


Lemma Lukasiewicz_demorgan_mand  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `** e2)]]_Lukasiewicz = [[(`~ e1) `++ (`~ e2)]]_Lukasiewicz.
Proof.
rewrite//= !big_ord_recl !big_ord0 !tnthS !tnth0 /= !addr0 /maxr /minr; repeat case: ifP; intros; lra.
Qed.

Lemma Lukasiewicz_demorgan_mor  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `++ e2)]]_Lukasiewicz = [[(`~ e1) `** (`~ e2)]]_Lukasiewicz.
Proof.
rewrite//= !big_ord_recl !big_ord0/= !addr0 /maxr /minr; repeat case: ifP; intros; lra.
Qed.

End Lukasiewicz_lemmas.

Section Yager_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Yager_mandC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ldl_mand s]]_Yager = [[ldl_mand (s \o pi)]]_Yager.
Proof.
rewrite /= (_ : \sum_(i < n) (1 - [[s i]]_Yager) `^ p = \sum_(i < n) (1 - [[s (pi i)]]_Yager) `^ p)//.
by rewrite (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma Yager_mandC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `** e2 ]]_Yager = [[ e2 `** e1 ]]_Yager.
Proof.
rewrite /= !big_ord_recl !big_ord0.
by rewrite /= addr0 addr0 (addrC (_ `^ _)).
Qed.

Lemma Yager_morC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ldl_mor s]]_Yager = [[ldl_mor (s \o pi)]]_Yager.
Proof.
rewrite /= (_ : \sum_(i < n) [[s i]]_Yager `^ p = \sum_(i < n) [[s (pi i)]]_Yager `^ p)//.
by rewrite (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma Yager_morC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_Yager = [[ e2 `++ e1 ]]_Yager.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0.
by rewrite /= addr0 addr0 (addrC (_ `^ _)).
Qed.

Lemma Yager_morA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) :
  [[ (e1 `++ (e2 `++ e3)) ]]_Yager = [[ ((e1 `++ e2) `++ e3) ]]_Yager.
Proof.
have p0 : 0 < p by rewrite (lt_le_trans ltr01).
have ? : p != 0 by exact: lt0r_neq0.
have := translate_boolT_01 p p1 Yager _ _ _  e1.
have := translate_boolT_01 p p1 Yager _ _ _ e2.
have := translate_boolT_01 p p1 Yager _ _ _ e3.
rewrite /= /maxR /minR /product_dl_prod !big_ord_recl !big_ord0 !tnthS !tnth0/= !big_ord_recl !big_ord0 !tnthS !tnth0/=.
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

Theorem Yager_mandA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) : (0 < p) ->
  [[ e1 `** (e2 `** e3)]]_Yager = [[ (e1 `** e2) `** e3 ]]_Yager.
Proof.
move=> p0. symmetry.
have pneq0 : p != 0 by exact: lt0r_neq0.
have := translate_boolT_01 p p1 Yager _ _ _ e1.
have := translate_boolT_01 p p1 Yager _ _ _ e2.
have := translate_boolT_01 p p1 Yager _ _ _ e3.
rewrite /= /maxR /minR /product_dl_prod !big_ord_recl !big_ord0 !tnthS !tnth0/= !big_ord_recl !big_ord0 !tnthS !tnth0.
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
  by rewrite -!powRrM !mulVf// powR1 powRr1// !nnegrE; apply => //; exact: powR_ge0.
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

Theorem Yager_mand_unit f1 f2 (e :  (expr (boolT_def f1 m_def f2))) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_Yager = [[ e ]]_Yager.
Proof.
have h01 := translate_boolT_01 p p1 Yager _ _ _ e.
rewrite /= !big_ord_recl big_ord0 addr0.
have p_nq : forall (x : R), 1 <= x -> x != 0 by intros; lra.
rewrite subrr powR0 ?p_nq//=.
rewrite addr0 -powRrM divff//= ?powRr1 ?p_nq//=; try lra.
rewrite /maxr; case: ifP; move => hy; lra.
Qed.

Theorem Yager_mor_unit f1 f2 (e :  (expr (boolT_def f1 m_def f2))) :
  [[ e `++ (ldl_bool _ _ _ _ false) ]]_Yager = [[ e ]]_Yager.
Proof.
have h01 := translate_boolT_01 p p1 Yager _ _ _ e.
rewrite /= !big_ord_recl big_ord0 addr0.
have p_nq : forall (x : R), 1 <= x -> x != 0 by intros; lra.
rewrite powR0 ?addr0 ?p_nq//=.
rewrite -powRrM divff//= ?powRr1 ?p_nq//=; try lra.
rewrite /minr; case: ifP; move => hy; lra.
Qed.

Lemma Yager_residuation (e1 e2 e3 : expr boolT_fuzzy) : (0 < p) ->
  [[e1 `** e2]]_Yager <= [[ e3 ]]_Yager <-> [[ e2 ]]_Yager <= [[e1 `=> e3]]_Yager.
Proof.
move => p0.
have pneq0 : p != 0 by exact: lt0r_neq0.
have := translate_boolT_01 p p1 Yager _ _ _ e1.
have := translate_boolT_01 p p1 Yager _ _ _ e2.
have := translate_boolT_01 p p1 Yager _ _ _ e3.
have powRpinv : 1 = 1 `^ p^-1.
  by rewrite powR1.
have powRgt1 : forall x, 0 <= x -> 1 < x `^ p^-1 -> 1 < x.
  move=> x x0; rewrite {1}powRpinv.
  move/(@gt0_ltr_powR _ p p0).
  by rewrite -!powRrM !mulVf// powR1 powRr1// !nnegrE; apply => //; exact: powR_ge0.
have powRselfNx : forall x, 0 <= x -> (x `^ p) `^ p^-1 = x.
  move => x x0. rewrite -powRrM divff ?powRr1//=.
have powRgt : forall x y, 0 <= x -> 0 <= y -> y `^ p <= x -> y <= x `^ p^-1.
  move=> x y x0 y0 hp.
  have h := @ge0_ler_powR  _ (p^-1) _ (y `^ p) x  .
  rewrite -(powRselfNx y)//=. rewrite h ?nnegrE ?powR_ge0//=.   
  rewrite -div1r divr_ge0//=. lra.
have powRle1 : forall x, 0 <= x -> x `^ p^-1 <= 1 -> x <= 1.
  move=> x x0; rewrite {1}powRpinv.
  move/(@ge0_ler_powR _ p (ltW p0)).
  by rewrite -!powRrM !mulVf// powR1 powRr1//; apply; rewrite nnegrE ?powR_ge0.
have powRselfxN : forall x, 0 <= x -> (x `^ p^-1) `^ p = x.
  move => x x0. rewrite -powRrM mulVf ?powRr1//=. 
have powRgtxy : forall x y, 0 <= x -> 0 <= y -> y <= x `^ p^-1 -> y `^ p <= x.
  move=> x y x0 y0 hp.
  have h := @ge0_ler_powR  _ p (ltW p0) y (x `^ p^-1) .
  rewrite -(powRselfxN x)//=. rewrite h ?nnegrE//=.
  by rewrite powR_ge0.
have powRge1 : forall x y, 0 <= x -> 0 <= y  -> x <= y `^ p -> x `^ p^-1 <= y .
  move=> x y x0 y0 hp.
  have h := @ge0_ler_powR  _ (p^-1) _ (x) (y `^ p).
  rewrite -(powRselfNx y)//=. rewrite h ?nnegrE//=.
  - by rewrite invr_ge0 (ltW p0).
  - by rewrite (le_trans x0 hp).
rewrite//= !big_ord_recl big_ord0 tnthS !tnth0 !addr0 //= /maxr/minr.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
split; case: ifP; case: ifP; rewrite//=; try lra.
- move => /negP/negP h1 h2 _. rewrite ltNge Bool.negb_involutive in h1. 
  rewrite subr_lt0 //= in h2. apply powRgt1 in h2.
  + rewrite lerBrDl -(lerBrDr _ _ t2).
    rewrite powRge1//=. 
    * have he12 : 1 - t3 >= 1 - t1 by lra.
        rewrite subr_ge0; apply ge0_ler_powR; rewrite ?nnegrE//=; lra. 
    * lra.
    * rewrite lerBlDl. move /ltW in h2.
      have H' : 0 <= (1 - t3) <= 1. lra.
      apply (pow_le01 _ p p0) in H'. move/andP in H'. destruct H' as [_ H'].
      by apply (le_trans H'  h2).
    * rewrite addr_ge0 ?powR_ge0//=.
- move => /negP/negP h1 /negP/negP h2 h3. 
  rewrite ltNge Bool.negb_involutive in h1.
  rewrite ltNge Bool.negb_involutive in h2.
  rewrite lerBrDl -(lerBrDr _ _ t2).
  rewrite powRge1//=.
  * have he12 : 1 - t3 >= 1 - t1 by lra.
    rewrite subr_ge0; apply ge0_ler_powR; rewrite ?nnegrE//=; lra. 
  * lra.
  * rewrite subr_ge0 in h2. apply (powRle1 _) in h2; last by rewrite addr_ge0 ?powR_ge0//=.
    rewrite lerBlDr -(lerBlDl _ t3) in h3. apply powRgtxy in h3.
    + by rewrite lerBlDl h3.
    + by rewrite addr_ge0 ?powR_ge0//=.
    + lra.
- move => /negP/negP h1 h2 h3. 
  rewrite ltNge Bool.negb_involutive in h1.
  rewrite lerBlDr -(lerBlDl _ t3).
  rewrite powRgt//=.
  + by rewrite addr_ge0 ?powR_ge0//=.
  + lra.
  + have he12 : 1 - t1 >= 1 - t3 by lra.
    apply (ge0_ler_powR (ltW p0)) in he12; rewrite ?nnegrE//=.
    * have HH : forall (a b c : R), a <= b -> b <= c -> a <= c. intros; lra.
      rewrite (HH _ _ _ he12)//=. 
      by rewrite lerDl powR_ge0.
    * lra.
    * lra.
- move => /negP/negP h1 /negP/negP h2 h3.
  rewrite !ltNge !Bool.negb_involutive in h1 h2.
  rewrite lerBlDr -(lerBlDl _ t3).
  rewrite powRgt//=.
  + by rewrite addr_ge0 ?powR_ge0//=.
  + lra.
  + rewrite lerBrDl -(lerBrDr _ _ t2) in  h3.
    have powR' : forall x y, 0 <= x -> 0 <= y  -> x `^ p^-1 <= y -> x <= y `^ p .
      move=> x y x0 y0 hp.
      have h := @ge0_ler_powR  _ (p) _ (x `^ p^-1) (y).
      rewrite -(powRselfxN x)//=. rewrite h ?nnegrE//=.
    - by rewrite (ltW p0).
    - by rewrite powR_ge0.
    apply powR' in h3.
    * by rewrite lerBlDl in h3.
    * have he12 : 1 - t3 >= 1 - t1 by lra.
      apply (ge0_ler_powR (ltW p0)) in he12; rewrite ?nnegrE//=; lra.
    * lra.
Qed.

Lemma Yager_involution (e : expr boolT_fuzzy) :
  [[`~ (`~e)]]_Yager = [[ e ]]_Yager.
Proof. by rewrite//=; lra. Qed.

Lemma Yager_demorgan_mand  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `** e2)]]_Yager = [[(`~ e1) `++ (`~ e2)]]_Yager.
Proof.
rewrite//= !big_ord_recl !big_ord0 !tnthS !tnth0/= !addr0 /maxr /minr; repeat case: ifP; intros; lra.
Qed.

Lemma Yager_demorgan_mor  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `++ e2)]]_Yager = [[(`~ e1) `** (`~ e2)]]_Yager.
Proof.
have oneone (x : R) : (1 - (1 - x))%R = x by lra.
rewrite//= !big_ord_recl !big_ord0 !tnthS !tnth0 !addr0 /maxr /minr/= !oneone; repeat case: ifP; lra.
Qed.

End Yager_lemmas.

Section Godel_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Godel_mandI f1 f2 (e : expr (boolT_def f1 m_def f2)) : [[ e `** e ]]_Godel = [[ e ]]_Godel.
Proof.
rewrite /=/minR !big_ord_recl !big_ord0 /= !tnthS !tnth0.
have := translate_boolT_01 p p1 Godel _ _ _ e.
set t1 := _ e.
move => h.
rewrite /=/minr; repeat case: ifP; lra.
Qed.

Lemma Godel_morI f1 f2 (e : expr (boolT_def f1 m_def f2)) : [[ e `++ e ]]_Godel = [[ e ]]_Godel.
Proof.
rewrite /= /maxR !big_ord_recl big_ord0.
have /max_idPl -> : 0 <= [[ e ]]_Godel.
  by have /andP[] := translate_boolT_01 p p1 Godel _ _ _ e.
by rewrite maxxx.
Qed.

Lemma Godel_mandC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ldl_mand s]]_Godel = [[ldl_mand (s \o pi)]]_Godel.
Proof.
by rewrite /= /minR (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma Godel_mandC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `** e2 ]]_Godel = [[ e2 `** e1 ]]_Godel.
Proof.
rewrite /=/minR !big_ord_recl !big_ord0/= !tnthS !tnth0.
by rewrite /=/minr; repeat case: ifP; lra.
Qed.

Lemma Godel_morC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ldl_mor s]]_Godel = [[ldl_mor (s \o pi)]]_Godel.
Proof.
by rewrite /= /maxR (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma Godel_morC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_Godel = [[ e2 `++ e1 ]]_Godel.
Proof.
rewrite /=  /maxR !big_ord_recl !big_ord0.
by rewrite /= /maxr; repeat case: ifP; lra.
Qed.

Lemma Godel_morA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) :
  [[ (e1 `++ (e2 `++ e3)) ]]_Godel = [[ ((e1 `++ e2) `++ e3) ]]_Godel.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0 /= !tnthS !tnth0/= /maxR !big_ord_recl !big_ord0 !tnthS !tnth0/=/maxr.
repeat case: ifPn => //; lra.
Qed.

Theorem Godel_mandA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) : (0 < p) ->
  [[ (e1 `** e2) `** e3]]_Godel = [[ e1 `** (e2 `** e3) ]]_Godel.
Proof.
rewrite /= /minR !big_ord_recl !big_ord0/=/minR !big_ord_recl !big_ord0 !tnthS !tnth0.
have := translate_boolT_01 p p1 Godel _ _ _ e1.
have := translate_boolT_01 p p1 Godel _ _ _ e2.
have := translate_boolT_01 p p1 Godel _ _ _ e3.
set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
move => h1 h2 h3 p0.
rewrite /minr.
repeat case: ifPn => //; lra.
Qed.

Theorem Godel_mand_unit f1 f2 (e :  (expr (boolT_def f1 m_def f2))) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_Godel = [[ e ]]_Godel.
Proof.
have := translate_boolT_01 p p1 Godel _ _ _ e.
rewrite//= /minR !big_ord_recl !big_ord0/= !tnth0.
rewrite /minr; repeat case: ifP; intros; lra.
Qed.

Theorem Godel_mor_unit f1 f2 (e :  (expr (boolT_def f1 m_def f2))) :
  [[ e `++ (ldl_bool _ _ _ _ false) ]]_Godel = [[ e ]]_Godel.
Proof.
have := translate_boolT_01 p p1 Godel _ _ _ e.
rewrite//= /maxR !big_ord_recl !big_ord0/= !tnth0.
rewrite /maxr; repeat case: ifP; intros; lra.
Qed.

Lemma Godel_prelinearity (e1 e2 e3 : @expr R boolT_fuzzy) :
  [[(e1 `=> e2) `\/ (e2 `=> e1)]]_Godel = [[ldl_bool  _ _ _ _ true]]_Godel.
Proof.
have := translate_boolT_01 p p1 Godel _ _ _ e1.
have := translate_boolT_01 p p1 Godel _ _ _ e2.
rewrite//=/maxR; rewrite !big_ord_recl big_ord0 tnthS !tnth0//= /maxr; repeat case: ifP; intros; lra.
Qed.

Lemma Godel_residuation (e1 e2 e3 : expr boolT_fuzzy) :
  [[e1 `** e2]]_Godel <= [[ e3 ]]_Godel <-> [[ e2 ]]_Godel <= [[e1 `=> e3]]_Godel.
Proof.
have := translate_boolT_01 p p1 Godel _ _ _ e1.
have := translate_boolT_01 p p1 Godel _ _ _ e2.
split; rewrite//=/minR; rewrite !big_ord_recl big_ord0 /minr; repeat case: ifP; intros; try lra.
Qed.

Lemma Godel_demorgan_mand  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `** e2)]]_Godel = [[(`~ e1) `++ (`~ e2)]]_Godel.
Proof.
have := translate_boolT_01 p p1 Godel _ _ _ e1.
have := translate_boolT_01 p p1 Godel _ _ _ e2.
rewrite//= /minR /maxR !big_ord_recl !big_ord0 !tnthS !tnth0/= /maxr /minr; repeat case: ifP; lra.
Qed.

Lemma Godel_demorgan_mor  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `++ e2)]]_Godel = [[(`~ e1) `** (`~ e2)]]_Godel.
Proof.
have := translate_boolT_01 p p1 Godel _ _ _ e1.
have := translate_boolT_01 p p1 Godel _ _ _ e2.
rewrite//= /minR /maxR !big_ord_recl !big_ord0 !tnthS !tnth0/= /maxr /minr; repeat case: ifP; lra.
Qed.

End Godel_lemmas.

Section product_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma product_mandC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ldl_mand s]]_Godel = [[ldl_mand (s \o pi)]]_Godel.
Proof.
by rewrite /= /minR (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma product_mandC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `** e2 ]]_product = [[ e2 `** e1 ]]_product.
Proof.
by rewrite /= !big_ord_recl !big_ord0 /= mulr1 mulr1 mulrC.
Qed.

Lemma product_morC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  [[ldl_mor s]]_Godel = [[ldl_mor (s \o pi)]]_Godel.
Proof.
by rewrite /= /maxR (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma product_morC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_product = [[ e2 `++ e1 ]]_product.
Proof.
rewrite /= /maxR/product_dl_prod !big_ord_recl !big_ord0.
by rewrite /=/product_dl_mul addr0 addr0 mulr0 mulr0 subr0 subr0 mulrC -(addrC (_ e2)).
Qed.

Lemma product_morA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) :
  [[ (e1 `++ (e2 `++ e3)) ]]_product = [[ ((e1 `++ e2) `++ e3) ]]_product.
Proof.
rewrite /= /product_dl_prod !big_ord_recl !big_ord0 !tnthS/= !tnth0 /product_dl_prod !big_ord_recl !big_ord0 !tnthS/= !tnth0.
rewrite /product_dl_mul !addr0 !mulr0 !subr0.
lra.
Qed.

Theorem product_mandA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) : 0 < p ->
  [[ (e1 `** e2) `** e3]]_product = [[ e1 `** (e2 `** e3) ]]_product.
Proof.
rewrite /= /maxR /minR /product_dl_prod.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
rewrite !big_ord_recl !big_ord0 !tnthS !tnth0/= !big_ord_recl !big_ord0 !tnthS !tnth0.
lra.
Qed.

Theorem product_mand_unit f1 f2 (e :  (expr (boolT_def f1 m_def f2))) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_product = [[ e ]]_product.
Proof. by rewrite /= !big_ord_recl big_ord0 !mulr1. Qed.

Lemma product_prelinearity (e1 e2 e3 : @expr R boolT_fuzzy) :
  [[(e1 `=> e2) `\/ (e2 `=> e1)]]_product = [[ldl_bool  _ _ _ _ true]]_product.
Proof.
have h1 := translate_boolT_01 p p1 product _ _ _ e1.
have h2 := translate_boolT_01 p p1 product _ _ _ e2.
rewrite//= /maxR !big_ord_recl big_ord0 tnthS !tnth0//=.
rewrite /maxr; repeat case: ifP; intros; try nra.
- have : 0 < [[e2]]_product \/ 0 = [[e2]]_product by lra.
  move => [h | h]. 
  + have inv_pos : 0 < ([[e2]]_product)^-1.
    by rewrite invr_gt0 h//=.
    have H : 1 < [[e1]]_product / [[e2]]_product -> 
             [[e2]]_product < [[e1]]_product * ([[e2]]_product / [[e2]]_product). intros; nra.
    apply H in i0.
    rewrite divff in i0; nra.
  + rewrite -h in i; nra.
- have : 0 < [[e1]]_product \/ 0 = [[e1]]_product by lra.
  move => [h | h]. 
  + have inv_pos : 0 < ([[e1]]_product)^-1.
    by rewrite invr_gt0 h//=.
    have H : ([[e2]]_product / [[e1]]_product < 1) = false -> 
             [[e2]]_product * ([[e1]]_product / [[e1]]_product) >= [[e1]]_product. intros; nra.
    apply H in n1.
    rewrite divff in n1; nra.
  + rewrite -h in i; nra.
Qed.

Lemma product_residuation (e1 e2 e3 : expr boolT_fuzzy) :
  [[e1 `** e2]]_product <= [[ e3 ]]_product <-> [[ e2 ]]_product <= [[e1 `=> e3]]_product.
Proof.
have := translate_boolT_01 p p1 product _ _ _ e1.
have := translate_boolT_01 p p1 product _ _ _ e2.
have := translate_boolT_01 p p1 product _ _ _ e3.
split; rewrite//= !big_ord_recl big_ord0 !tnthS !tnth0 mulr1 /maxr/minr; case: ifP; try nra.
- move => h1 h2. 
  have : [[e1]]_product = 0 \/ [[e1]]_product > 0 by lra.
  move => [h|h]; first by rewrite h in h1; lra.
  have inv_pos : 0 < ([[e1]]_product)^-1.
    by rewrite invr_gt0 h//=.
  have HH := (@ler_pM _ _ _ ([[e1]]_product)^-1 ([[e1]]_product)^-1 _ _ h2).
  rewrite mulrC//= in HH.
  have e21 : [[e1]]_product / [[e1]]_product = 1 by rewrite mulfV//=; lra.
  rewrite -(mulr1 ([[e2]]_product)) -e21 mulrA.
  apply HH; try nra.
- move => h1 h2. 
  have : [[e1]]_product = 0 \/ [[e1]]_product > 0 by lra.
  move => [h|h]; first by rewrite h in h1; lra.
    have inv_pos : 0 < ([[e1]]_product)^-1.
    by rewrite invr_gt0 h//=.
  have HH := (@ler_pM _ _ _ ([[e1]]_product) ([[e1]]_product) _ _ h2).
  rewrite mulrC//= in HH.
  have e21 : [[e1]]_product / [[e1]]_product = 1 by rewrite mulfV//=; lra.
  rewrite -(mulr1 ([[e3]]_product)) -e21 mulrA. nra.
Qed.

Lemma product_demorgan_mand  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `** e2)]]_product = [[(`~ e1) `++ (`~ e2)]]_product.
Proof.
have ? := translate_boolT_01 p p1 product _ _ _ e1.
have ? := translate_boolT_01 p p1 product _ _ _ e2.
rewrite//=/product_dl_prod /product_dl_mul !big_ord_recl !big_ord0 !tnthS !tnth0.
case: ifP;
rewrite !mulr1 !mulr0 !addr0 !subr0 ?mulr0 ?mul0r ?addr0 ?add0r ?subr0 ?mulr1 ?oppr0 => h1/=.
all: repeat case: ifP => ?; nra.
Qed.

Lemma product_demorgan_mor  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `++ e2)]]_product = [[(`~ e1) `** (`~ e2)]]_product.
Proof.
have ? := translate_boolT_01 p p1 product _ _ _ e1.
have ? := translate_boolT_01 p p1 product _ _ _ e2.
rewrite//=/product_dl_prod /product_dl_mul !big_ord_recl !big_ord0.  
case: ifP; rewrite !mulr1 !mulr0 !addr0 !subr0 ?mulr0 ?mul0r ?addr0 ?add0r ?subr0 ?mulr1 ?oppr0 => h1/=.
all: repeat case: ifP => /=; nra.
Qed.

End product_lemmas.

Section lattice_fuzzy_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.
Hypothesis p1 : 1 <= p.
Variable dl : DL.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma fuzzy_landI f1 f2 (e : expr (boolT_def f1 f2 l_def)) : [[ e `/\ e ]]_ dl = [[ e ]]_dl.
Proof.
rewrite /=/minR !big_ord_recl !big_ord0 !tnthS !tnth0.
have := translate_boolT_01 p p1 dl _ _ _ e.
set t1 := _ e.
move => h.
rewrite /=/minr; repeat case: ifP; lra.
Qed.


Lemma fuzzy_lorI f1 f2 (e : expr (boolT_def f1 f2 l_def)) : [[ e `\/ e ]]_dl = [[ e ]]_dl.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0 !tnthS !tnth0.
have /max_idPl -> : 0 <= [[ e ]]_ dl.
  by have /andP[] := translate_boolT_01 p p1 dl _ _ _ e.
by rewrite maxxx.
Qed.

Lemma fuzzy_andC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 f2 l_def))) :
  [[ldl_and s]]_ dl = [[ldl_and (s \o pi)]]_ dl.
Proof.
by rewrite /= /minR (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma fuzzy_andC f1 f2 (e1 e2 : expr (boolT_def f1 f2 l_def)) :
  [[ e1 `/\ e2 ]]_ dl = [[ e2 `/\ e1 ]]_ dl.
Proof.
rewrite /=/minR !big_ord_recl !big_ord0 !tnthS !tnth0.
by rewrite /=/minr; repeat case: ifP; lra.
Qed.

Lemma fuzzy_orC_nary f1 f2 n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def f1 f2 l_def))) :
  [[ldl_or s]]_ dl = [[ldl_or (s \o pi)]]_ dl.
Proof.
by rewrite /= /maxR (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma fuzzy_orC f1 f2 (e1 e2 : expr (boolT_def f1 f2 l_def)) :
  [[ e1 `\/ e2 ]]_ dl = [[ e2 `\/ e1 ]]_ dl.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0.
rewrite /=/maxr; repeat case: ifP; lra.
Qed.

Lemma fuzzy_orA f1 f2 (e1 e2 e3 : expr (boolT_def f1 f2 l_def)) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_ dl = [[ ((e1 `\/ e2) `\/ e3) ]]_ dl.
Proof.
rewrite /= /maxR !big_ord_recl !big_ord0 !tnthS !tnth0 /=/maxR !big_ord_recl !big_ord0 !tnthS !tnth0 /maxr.
by repeat case: ifPn => //; lra.
Qed.

Theorem fuzzy_andA f1 f2 (e1 e2 e3 : expr (boolT_def f1 f2 l_def)) : (0 < p) ->
  [[ (e1 `/\ e2) `/\ e3]]_ dl = [[ e1 `/\ (e2 `/\ e3) ]]_ dl.
Proof.
rewrite /= /minR !big_ord_recl !big_ord0 /=/minR !big_ord_recl !big_ord0 !tnthS !tnth0.
have := translate_boolT_01 p p1 dl _ _ _ e1.
have := translate_boolT_01 p p1 dl _ _ _ e2.
have := translate_boolT_01 p p1 dl _ _ _ e3.
set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
move => h1 h2 h3 p0.
rewrite /minr.
by repeat case: ifPn => //; lra.
Qed.

Lemma fuzzy_and_distr (e1 e2 e3 : expr boolT_fuzzy) :
  [[ e1 `/\ (e2 `\/ e3)]]_ dl = [[ (e1 `/\ e2) `\/ (e1 `/\ e3)]]_ dl.
Proof.
rewrite//= /minR/maxR !big_ord_recl !big_ord0/= /minR/maxR !big_ord_recl !big_ord0 !tnthS !tnth0/=.
have e101 := translate_boolT_01 _ p1 dl _ _ _ e1.
have e201 := translate_boolT_01 _ p1 dl _ _ _ e2.
have e301 := translate_boolT_01 _ p1 dl _ _ _ e3.
(*Time rewrite /minr /maxr; repeat case: ifP => //; intros; try lra.
Finished transaction in 205.419 secs (204.099u,1.173s) (successful)*)
rewrite [in RHS]maxA.
rewrite -(min_maxr ([[e1]]_dl)).
rewrite -(min_maxl _ _ 1).
Time rewrite /minr /maxr; repeat case: ifP => //; lra.
(* Finished transaction in 17.673 secs (17.434u,0.22s) (successful) *)
Qed.

Lemma fuzzy_and_distr2 (e1 e2 e3 : expr boolT_fuzzy) :
  [[ e1 `\/ (e2 `/\ e3)]]_ dl = [[ (e1 `\/ e2) `/\ (e1 `\/ e3)]]_ dl.
Proof.
rewrite//= /minR/maxR !big_ord_recl !big_ord0/= /minR/maxR !big_ord_recl !big_ord0 !tnthS !tnth0/=.
have e101 := translate_boolT_01 _ p1 dl _ _ _ e1.
have e201 := translate_boolT_01 _ p1 dl _ _ _ e2.
have e301 := translate_boolT_01 _ p1 dl _ _ _ e3.
(*Time rewrite /minr /maxr; repeat case: ifP; intros; try lra. <- too long *)
rewrite [in RHS]minA.
rewrite -(max_minr ([[e1]]_dl)).
rewrite -(max_minl _ _ 0).
Time rewrite /minr /maxr; repeat case: ifP => //; lra.
(* Finished transaction in 18.3 secs (17.851u,0.361s) (successful) *)
Qed.

Lemma fuzzy_and_abs (e1 e2 : expr boolT_fuzzy) :
  [[ e1 `/\ (e1 `\/ e2)]]_ dl = [[ e1 ]]_ dl.
Proof.
rewrite//=/minR/maxR !big_ord_recl !big_ord0 !tnth0/=/maxR !big_ord_recl !big_ord0 !tnthS !tnth0.
have := translate_boolT_01 p p1 dl _ _ _ e1.
have := translate_boolT_01 p p1 dl _ _ _ e2.
by rewrite /minr /maxr; repeat case: ifP; intros; try lra.
Qed.

Lemma fuzzy_or_abs (e1 e2 : expr boolT_fuzzy) :
  [[ e1 `\/ (e1 `/\ e2)]]_ dl = [[ e1 ]]_ dl.
Proof.
rewrite//=/minR/maxR !big_ord_recl !big_ord0 !tnthS !tnth0/=/minR !big_ord_recl big_ord0/= !tnthS !tnth0/=.
have := translate_boolT_01 p p1 dl _ _ _ e1.
have := translate_boolT_01 p p1 dl _ _ _ e2.
by rewrite /minr /maxr; repeat case: ifP; intros; try lra.
Qed.

Lemma fuzzy_demorgan_mor  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `\/ e2)]]_ dl = [[(`~ e1) `/\ (`~ e2)]]_ dl.
Proof.
case: dl; rewrite//= /minR /maxR !big_ord_recl !big_ord0 !tnthS !tnth0/= /minr /maxr;
repeat case: ifP; intros; lra.
Qed.

Lemma fuzzy_demorgan_and  (e1 e2 : expr boolT_fuzzy) :
  [[`~ (e1 `/\ e2)]]_ dl = [[(`~ e1) `\/ (`~ e2)]]_ dl.
Proof.
case: dl; rewrite//= /minR /maxR !big_ord_recl !big_ord0 !tnthS !tnth0/= /minr /maxr; repeat case: ifP; intros; lra.
Qed.

End lattice_fuzzy_lemmas.
