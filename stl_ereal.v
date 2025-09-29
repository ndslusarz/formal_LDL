From HB Require Import structures.
Require Import Stdlib.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra dl.

(**md**************************************************************************)
(* # Properties of STL on extended reals                                      *)
(*                                                                            *)
(* ## Structural properties                                                   *)
(* - andI_stl == idempotence of conjunction                                   *)
(* - andC_stl == commutativity of conjunction                                 *)
(* - orI_stl == idempotence of disjunction                                    *)
(* - orC_stl == commutativity of disjunction                                  *)
(*                                                                            *)
(* ## Adequacy                                                                *)
(* - stl_nary_inversion_andE1 == inversion lemma for conjunction/true         *)
(* - stl_nary_inversion_andE0 == inversion lemma for conjuntion/false         *)
(* - stl_nary_inversion_orE1 == inversion lemma for disjunction/true          *)
(* - stl_nary_inversion_orE0 == inversion lemma for disjunction/false         *)
(* - stl_ereal_translations_Vector_coincide == shows that the Boolean         *)
(*   translation and the STL translation coincide on expressions of type      *)
(*   Vector_T                                                                 *)
(* - stl_ereal_translations_Index_coincide == shows that the Boolean          *)
(*   translation and the STL translation coincide on expressions of type      *)
(*   Index_T                                                                  *)
(* - stl_ereal_translations_Real_coincide == shows that the Boolean           *)
(*   translation and the STL translation coincide on expressions of type      *)
(*   Real_T                                                                   *)
(* - stl_ereal_adequacy == final adequacy result for STL                      *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

HB.instance Definition _ (R : realType) x y z v :=
  @gen_eqMixin (@expr R (boolT x y z v )).

Section stl_lemmas.
Local Open Scope ring_scope.
Context {R : realType}.
Variables nu : R.
Hypothesis nu0 : 0 < nu.
Local Open Scope dl_scope.
Local Open Scope ereal_scope.

Lemma andI_stl f (e : expr (boolT_def f m_undef l_def)) :
  nu.-[[e `/\ e]]_stle = nu.-[[e]]_stle.
Proof.
rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0/=.
have [->//|epoo] := eqVneq (nu.-[[e]]_stle) +oo.
have [->//=|enoo] := eqVneq (nu.-[[e]]_stle) -oo.
set a_min := mine (nu.-[[e]]_stle) (mine (nu.-[[e]]_stle) +oo).
set a := mine_dev (nu.-[[e]]_stle) a_min.
have a_min_e : a_min = nu.-[[e]]_stle.
  by rewrite /a_min /mine; repeat case: ifPn => //; rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0 by rewrite /a a_min_e mine_devxx// fin_numE epoo enoo.
rewrite !adde0 !mule0 expeR0 !mule1/= a_min_e.
have : (nu.-[[e]]_stle + nu.-[[e]]_stle) / (1 + 1)%:E = nu.-[[e]]_stle.
  by rewrite -mule2n -mule_natr -muleA divee// mule1.
rewrite (negbTE enoo)/= (negbTE epoo)/=; case: ifPn => //.
rewrite -leNgt => nue0.
case: ifPn => //; rewrite -leNgt => nue0' _.
by apply: le_anti_ereal; apply/andP; split.
Qed.

Lemma andC_stl f (e1 e2 : expr (boolT_def f m_undef l_def)) :
  nu.-[[e1 `/\ e2]]_stle = nu.-[[e2 `/\ e1]]_stle.
Proof.
rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0 /=.
set a_min := mine (nu.-[[e1]]_stle) (mine (nu.-[[e2]]_stle) +oo).
have -> : (mine (nu.-[[e2]]_stle) (mine (nu.-[[e1]]_stle) +oo)) = a_min.
  by rewrite minA [X in mine X _]minC -minA.
set a1 := mine_dev (nu.-[[e1]]_stle) a_min.
set a2 := mine_dev (nu.-[[e2]]_stle) a_min.
rewrite !adde0.
case: ifPn => // aminNy.
case: ifPn => // aminy.
case: ifPn => a0.
  by rewrite addeC [X in _ / X]addeC.
case: ifPn => // a0'.
by rewrite addeC [X in _ / X]addeC.
Qed.

Lemma orI_stl f (e : expr (boolT_def f m_undef l_def)) :
  nu.-[[e `\/ e]]_stle = nu.-[[e]]_stle.
Proof.
rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0/=.
have [->//|enoo] := eqVneq (nu.-[[e]]_stle) -oo.
have [->//=|epoo] := eqVneq (nu.-[[e]]_stle) +oo.
set a_max := maxe (nu.-[[e]]_stle) (maxe (nu.-[[e]]_stle) -oo).
set a := maxe_dev a_max (nu.-[[e]]_stle).
have a_max_e : a_max = nu.-[[e]]_stle.
  by rewrite /a_max /maxe; repeat case: ifPn; rewrite ltNge leNye.
have -> : a = 0 by rewrite /a a_max_e maxe_devxx// fin_numE epoo enoo.
rewrite !adde0 !mule0 expeR0 !mule1/= a_max_e.
have -> : (nu.-[[e]]_stle + nu.-[[e]]_stle) / (1 + 1) = nu.-[[e]]_stle.
  by rewrite -mule2n -mule_natr -muleA divee// mule1.
case: ifPn => [/eqP->//|?].
case: ifPn => [/eqP->//|?].
case: ifPn => [//|].
rewrite -leNgt => ege0.
case: ifPn => [//|].
rewrite -leNgt => ele0.
by apply/eqP; rewrite eq_le ege0 ele0.
Qed.

Lemma orC_stl f (e1 e2 : expr (boolT_def f m_undef l_def)) :
  nu.-[[e1 `\/ e2]]_stle  = nu.-[[e2 `\/ e1]]_stle.
Proof.
rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0 /=.
set a_max := maxe (nu.-[[e1]]_stle) (maxe (nu.-[[e2]]_stle) -oo).
have -> : maxe (nu.-[[e2]]_stle) (maxe (nu.-[[e1]]_stle) -oo) = a_max.
  by rewrite maxA [X in maxe X _]maxC -maxA.
set a1 := maxe_dev a_max (nu.-[[e1]]_stle).
set a2 := maxe_dev a_max (nu.-[[e2]]_stle).
rewrite !adde0.
case: ifPn; first by [].
move=> aNy.
case: ifPn; first by [].
move=> ay.
case: ifPn.
  by rewrite addeC [in X in _ / X]addeC.
move=> a0.
case: ifPn => // a0'.
by rewrite addeC [in X in _ / X]addeC.
Qed.

Lemma stl_ereal_translations_coincide t (e : @expr R t) n m j :
  (t = realT \/ t = vectorT n \/ t = indexT n \/ t = funT n m \/ t = fun2T n m j) ->
  nu.-[[ e ]]_stle ~= [[ e ]]_B.
Proof.
dependent induction e using expr_ind' => //=; move=> [|[|[|[|]]]]t0//.
- rewrite (JMeq_eq (IHe1 n m j _)); last by right; right; right; left.
  by rewrite (JMeq_eq (IHe2 n m j _)); last by right; left.
- rewrite (JMeq_eq (IHe1 n m l _)); last by right; right; right; right.
  rewrite (JMeq_eq (IHe2 n m l _)); last by right; left.
  by rewrite (JMeq_eq (IHe3 m n l _)); last by right; left.
- rewrite (JMeq_eq (IHe1 n m j _)); last by right; left.
  by rewrite (JMeq_eq (IHe2 n m j _)); last by right; right; left.
Qed.

Lemma stl_ereal_translations_Fun_coincide n m (e : expr (funT n m)) :
  nu.-[[ e ]]_stle = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(stl_ereal_translations_coincide _ _ n m 0); right;right;right;left.
Qed.

Lemma stl_ereal_translations_Vector_coincide n (e : @expr R (vectorT n)) :
  nu.-[[ e ]]_stle = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(stl_ereal_translations_coincide _ _ n 0 0); right;left.
Qed.

Lemma stl_ereal_translations_Index_coincide n (e : expr (indexT n)) :
  nu.-[[ e ]]_stle = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(stl_ereal_translations_coincide _ _ n 0 0); right;right;left.
Qed.

Lemma stl_ereal_translations_Real_coincide (e : expr realT):
  nu.-[[ e ]]_stle = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(stl_ereal_translations_coincide _ _ 0 0 0); left.
Qed.

Definition is_stl b (x : \bar R) := if b then x >= 0 else x < 0.

Lemma stl_nary_inversion_andE1 f n
    (Es : 'I_n -> expr (boolT_undef f m_undef l_def)) :
  is_stl true (nu.-[[ dl_and Es ]]_stle) ->
  (forall i, is_stl true (nu.-[[ Es i ]]_stle)).
Proof.
rewrite /is_stl/=.
case: ifPn => [//|hnoo].
case: ifPn => [/eqP min_apoo _|hpoo].
  by move=> i; rewrite ((mine_eqyP _ _ _).1 min_apoo i (mem_index_enum _) isT).
case: ifPn=>[hminlt0|].
  rewrite leNgt.
  rewrite mule_lt0_gt0//; last first.
    rewrite inve_gt0//; last 2 first.
      rewrite psume_eq0; last 2 first.
        apply/allPn.
        have [h hEs nuhoo] : exists2 h, h \in index_enum _ & nu.-[[Es h]]_stle != +oo.
          apply/not_exists2P => abs.
          move/eqP : hpoo; apply.
          apply/big_miney => x xEs.
          have [//|] := abs x.
          move/negP.
          by rewrite negbK => /eqP.
        exists h => //.
        rewrite implyTb.
        rewrite expeR_eq0.
        rewrite mule_eq_ninfty//.
        rewrite lte_fin nu0/= orbF ltNge lee_fin (ltW nu0)/= orbF.
        rewrite /mine_dev mule_eq_ninfty//=.
        rewrite inve_eqNy (negbTE hnoo)/= andbF/=.
        rewrite inve_eqy lt_eqF// andbF/=.
        rewrite inve_gt0//; last by rewrite lt_eqF.
        rewrite ltNge (ltW hminlt0)/= andbF/=.
        rewrite inve_lt0 hminlt0 andbT.
        rewrite adde_Neq_pinfty// ?eqe_oppLR/= ?hnoo ?hpoo ?andbT//.
        apply: contra hnoo => /eqP hoo.
        apply/eqP.
        apply: big_mineNy.
        apply/mapP.
        by exists h => //.
        move=> /= i _.
        by rewrite expeR_ge0.
      rewrite -ltey.
      rewrite big_seq.
      apply: lte_sum_pinfty => /= i iEs.
      apply: expeR_lty.
      rewrite /mine_dev.
      rewrite ltey !mule_eq_pinfty/= !negb_or !negb_and !negb_or !negb_and/=.
      rewrite andbT !lte_fin nu0/=.
      rewrite inve_eqy lt_eqF//= orbT/=.
      rewrite inve_eqNy hnoo orbT/=.
      rewrite inve_lt0 hminlt0/= orbF.
      rewrite inve_gt0//; last by rewrite lt_eqF.
      rewrite -leNgt (ltW hminlt0)/= orbT/=.
      rewrite -leNgt (ltW nu0)/= andbT.
      rewrite adde_eq_ninfty negb_or.
      rewrite eqe_oppLR/= hpoo andbT.
      apply: contra hnoo => /eqP iNy; apply/eqP.
      rewrite big_mineNy//.
      by apply/mapP; exists i.
    rewrite big_seq_cond sume_gt0//.
    move=> i /andP[iEs _]; apply: expeR_ge0.
    have := hminlt0.
    move/mine_lt => [i [iEs _ hilt0]].
    exists i; split; [exact: iEs|by rewrite andbT|].
    rewrite expeR_gt0 ?iEs//.
    rewrite ltNye !mule_eq_ninfty.
    rewrite !lte_fin !nu0/=.
    rewrite !negb_or !negb_and -!leNgt/= andbT.
    rewrite (ltW nu0)/= andbT.
    rewrite inve_le0//; last by rewrite lt_eqF.
    rewrite (ltW hminlt0) !orbT/=.
    rewrite inve_eqNy hnoo orbT/=.
    rewrite inve_eqy lt_eqF//= orbT/=.
    rewrite inve_ge0 leNgt hminlt0/= orbF.
    have [->|nuiNy] := eqVneq (nu.-[[Es i]]_stle) -oo.
      move: hnoo hpoo.
      by case: (\big[mine/-oo]_(j0 < n) nu.-[[Es j0]]_stle).
    rewrite adde_Neq_pinfty//; last by rewrite eqe_oppLR.
    by rewrite eqe_oppLR/= hnoo andbT lt_eqF// (lt_le_trans hilt0).
  apply sume_lt0.
    move=> i _.
    rewrite !mule_le0_ge0//; last 2 first.
      by apply expeR_ge0.
      by apply expeR_ge0.
    exact: ltW.
  have := hminlt0.
  rewrite {1}big_seq_cond.
  move/mine_lt => [i [iEs _ hilt0]].
  exists i; split => //.
  rewrite mule_lt0_gt0//; last first.
    rewrite expeR_gt0// ltNye !mule_eq_ninfty/=.
    rewrite orbF/=.
    rewrite lte_fin nu0/=.
    rewrite inve_lt0 hminlt0 andbT.
    rewrite inve_eqNy (negbTE hnoo) andbF/=.
    rewrite inve_eqy lt_eqF// andbF/=.
    rewrite inve_gt0//; last by rewrite lt_eqF.
    rewrite ltNge (ltW hminlt0)/= andbF/=.
    rewrite ltNge lee_fin (ltW nu0)/= orbF.
    have [->|nuiNy] := eqVneq (nu.-[[Es i]]_stle) -oo.
      move: hnoo hpoo.
      by case: (\big[mine/-oo]_(j0 < n) nu.-[[Es j0]]_stle).
    move: hnoo hpoo hminlt0.
    case: (\big[mine/+oo]_(j < n) nu.-[[Es j]]_stle) => // r _ _.
    rewrite lte_fin => r0.
    rewrite adde_Neq_pinfty// eqe_oppLR/= andbT.
    by rewrite lt_eqF// (lt_le_trans hilt0).
  rewrite mule_lt0 hminlt0/= {1}lt_eqF//= {1}gt_eqF//=.
    by rewrite -leNgt expeR_ge0.
  rewrite expeR_gt0// ltNye mule_eq_ninfty !negb_or !negb_and -!leNgt.
  rewrite inve_eqNy hnoo orbT/=.
  rewrite inve_eqy lt_eqF//= orbT/=.
  rewrite inve_le0//; last by rewrite lt_eqF.
  rewrite (ltW hminlt0) orbT/=.
  rewrite inve_ge0 leNgt hminlt0/= orbF.
  have [->|nuiNy] := eqVneq (nu.-[[Es i]]_stle) -oo.
    move: hnoo hpoo.
    by case: (\big[mine/+oo]_(j0 < n) nu.-[[Es j0]]_stle).
  rewrite adde_Neq_pinfty//; last by rewrite eqe_oppLR.
  rewrite lt_eqF//=; last by rewrite (lt_le_trans hilt0).
  by rewrite eqe_oppLR.
by rewrite -leNgt => /mine_geP + _ i => /(_ i(mem_index_enum _) isT).
Qed.

Lemma stl_nary_inversion_andE0 f n
    (Es : 'I_n -> expr (boolT_undef f m_undef l_def) ) :
  is_stl false (nu.-[[ dl_and Es ]]_stle) ->
  exists i, is_stl false (nu.-[[ Es i ]]_stle).
Proof.
rewrite /is_stl/=.
case: ifPn => [/eqP|hnoo].
  move/(@mine_eq _ _ _ _ _ -oo isT) => [x [_ _ hxnoo]].
  by exists x; rewrite hxnoo ltNy0.
case: ifPn => [/eqP|hpoo].
  by rewrite lt_neqAle leye_eq => _ /andP[_ /eqP].
case: ifPn => [|].
  rewrite {1}big_seq_cond.
  move/mine_lt => [x [xEs _ xlt0]].
  by exists x; rewrite xlt0.
rewrite -leNgt => hge0.
case: ifPn => [hgt0|].
  apply: contraPP => /forallNP h.
  apply/negP; rewrite -leNgt mule_ge0//=.
    rewrite big_seq sume_ge0// => x xEs.
    rewrite mule_ge0// leNgt; first exact/negP.
    by rewrite -leNgt expeR_ge0.
  rewrite inve_ge0 sume_ge0// => i _.
  exact/expeR_ge0.
by rewrite ltxx.
Qed.

Lemma stl_nary_inversion_orE1 f n
    (Es : 'I_n -> expr (boolT_undef f m_undef l_def)) :
  is_stl true (nu.-[[ dl_or Es ]]_stle) ->
  exists i, is_stl true (nu.-[[ Es i ]]_stle).
Proof.
rewrite /is_stl/=.
case: ifPn => [_|hnoo]; first by rewrite leNgt ltNyr.
case: ifPn => [/eqP|hpoo].
  move/maxe_eq => /(_ isT)[x [xEs _ xlt0]] _.
  by exists x; rewrite xlt0 ltW.
have := hnoo; rewrite eq_sym -ltNye => /maxe_gt[j [jEs _ jgtNye]].
case: ifPn => [hlt0 _|].
  move: hlt0 => /maxe_gt [x [xEs _ hxgt0]].
  by exists x; rewrite ltW.
rewrite -leNgt => hle0.
case: ifPn => [hlt0|].
  have h1 i :
      maxe_dev (\big[maxe/-oo]_(i0 < n) nu.-[[Es i0]]_stle) (nu.-[[Es i]]_stle) != +oo.
    rewrite /maxe_dev mule_eq_pinfty !negb_or !negb_and -!leNgt.
    rewrite lt_eqF; last by rewrite ltey// inve_eqy// lt_eqF.
    rewrite !orbT/= inve_le0//; last by rewrite lt_eqF.
    rewrite hle0 !orbT adde_eq_ninfty negb_or hnoo/= -!oppeey oppeK.
    rewrite eqe_oppLR inve_eqNy hnoo orbT inve_ge0// leNgt hlt0 orbF lt_eqF//=.
    exact: (lt_trans ((@maxe_lt _ _ _ _ _ _ _).1 hlt0 i (mem_index_enum _) _)).
  have h2 i (gtNyi : -oo < nu.-[[Es i]]_stle) :
      maxe_dev (\big[maxe/-oo]_(i0 < n) nu.-[[Es i0]]_stle) (nu.-[[Es i]]_stle) != -oo.
    rewrite /maxe_dev mule_eq_ninfty !negb_or !negb_and -!leNgt.
    rewrite gt_eqF; last by rewrite ltNye inve_eqNy.
    rewrite orbT inve_eqy lt_eqF// orbT/=.
    rewrite inve_le0//; last by rewrite lt_eqF.
    rewrite hle0 orbT inve_ge0 leNgt hlt0 orbF/=.
    have [->|nuiNy] := eqVneq (nu.-[[Es i]]_stle) +oo.
      move: hnoo hpoo.
      by case: (\big[maxe/-oo]_(j0 < n) nu.-[[Es j0]]_stle).
    rewrite adde_Neq_pinfty//; last by rewrite eqe_oppLR.
    by rewrite hpoo/= eqe_oppLR/= gt_eqF.
  rewrite !big_seq.
  rewrite leNgt nmule_rlt0.
    rewrite inve_gt0; last 2 first.
    - rewrite psume_eq0; last 2 first.
      - apply/allPn.
        have [h nuhoo] : exists h, nu.-[[Es h]]_stle != -oo.
          apply/not_existsP => abs.
          move/eqP : hnoo; apply.
          apply/big_maxeNy => x xEs.
          move: (abs x) => /negP.
          by rewrite negbK => /eqP.
        exists h; first exact/mem_index_enum.
        rewrite negb_imply mem_index_enum/=.
        rewrite expeR_eq0 mule_eq_ninfty//.
        rewrite lte_fin nu0/= orbF ltNge lee_fin (ltW nu0)/= orbF.
        rewrite /mine_dev mule_eq_ninfty//=.
        rewrite inve_eqNy -big_seq (negbTE hnoo) andbF/=.
        rewrite inve_eqy lt_eqF// andbF/=.
        rewrite inve_gt0//; last by rewrite lt_eqF.
        rewrite ltNge hle0 andbF/=.
        rewrite inve_lt0 hlt0 andbT.
        rewrite adde_Neq_pinfty// ?eqe_oppLR/= ?hnoo ?hpoo ?andbT//=.
        apply: contra hpoo => /eqP hoo.
        apply/eqP.
        apply: big_maxey.
        apply/mapP.
        by exists h; first exact: mem_index_enum.
      - move=> /= i _.
        by rewrite expeR_ge0.
      rewrite -ltey lte_sum_pinfty// => i iEs.
      rewrite expeR_lty// lteey mule_eq_pinfty !negb_or !negb_and !lte_fin nu0 -!leNgt (ltW nu0)//= andbT -big_seq.
      exact: h1.
    move=> /negP abs; exfalso; apply: abs.
    rewrite sume_gt0//.
      move=> i iEs.
      by rewrite expeR_ge0.
    exists j; split => //.
    rewrite expeR_gt0//.
    rewrite ltNye mule_eq_ninfty//.
    rewrite lte_fin nu0/= orbF.
    rewrite ltNge lee_fin (ltW nu0)/= orbF.
    rewrite /maxe_dev mule_eq_ninfty.
    rewrite inve_eqNy -big_seq (negbTE hnoo) andbF/=.
    rewrite inve_eqy lt_eqF// andbF/=.
    rewrite inve_gt0//; last by rewrite lt_eqF.
    rewrite ltNge hle0/= andbF/=.
    rewrite inve_lt0 hlt0 andbT.
    rewrite adde_Neq_pinfty// ?eqe_oppLR/= ?hnoo ?hpoo ?andbT//=.
    by rewrite -ltNye.
    apply: contra hpoo => /eqP hoo.
    apply/eqP/big_maxey.
    by apply/mapP; exists j.
  - rewrite sume_lt0//.
    move=> i iEs; rewrite nmule_rle0 ?expeR_ge0//.
      by move: hlt0 => /maxe_lt ->.
    exists j; rewrite jEs ?nmule_rlt0 ?expeR_gt0//.
      rewrite ltNye mule_eq_ninfty !lte_fin ltrNl ltrNr oppr0 nu0 !negb_or !negb_and -leNgt (ltW nu0) andbT/= -big_seq.
      exact: h1.
    by move: hlt0 => /maxe_lt ->.
rewrite -leNgt => hge0 _.
move: hge0 => /maxe_ge'.
rewrite gt_eqF//=.
move=> /(_ isT)[i [iEs _ hige0 ] ].
by exists i; rewrite hige0.
Qed.

Lemma stl_nary_inversion_orE0 f n
    (Es : 'I_n -> expr (boolT_undef f m_undef l_def)) :
  is_stl false (nu.-[[ dl_or Es ]]_stle) ->
  forall i, is_stl false (nu.-[[ Es i ]]_stle).
Proof.
rewrite/is_stl/=.
case: ifPn => [/eqP hnoo _|hnoo].
  move=> i.
  move: hnoo => /maxe_eqyP ->//.
  exact: mem_index_enum.
case: ifPn => [/eqP hpoo//|hpoo].
case: ifPn => [hgt0|].
  rewrite !big_seq ltNge.
  rewrite mule_ge0//; last first.
    rewrite inve_ge0 sume_ge0//.
    by move=> i iEs; rewrite expeR_ge0.
  rewrite sume_ge0// => i iEs.
  rewrite !mule_ge0// ?expeR_ge0//.
  by rewrite -big_seq ltW.
rewrite -leNgt => hle0.
case: ifPn => [hlt0 _|].
  move=> i.
  move: hlt0 => /maxe_lt ->//.
  exact: mem_index_enum.
by rewrite ltxx.
Qed.

Lemma stl_ereal_adequacy (e : expr (boolT_undef impl_undef m_undef l_def)) b :
  is_stl b (nu.-[[ e ]]_stle) -> [[ e ]]_B = b.
Proof.
dependent induction e using expr_ind'.
- move: b b0 => [] [] //=.
- move: b => []. rewrite /is_stl.
  + move/stl_nary_inversion_andE1 => h/=.
    by rewrite big_all; apply/allP => i _; exact/(@H i _ _ _ true (h i)).
  + move/stl_nary_inversion_andE0 => [i h]/=.
    rewrite big_all; apply/allPn.
    by exists i; rewrite ?mem_index_enum// (@H i _ _ _ false).
- move: b => [].
  + move/stl_nary_inversion_orE1 => [i h]/=.
    rewrite big_has; apply/hasP.
    by exists i; rewrite ?mem_index_enum// (@H i _ _ _ true).
  + move/stl_nary_inversion_orE0 => h/=.
    by rewrite big_has; apply/hasPn => i _; rewrite (@H i _ _ _ false).
- case: c.
  + by case: b; rewrite /is_stl/= ?lee_fin ?lte_fin ?ltNge subr_ge0 !stl_ereal_translations_Real_coincide// => /negbTE.
  + case: b; rewrite /is_stl/= ?lee_fin ?lte_fin !stl_ereal_translations_Real_coincide.
    by rewrite oppr_ge0 normr_le0 subr_eq0.
    by rewrite oppr_lt0 normr_gt0 subr_eq0 => /negbTE.
Qed.

End stl_lemmas.
