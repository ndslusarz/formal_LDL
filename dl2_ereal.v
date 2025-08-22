From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra ldl dl2.

(**md**************************************************************************)
(* # Properties of DL2 on extended reals                                      *)
(*                                                                            *)
(* ## Structural properties                                                   *)
(* - dl2_andC_nary == n-ary commutativity of conjunction                      *)
(* - dl2_andC == commutativity of conjunction                                 *)
(* - dl2_andA == associativity of conjunction                                 *)
(* - dl2_orC_nary == n-ary commutativity of disjunction                       *)
(* - dl2_orC == commutativity of disjunction                                  *)
(* - dl2_orA == associativity of disjunction                                  *)
(*                                                                            *)
(* ## Adequacy                                                                *)
(* - dl2_ereal_translation_le0 == invariant for the translation: all values   *)
(*                                are in the range $[-\infty, 0]$             *)
(* - dl2_nary_inversion_andE1 == inversion lemma for conjunction/true         *)
(* - dl2_nary_inversion_andE0 == inversion lemma for conjuntion/false         *)
(* - dl2_nary_inversion_orE1 == inversion lemma for disjunction/true          *)
(* - dl2_nary_inversion_orE0 == inversion lemma for disjunction/false         *)
(* - dl2_translations_Vector_coincide == shows that the Boolean translation   *)
(*   and the DL2 translation coincide on expressions of type Vector_T         *)
(* - dl2_translations_Index_coincide == shows that the Boolean translation    *)
(*   and the DL2 translation coincide on expressions of type Index_T          *)
(* - dl2_translations_Real_coincide == shows that the Boolean translation and *)
(*   the DL2 translation coincide on expressions of type Real_T               *)
(* - dl2_ereal_adequacy == final adequacy result for DL2                      *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Local Open Scope ereal_scope.

Lemma adde_eq_pinfty {R : numDomainType} (x y : \bar R) :
  (x + y == +oo) = ((x == +oo) && (y != -oo)) || ((y == +oo) && (x != -oo)).
Proof. by move: x y => [?| |] [?| |]. Qed.

Local Close Scope ereal_scope.

Section dl2_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_dl2e" := (@dl2_ereal_translation R _ e).

Lemma dl2_mandC_nary (s1 s2 : seq (expr (Bool_T_def impl_def m_def l_undef))) :
  perm_eq s1 s2 -> [[ldl_mand s1]]_dl2e = [[ldl_mand s2]]_dl2e.
Proof.
move=> s12/=.
move/(perm_map (fun e => [[e]]_dl2e)) : (s12) => /[dup].
move/(perm_has (pred1 -oo%E)) ->.
move/(perm_has (pred1 +oo%E)) ->.
case: ifPn => //=; case: ifPn => //= _ _.
rewrite !big_map.
exact: perm_big.
Qed.

Lemma dl2_mandC (e1 e2 : expr (Bool_T_def impl_def m_def l_undef)) :
 [[ e1 `** e2 ]]_dl2e = [[ e2 `** e1 ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons !big_nil !adde0.
rewrite !(orbC ([[e2]]_dl2e == _)).
by rewrite addeC.
Qed.

Lemma dl2_mandA (e1 e2 e3 : expr (Bool_T_undef impl_def m_def l_undef)) :
  [[ e1 `** (e2 `** e3) ]]_dl2e = [[ (e1 `** e2) `** e3 ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons !big_nil !adde0.
have [H1//=|/negbTE H1/=] := eqVneq ([[e1]]_dl2e) -oo%E.
have [H2//=|/negbTE H2/=] := eqVneq ([[e2]]_dl2e) -oo%E.
have [H3/=|/negbTE H3/=] := eqVneq ([[e3]]_dl2e) -oo%E.
  by rewrite orbT.
have [K1//=|/negbTE K1/=] := eqVneq ([[e1]]_dl2e) +oo%E.
  have [K2//=|/negbTE K2/=] := eqVneq ([[e2]]_dl2e) +oo%E.
  have [K3//=|/negbTE K3/=] := eqVneq ([[e3]]_dl2e) +oo%E.
  by case: ifPn.
have [K2//=|/negbTE K2/=] := eqVneq ([[e2]]_dl2e) +oo%E.
have [K3//=|/negbTE K3/=] := eqVneq ([[e3]]_dl2e) +oo%E.
  rewrite !orbF !orbT.
  by case: ifPn.
rewrite !adde_eq_ninfty !orbF H1 H2 H3/=.
by rewrite !adde_eq_pinfty H1 H2 H3 K1 K2 K3/= addeA.
Qed.

Lemma dl2_morC_nary (s1 s2 : seq (expr (Bool_T_def impl_def m_def l_undef))) :
  perm_eq s1 s2 -> [[ldl_mor s1]]_dl2e = [[ldl_mor s2]]_dl2e.
Proof.
move=> s12/=.
move/(perm_map (fun e => [[e]]_dl2e)) : (s12) => /[dup].
move/(perm_has (pred1 -oo%E)) ->.
move/(perm_has (pred1 +oo%E)) ->.
case: ifPn => //=; case: ifPn => //= _ _.
rewrite !big_map.
exact: perm_big.
Qed.

Lemma dl2_morC (e1 e2 : expr (Bool_T_undef impl_def m_def l_undef)) :
 [[ e1 `++ e2 ]]_dl2e = [[ e2 `++ e1 ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons !big_nil !adde0.
rewrite !(orbC ([[e2]]_dl2e == _)).
by rewrite addeC.
Qed.

Lemma dl2_morA (e1 e2 e3 : expr (Bool_T_undef impl_def m_def l_undef)) :
  [[ e1 `++ (e2 `++ e3) ]]_dl2e = [[ (e1 `++ e2) `++ e3 ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons !big_nil !adde0.
have [H1//=|/negbTE H1/=] := eqVneq ([[e1]]_dl2e) -oo%E.
have [H2//=|/negbTE H2/=] := eqVneq ([[e2]]_dl2e) -oo%E.
have [H3/=|/negbTE H3/=] := eqVneq ([[e3]]_dl2e) -oo%E.
  by rewrite orbT.
have [K1//=|/negbTE K1/=] := eqVneq ([[e1]]_dl2e) +oo%E.
  have [K2//=|/negbTE K2/=] := eqVneq ([[e2]]_dl2e) +oo%E.
  have [K3//=|/negbTE K3/=] := eqVneq ([[e3]]_dl2e) +oo%E.
  by case: ifPn.
have [K2//=|/negbTE K2/=] := eqVneq ([[e2]]_dl2e) +oo%E.
have [K3//=|/negbTE K3/=] := eqVneq ([[e3]]_dl2e) +oo%E.
  rewrite !orbF !orbT.
  by case: ifPn.
rewrite !adde_eq_ninfty !orbF H1 H2 H3/=.
by rewrite !adde_eq_pinfty H1 H2 H3 K1 K2 K3/= addeA.
Qed.

Lemma dl2_ereal_translation_le0 e :
  ([[ e ]]_dl2e <= 0
    :> ereal_type_translation (Bool_T_undef impl_def m_def l_undef))%E.
Proof.
dependent induction e using expr_ind' => /=.
- by case: b.
- rewrite /maxe; case: ifPn => h //=.
  by rewrite leeNl oppe0 leNgt h.
- case: ifPn => //.
  case: ifPn => //.
  rewrite big_map big_seq sume_le0// => t tl.
  move/List.Forall_forall : H => /(_ t); apply => //.
  exact/In_in.
- case: ifPn => //.
  case: ifPn => //.
  rewrite big_map big_seq sume_le0// => t tl.
  move/List.Forall_forall : H => /(_ t); apply => //.
  exact/In_in.
- case: c => //=.
  by rewrite lee_fin oppr_le0 le_max lexx orbT.
Qed.

Theorem dl2_mand_unit (e : expr (Bool_T_undef impl_def m_def l_undef)) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_dl2e = [[ e ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons big_nil !adde0.
case: ifPn => [/eqP ->//|e2oo].
rewrite ifF//.
apply/negbTE.
by rewrite -leye_eq -ltNge (le_lt_trans (dl2_ereal_translation_le0 e)).
Qed.

Theorem dl2_residuation (e1 e2 e3 : expr (Bool_T_undef impl_def m_def l_undef)) :
  ([[ e1 `** e2 ]]_dl2e <= [[ e3 ]]_dl2e <->
   [[ e2 ]]_dl2e <= [[ e1 `=> e3 ]]_dl2e)%E.
Proof.
rewrite /= orbF.
have [H1//=|/negbTE H1/=] := eqVneq ([[e1]]_dl2e) -oo%E.
  rewrite H1 leNye; split => // _.
  rewrite (le_trans (dl2_ereal_translation_le0 e2))//.
  by rewrite -leeNr oppe0 addNye maxNye.
case: ifPn => //= H2.
  rewrite leNye; split => // _.
  by rewrite (eqP H2) leNye.
split.
- rewrite !big_cons big_nil adde0 => H.
  rewrite /maxe; case: ifPn => h.
  + by rewrite oppe0; exact: dl2_ereal_translation_le0.
  + rewrite oppeB; last first.
      rewrite /adde_def H1/= andbT.
      apply/negP => /andP[/eqP e1oo].
      rewrite eqe_oppLR/= => /eqP e3oo.
      by rewrite e1oo e3oo/= ltNyr in h.
    move: H.
    rewrite -leeBlDl; last first.
      rewrite fin_numN fin_numE H1/=.
      by rewrite -leye_eq -ltNge (le_lt_trans (dl2_ereal_translation_le0 e1)).
    rewrite orbF.
    rewrite ifF; last first.
      apply/negbTE.
      rewrite negb_or.
      rewrite -leye_eq -ltNge (le_lt_trans (dl2_ereal_translation_le0 e1))//=.
      by rewrite -leye_eq -ltNge (le_lt_trans (dl2_ereal_translation_le0 e2))//=.
    by rewrite oppeK addeC.
- rewrite !big_cons big_nil adde0 => H.
  rewrite /maxe; case: ifPn => [h|].
  + by rewrite leNye.
  + rewrite orbF negb_or => /andP[e1oo e2oo].
    move: H.
    rewrite /maxe.
    case: ifPn.
      rewrite oppe0 => e1e3 e20.
      rewrite sube_lt0 in e1e3; last first.
        by rewrite !fin_numE H1/= e1oo.
      rewrite (le_trans _ (ltW e1e3))//.
      rewrite -[leRHS]adde0.
      by rewrite leeD2l.
    move=> e1e3.
    rewrite oppeB; last first.
      by rewrite /adde_def H1/= andbT (negbTE e1oo)/=.
    rewrite addeC.
    rewrite -leeBlDr; last first.
      by rewrite fin_numN fin_numE e1oo H1.
    by rewrite oppeK addeC.
Qed.

Lemma dl2_ereal_translations_Vector_coincide : forall n (e : @expr R (Vector_T n)),
  [[ e ]]_dl2e = [[ e ]]_B.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ e2 erefl JMeq_refl).
Qed.

Lemma dl2_ereal_translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_dl2e = [[ e ]]_B.
Proof.
dependent induction e => //=.
Qed.

Lemma dl2_ereal_translations_Real_coincide (e : expr Real_T):
  [[ e ]]_dl2e = [[ e ]]_B.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite dl2_ereal_translations_Vector_coincide dl2_ereal_translations_Index_coincide.
Qed.

End dl2_lemmas.
