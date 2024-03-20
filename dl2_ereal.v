From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
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
(* ## Soundness                                                               *)
(* - dl2_translation_le0 == invariant for the translation: all values are in *)
(*                          the range $[-\infty, 0]$                          *)
(* - dl2_nary_inversion_andE1 == inversion lemma for conjunction/true         *)
(* - dl2_nary_inversion_andE0 == inversion lemma for conjuntion/false         *)
(* - dl2_nary_inversion_orE1 == inversion lemma for disjunction/true          *)
(* - dl2_nary_inversion_orE0 == inversion lemma for disjunction/false         *)
(* - dl2_translations_Vector_coincide == shows that the Boolean translation *)
(*   and the DL2 translation coincide on expressions of type Vector_T         *)
(* - dl2_translations_Index_coincide == shows that the Boolean translation *)
(*   and the DL2 translation coincide on expressions of type Index_T          *)
(* - dl2_translations_Real_coincide == shows that the Boolean translation and *)
(*   the DL2 translation coincide on expressions of type Real_T               *)
(* - dl2_soundness == final soundness result for DL2                          *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Section dl2_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_dl2e" := (@dl2_ereal_translation R _ e).

Lemma dl2_andC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_and s1]]_dl2e = [[ldl_and s2]]_dl2e.
Proof.
by move=> pi; rewrite /=/sumE !big_map (perm_big _ pi)/=.
Qed.

Lemma dl2_andC (e1 e2 : expr Bool_N) : [[ e1 `/\ e2 ]]_dl2e = [[ e2 `/\ e1 ]]_dl2e.
Proof.
by rewrite /=/sumE ?big_cons ?big_nil /= adde0 adde0 addeC.
Qed.

Lemma dl2_andA (e1 e2 e3 : expr Bool_P) :
  [[ e1 `/\ (e2 `/\ e3) ]]_dl2e = [[ (e1 `/\ e2) `/\ e3 ]]_dl2e.
Proof.
by rewrite /=/sumE ?big_cons ?big_nil !adde0 addeA.
Qed.

Lemma dl2_orC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_or s1]]_dl2e = [[ldl_or s2]]_dl2e.
Proof.
by move=> pi; rewrite /=/prodE !big_map (perm_big _ pi)/= (perm_size pi).
Qed.

Lemma dl2_orC (e1 e2 : expr Bool_P) :
 [[ e1 `\/ e2 ]]_dl2e = [[ e2 `\/ e1 ]]_dl2e.
Proof.
rewrite /= /prodE !big_cons big_nil !mule1; congr *%E.
by rewrite muleC.
Qed.

Lemma dl2_orA (e1 e2 e3 : expr Bool_P) :
  [[ e1 `\/ (e2 `\/ e3) ]]_dl2e = [[ (e1 `\/ e2) `\/ e3 ]]_dl2e.
Proof.
rewrite /= /prodE !big_cons big_nil !mule1; congr (_ * _)%E.
by rewrite muleCA !muleA.
Qed.

Lemma dl2_ereal_translation_le0 e :
  ([[ e ]]_dl2e <= 0 :> ereal_type_translation Bool_P)%E.
Proof.
dependent induction e using expr_ind' => /=.
- by case: b.
- rewrite /sumE big_map big_seq sume_le0// => t tl.
  move/List.Forall_forall : H => /(_ t); apply => //.
  exact/In_in.
- rewrite /prodE big_map big_seq; have [ol|ol] := boolP (odd (length l)).
    rewrite exprS -signr_odd ol expr1 mulrN1 !EFinN oppeK mul1e.
    have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2e != 0)%E; last first.
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
  have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2e != 0)%E; last first.
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

Definition is_dl2 b (x : \bar R) := (if b then x == 0 else x < 0)%E.

Lemma dl2_nary_inversion_andE1 (s : seq (expr (Bool_P))) :
  is_dl2 true ([[ ldl_and s ]]_dl2e) ->
  (forall i, (i < size s)%N -> is_dl2 true ([[ nth (ldl_bool _ false) s i ]]_dl2e)).
Proof.
rewrite/is_dl2.
elim: s => //= h t ih H [_|]/=.
  move: H; rewrite /sumE big_cons.
  rewrite nadde_eq0//.
  - by move=> /andP[->].
  - exact: dl2_ereal_translation_le0.
  - rewrite big_seq_cond; apply: sume_le0 => /= x.
    by rewrite andbT => /mapP[/= e et] ->; exact: dl2_ereal_translation_le0.
move=> n; rewrite ltnS => nt /=; apply: ih => //.
move: H; rewrite /sumE big_cons.
rewrite nadde_eq0.
- by move=> /andP[_ ->].
- exact: dl2_ereal_translation_le0.
- rewrite big_seq_cond; apply: sume_le0 => /= x.
  by rewrite andbT => /mapP[/= e et] ->; exact: dl2_ereal_translation_le0.
Qed.

Lemma dl2_nary_inversion_andE0 (s : seq (expr (Bool_P))) :
  is_dl2 false ([[ ldl_and s ]]_dl2e) ->
  (exists i, (is_dl2 false ([[ nth (ldl_bool _ false) s i ]]_dl2e)) && (i < size s)%nat).
Proof.
rewrite/is_dl2.
elim: s => [|h t ih] //=; first by rewrite /sumE big_nil ltxx.
rewrite /sumE big_cons => /nadde_lt0 => /(_ (dl2_ereal_translation_le0 _)).
have : (\sum_(j <- [seq [[i]]_dl2e | i <- t]) j <= 0)%E.
  rewrite big_seq_cond; apply: sume_le0 => /= z.
  by rewrite andbT => /mapP[/= e et ->]; exact: dl2_ereal_translation_le0.
move=> /[swap] /[apply] /orP[H|/ih[j /andP[j0 jt]]].
  by exists 0%N; rewrite /= H.
by exists j.+1; rewrite /= j0.
Qed.

Lemma dl2_nary_inversion_orE1 (s : seq (expr (Bool_P))) : [[ ldl_or s ]]_dl2e = 0%E ->
  exists i, ([[ nth (ldl_bool _ false) s i ]]_dl2e == 0%E) && (i < size s)%nat.
Proof.
elim: s => [|h t ih] /=.
  rewrite /prodE big_nil mule1 expr1 EFinN => /eqe_oppLRP.
  by rewrite oppe0 => /eqP; rewrite onee_eq0.
move=> /eqP; rewrite mule_eq0 eqe signr_eq0/=.
rewrite /prodE big_cons mule_eq0 => /orP[H|/eqP H].
  by exists 0%N; rewrite /= H.
have /ih[j /andP[Hj jt]] : [[ldl_or t]]_dl2e = 0 by rewrite /= /prodE H mule0.
by exists j.+1; rewrite /= Hj.
Qed.

Lemma dl2_nary_inversion_orE0 (Es : seq (expr (Bool_P)) ) :
    ([[ ldl_or Es ]]_dl2e  < 0)%E  -> (forall i, (i < size Es)%nat -> ([[ nth (ldl_bool _ false) Es i ]]_dl2e < 0)%E).
Proof.
elim: Es => //= a l IH.
rewrite /prodE big_cons muleCA mule_lt0 => /andP[aneq0]/andP[]/[swap] _.
rewrite exprS EFinM -muleA EFinN mulN1e oppe_eq0 => lneq0.
have ale0 := dl2_ereal_translation_le0 a.
have alt0 : ([[a]]_dl2e < 0)%E by rewrite lt_neqAle aneq0 ale0.
elim => [_//=|i _].
rewrite ltnS => isize.
apply IH => //.
rewrite /prodE lt_neqAle lneq0/= big_map.
apply: prode_le0 => j.
exact: dl2_ereal_translation_le0.
Qed.

Lemma dl2_ereal_translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  [[ e ]]_dl2e = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ e2 erefl JMeq_refl).
Qed.

Lemma dl2_ereal_translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_dl2e = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma dl2_ereal_translations_Real_coincide (e : expr Real_T):
  [[ e ]]_dl2e = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite dl2_ereal_translations_Vector_coincide dl2_ereal_translations_Index_coincide.
Qed.

Lemma dl2_soundness (e : expr Bool_P) b :
  is_dl2 b ([[ e ]]_dl2e) -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind'.
- by move: b b0 => [] [] //=; rewrite ltxx.
- rewrite List.Forall_forall in H.
  move: b => [].
  + move/dl2_nary_inversion_andE1.
    rewrite /= big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    by apply: H => //=; rewrite ?h// -In_in mem_nth.
  + move/dl2_nary_inversion_andE0.
    rewrite /= big_map big_all.
    elim=>// i /andP[/eqP i0 isize].
    apply/allPn; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    * by rewrite -In_in mem_nth.
    * rewrite /is_dl2/=. move: i0.
      by rewrite eqb_id.
- rewrite List.Forall_forall in H.
  move: b => [].
  + rewrite/is_dl2=>/eqP; move/dl2_nary_inversion_orE1.
    rewrite /= big_map big_has.
    elim=>// i /andP[/eqP i0 isize].
    apply/hasP; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
    rewrite /is_dl2/=. by rewrite i0.
  + move/dl2_nary_inversion_orE0.
    rewrite /= big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    apply/negPf; apply: H => //.
    * by rewrite ?h// -In_in mem_nth.
    * by rewrite /is_dl2/= h.
- case: c; rewrite //=; rewrite -!dl2_ereal_translations_Real_coincide;
  set t1 := _ e1; set t2 := _ e2; case: b => //.
  + by rewrite /is_dl2 => /eqP[] /maxr0_le; rewrite subr_le0.
  + rewrite/is_dl2 lte_fin oppr_lt0 /maxr; case: ifPn; first by rewrite ltxx.
    by rewrite subr_gt0 => _; move/lt_geF.
  + by rewrite/is_dl2=>/eqP; case=>/eqP; rewrite oppr_eq0 normr_eq0 subr_eq0.
  + rewrite/is_dl2; rewrite lte_fin oppr_lt0 normr_gt0.
    by rewrite subr_eq0; move/eqP => h; apply/eqP.
Qed.

End dl2_lemmas.
