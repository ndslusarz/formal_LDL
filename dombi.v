From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals ereal signed topology derive.
From mathcomp Require Import normedtype sequences exp measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra ldl.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Section dombi_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable v : R.
Hypothesis v1 : v < 1.
Hypothesis v2 : v > 0.

Local Notation "[[ e ]]_d" := (@dombi_translation R v _ e).

Lemma dombi_translations_Fun_coincide:
  forall n m (e : expr (Fun_T n m)), [[ e ]]_d = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma dombi_translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  [[ e ]]_d = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ v1 v2 _ e2 erefl JMeq_refl).
Qed.

Lemma dombi_translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_d = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma dombi_translations_Real_coincide (e : expr Real_T):
  [[ e ]]_d = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite dombi_translations_Vector_coincide dombi_translations_Index_coincide.
Qed.

Lemma dombi_translate_Bool_T_01 (e : expr Bool_N) :
  0 <= [[ e ]]_d <= 1.
Proof.
dependent induction e using expr_ind'.
- rewrite /=; case b; lra.
- move: H. rewrite /=; move=> /List.Forall_forall H.
  rewrite /sumR; apply/andP; split.
  + Search (0 <= _%E ^ _).  admit.
  + Search powR (1). admit.

- move: H. rewrite /=; move=> /List.Forall_forall H.
  rewrite /sumR; apply/andP; split.
  + admit.
  + admit.

- move: IHe => /(_ e erefl JMeq_refl).
  rewrite //=. set a := [[e]]_d.
  move => a1; apply/andP; split.
  + admit.
  + admit.
- case: c => /=; case: ifP => ?.
  - by case: ([[e1]]_d <= [[e2]]_d)%R; rewrite lexx ler01.
  - by rewrite le_maxr lexx orbT/= le_maxl ler01 gerBl// le_maxr lexx orbT.
  - by case: ([[e1]]_d == [[e2]]_d); rewrite lexx ler01.
  - by rewrite le_maxr lexx orbT/= le_maxl ler01 gerBl// normr_ge0 andTb.
Admitted.

Lemma dombi_nary_inversion_andE1 (s : seq (expr (Bool_N))) :
  [[ ldl_and s ]]_d = 1 ->
    forall i, (i < size s)%N -> [[ nth (ldl_bool _ false) s i ]]_d = 1.
Proof.
have := dombi_translate_Bool_T_01.
Admitted.

Lemma dombi_nary_inversion_andE0 (s : seq (expr (Bool_N))) :
  [[ ldl_and s ]]_d = 0 ->
   exists2 i, ([[ nth (ldl_bool _ false) s i ]]_d == 0) & (i < size s)%N.
Proof.
have H := dombi_translate_Bool_T_01. move: H.
Admitted.

Lemma dombi_nary_inversion_orE1 (Es : seq (expr (Bool_N))) :
  [[ ldl_or Es ]]_d = 1 ->
    exists2 i, ([[ nth (ldl_bool _ false) Es i ]]_d == 1) & (i < size Es)%N.
Proof.
Admitted.

Lemma dombi_nary_inversion_orE0 (Es : seq (expr (Bool_N))) :
  [[ ldl_or Es ]]_d = 0 ->
    forall i, (i < size Es)%N -> [[ nth (ldl_bool _ false) Es i ]]_d = 0.
Proof.
Admitted.

Lemma dombi_soundness (e : expr (Bool_N)) b :
   [[ e ]]_d = [[ ldl_bool _ b ]]_d -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind' .
- move: b b0 => [] [] //=; lra.
- rewrite List.Forall_forall in H.
  rewrite [ [[ldl_bool _ b]]_d ]/=.
  move: b => [].
  + move/dombi_nary_inversion_andE1.
    rewrite /= big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    by apply: H  => //; rewrite ?h// -In_in mem_nth.
  + move/dombi_nary_inversion_andE0.
    rewrite /= big_map big_all.
    elim=>// i /eqP i0 isize.
    apply/allPn; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    by rewrite -In_in mem_nth.
- rewrite List.Forall_forall in H.
  rewrite [ [[ldl_bool _ b]]_d]/=.
  move: b => [].
  + move/dombi_nary_inversion_orE1.
    rewrite /= big_map big_has.
    elim=>// i /eqP i0 isize.
    apply/hasP; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
  + move/dombi_nary_inversion_orE0.
    rewrite /= big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    by apply/negPf; apply: H => //; rewrite ?h// -In_in mem_nth.
- move=>/=h; rewrite (IHe e erefl JMeq_refl (~~ b)) ?negbK//.
  move: h. case: b => /=. admit. admit.
- case: c; rewrite //=; rewrite -!dombi_translations_Real_coincide;
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
Admitted.

End dombi_lemmas.