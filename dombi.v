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

Lemma translations_Fun_coincide:
  forall n m (e : expr (Fun_T n m)), [[ e ]]_d = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  [[ e ]]_d = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ v1 v2 _ e2 erefl JMeq_refl).
Qed.

Lemma translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_d = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma translations_Real_coincide (e : expr Real_T):
  [[ e ]]_d = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite translations_Vector_coincide translations_Index_coincide.
Qed.

Lemma translate_Bool_T_01 (e : expr Bool_N) :
  0 <= [[ e ]]_d <= 1.
Proof.
dependent induction e using expr_ind'.
- rewrite /=; case b; lra.
- move: H. rewrite /=; move=> /List.Forall_forall H.
  rewrite /sumR; apply/andP; split.
  + Search (0 <= _%E ^ _).  admit.
  + admit.

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