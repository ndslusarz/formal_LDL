From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum matrix interval.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import reals signed topology prodnormedzmodule.
From mathcomp Require Import normedtype landau forms derive.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldNormedType.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Cauchy_MVT.
Context {R : realType}.
Variables (f df g dg : R -> R) (a b c : R).
Hypothesis ab : a < b.
Hypotheses (cf : {within `[a, b], continuous f})
           (cg : {within `[a, b], continuous g}).
Hypotheses (fdf : forall x, x \in `]a, b[%R -> is_derive x 1 f (df x))
           (gdg : forall x, x \in `]a, b[%R -> is_derive x 1 g (dg x)).
Hypotheses (dg0 : forall x, x \in `]a, b[%R -> dg x != 0).

Lemma cauchy_MVT :
  exists2 c, c \in `]a, b[%R & df c / dg c = (f b - f a) / (g b - g a).
Proof.
have [r] := MVT ab gdg cg; rewrite in_itv/= => /andP[ar rb] dgg.
have gba0 : g b - g a != 0.
  by rewrite dgg mulf_neq0 ?dg0 ?in_itv/= ?ar// subr_eq0 gt_eqF.
pose h (x : R^o) := f x - ((f b - f a) / (g b - g a)) * g x.
have hder x : x \in `]a, b[%R -> derivable h x 1.
  move=> xab; apply: derivableB => /=.
    exact: (@ex_derive _ _ _ _ _ _ _ (fdf xab)).
  by apply: derivableM => //; exact: (@ex_derive _ _ _ _ _ _ _ (gdg xab)).
have ch : {within `[a, b], continuous h}.
  rewrite continuous_subspace_in => x xab.
  apply: cvgB.
    apply: cf.
  apply: cvgM.
    apply: cvg_cst.
  apply: cg.
have : h a = h b.
  rewrite /h; apply/eqP; rewrite subr_eq eq_sym -addrA eq_sym addrC -subr_eq.
  apply/eqP; rewrite [RHS]addrC -mulrBr -[in RHS](opprB (g a)) divrN -mulNr.
  by rewrite -mulrA mulVf ?mulr1 ?opprB// subr_eq0 eq_sym -subr_eq0.
move=> /(Rolle ab hder ch)[x xab derh].
pose dh (x : R^o) := df x - (f b - f a) / (g b - g a) * dg x.
have : forall x, x \in `]a, b[%R -> is_derive x 1 h (dh x).
  move=> y yab.
  apply: is_deriveB.
    by apply: fdf.
  apply: is_deriveZ.
  by apply: gdg.
exists x => //.
have hdh := H _ xab.
have := @derive_val _ R^o _ _ _ _ _ hdh.
have -> := @derive_val _ R^o _ _ _ _ _ derh.
rewrite /dh => /eqP.
rewrite eq_sym subr_eq add0r => /eqP ->.
rewrite -mulrA divff ?mulr1//.
exact: dg0.
Qed.

End Cauchy_MVT.

Definition derivable_at_right {R : numFieldType} {V W : normedModType R}
    (f : V -> W) a v :=
  cvg ((fun h => h^-1 *: ((f \o shift a) (h *: v) - f a)) @ 0^'+).

Section lhopital.
Context {R : realType}.
Variables (f df g dg : R -> R) (a u v : R).
Hypothesis uav : u < a < v.
Hypotheses (fdf : forall x, x \in `]u, v[%R -> is_derive x 1 f (df x))
           (gdg : forall x, x \in `]u, v[%R -> is_derive x 1 g (dg x)).
Hypotheses (fa0 : f a = 0) (ga0 : g a = 0)
           (cdg : \forall x \near a^', dg x != 0).

Lemma lhopital (l : R) : derivable_at_right f a 1 -> derivable_at_right g a 1 ->
  df x / dg x @[x --> a^'+] --> l -> f x / g x @[x --> a^'+] --> l.
Proof.
move=> fa ga.
case/andP: uav => ua av.
case: cdg => r/= r0 cdg'.
near a^'+ => b.
have bv : b < v.
  near: b.
  by apply: nbhs_right_lt.
  have H1 : forall x, x \in `]a, b[%R -> {within `[a, x], continuous f}.
    move=> x; rewrite in_itv/= => /andP[ax xb].
    apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[ay yx].
    apply: ex_derive.
    apply: fdf.
    rewrite in_itv/=.
    apply/andP; split.
      by rewrite (lt_le_trans ua).
    rewrite (le_lt_trans _ bv)//.
    by rewrite (le_trans yx)// ltW.
  have H2 : forall x, x \in `]a, b[%R -> {within `[a, x], continuous g}.
    move=> x; rewrite in_itv/= => /andP[ax xb].
    apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[ay yx].
    apply: ex_derive.
    apply: gdg.
    rewrite in_itv/=.
    apply/andP; split.
      by rewrite (lt_le_trans ua).
    rewrite (le_lt_trans _ bv)//.
    by rewrite (le_trans yx)// ltW.
  have fdf' : forall y, y \in `]a, b[%R -> is_derive y 1 f (df y).
    move=> y; rewrite in_itv/= => /andP[ay yb]; apply: fdf; rewrite in_itv/=.
    by rewrite (lt_trans ua)//= (lt_trans _ bv).
  have gdg' : forall y, y \in `]a, b[%R -> is_derive y 1 g (dg y).
    move=> y; rewrite in_itv/= => /andP[ay yb]; apply: gdg; rewrite in_itv/=.
    by rewrite (lt_trans ua)//= (lt_trans _ bv).
  have {}dg0 : forall y, y \in `]a, b[%R -> dg y != 0.
    move=> y; rewrite in_itv/= => /andP[ay yb].
    have := cdg' y; apply.
      rewrite /=.
      rewrite ltr0_norm; last first.
        by rewrite subr_lt0.
      rewrite opprB.
      rewrite ltrBlDl.
      rewrite (lt_trans yb)//.
      near: b.
      apply: nbhs_right_lt.
      by rewrite ltrDl.
    by rewrite gt_eqF.
  move=> fgal.
  have L : \forall x \near a^'+,
    exists2 c, c \in `]a, x[%R & df c / dg c = f x / g x.
    near=> x.
    have /andP[ax xb] : a < x < b.
      by apply/andP; split => //.
    have {}fdf' : forall y, y \in `]a, x[%R -> is_derive y 1 f (df y).
      move=> y yax.
      apply: fdf'.
      move: yax.
      rewrite !in_itv/= => /andP[->/= yx].
      by rewrite (lt_trans _ xb).
    have {}gdg' : forall y, y \in `]a, x[%R -> is_derive y 1 g (dg y).
      move=> y yax.
      apply: gdg'.
      move: yax.
      rewrite !in_itv/= => /andP[->/= yx].
      by rewrite (lt_trans _ xb).
    have {}dg0 : forall y, y \in `]a, x[%R -> dg y != 0.
      move=> y.
      rewrite in_itv/= => /andP[ya yx].
      apply: dg0.
      by rewrite in_itv/= ya/= (lt_trans yx).
    have {}H1 : {within `[a, x], continuous f}.
      rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[ay yx].
      apply: H1.
      by rewrite in_itv/= xb andbT.
    have {}H2 : {within `[a, x], continuous g}.
      rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[ay yx].
      apply: H2.
      by rewrite in_itv/= xb andbT.
    have := @cauchy_MVT _ f df g dg _ _ ax H1 H2 fdf' gdg' dg0.
    rewrite fa0 ga0 2!subr0.
    exact.
  apply/cvgrPdist_le => /= e e0.
  move/cvgrPdist_le : fgal.
  move=> /(_ _ e0)[r'/= r'0 fagl].
  case: L => d /= d0 L.
  near=> t.
  have /= := L t.
  have L1 : `|a - t| < d.
    rewrite ltr0_norm; last first.
      by rewrite subr_lt0//.
    rewrite opprB.
    rewrite ltrBlDl.
    near: t.
    apply: nbhs_right_lt.
    by rewrite ltrDl.
  have L2 : a < t.
    done.
  move=> /(_ L1)/(_ L2)[c cat <-].
  apply: fagl.
    rewrite /=.
    rewrite ltr0_norm; last first.
      rewrite subr_lt0.
      rewrite in_itv/= in cat.
      by case/andP : cat.
    rewrite opprB.
    rewrite ltrBlDl.
    rewrite in_itv/= in cat.
    case/andP : cat => _ ct.
    rewrite (lt_trans ct)//.
    near: t.
    apply: nbhs_right_lt.
    by rewrite ltrDl.
  rewrite in_itv/= in cat.
  by case/andP : cat.
Unshelve. all: by end_near. Qed.

End lhopital.
