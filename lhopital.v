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

Definition derivable_at_right {R : numFieldType} {V W : normedModType R}
    (f : V -> W) a v :=
  cvg ((fun h => h^-1 *: ((f \o shift a) (h *: v) - f a)) @ 0^'+).

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
  by apply: cvgB; [exact: cf|apply: cvgM; [exact: cvg_cst|exact: cg]].
have /(Rolle ab hder ch)[x xab derh] : h a = h b.
  rewrite /h; apply/eqP; rewrite subr_eq eq_sym -addrA eq_sym addrC -subr_eq.
  rewrite -mulrN -mulrDr -(addrC (g a)) -[X in _ * X]opprB mulrN -mulrA.
  by rewrite mulVf// mulr1 opprB.
pose dh (x : R^o) := df x - (f b - f a) / (g b - g a) * dg x.
have his_der y : y \in `]a, b[%R -> is_derive x 1 h (dh x).
  by move=> yab; apply: is_deriveB; [exact: fdf|apply: is_deriveZ; exact: gdg].
exists x => //.
have := @derive_val _ R^o _ _ _ _ _ (his_der _ xab).
have -> := @derive_val _ R^o _ _ _ _ _ derh.
move=> /eqP; rewrite eq_sym subr_eq add0r => /eqP ->.
by rewrite -mulrA divff ?mulr1//; exact: dg0.
Qed.

End Cauchy_MVT.

Section lhopital.
Context {R : realType}.
Variables (f df g dg : R -> R) (a : R) (U : set R) (Ua : nbhs a U).
Hypotheses (fdf : forall x, x \in U -> is_derive x 1 f (df x))
           (gdg : forall x, x \in U -> is_derive x 1 g (dg x)).
Hypotheses (fa0 : f a = 0) (ga0 : g a = 0)
           (cdg : \forall x \near a^', dg x != 0).

Lemma lhopital_right (l : R) :
  df x / dg x @[x --> a^'+] --> l -> f x / g x @[x --> a^'+] --> l.
Proof.
case: cdg => r/= r0 cdg'.
move: Ua; rewrite filter_of_nearI => -[D /= D0 aDU].
near a^'+ => b.
have abf x : x \in `]a, b[%R -> {within `[a, x], continuous f}.
  rewrite in_itv/= => /andP[ax xb].
  apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[ay yx].
  apply: ex_derive.
  apply: fdf.
  rewrite inE; apply: aDU => /=.
  rewrite ler0_norm? subr_le0//.
  rewrite opprD opprK addrC ltrBlDr (le_lt_trans yx)// (lt_trans xb)//.
  near: b; apply: nbhs_right_lt.
  by rewrite ltrDr.
have abg x : x \in `]a, b[%R -> {within `[a, x], continuous g}.
  rewrite in_itv/= => /andP[ax xb].
  apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[ay yx].
  apply: ex_derive.
  apply: gdg.
  rewrite inE; apply: aDU => /=.
  rewrite ler0_norm? subr_le0//.
  rewrite opprD opprK addrC ltrBlDr (le_lt_trans yx)// (lt_trans xb)//.
  near: b; apply: nbhs_right_lt.
  by rewrite ltrDr.
have fdf' y : y \in `]a, b[%R -> is_derive y 1 f (df y).
  rewrite in_itv/= => /andP[ay yb]; apply: fdf.
  rewrite inE; apply: aDU => /=.
  rewrite ltr0_norm ?subr_lt0//.
  rewrite opprD opprK addrC ltrBlDr (lt_le_trans yb)//.
  near: b; apply: nbhs_right_le.
  by rewrite ltrDr.
have gdg' y : y \in `]a, b[%R -> is_derive y 1 g (dg y).
  rewrite in_itv/= => /andP[ay yb]; apply: gdg.
  rewrite inE; apply: aDU => /=.
  rewrite ltr0_norm ?subr_lt0//.
  rewrite opprD opprK addrC ltrBlDr (lt_le_trans yb)//.
  near: b; apply: nbhs_right_le.
  by rewrite ltrDr.
have {}dg0 y : y \in `]a, b[%R -> dg y != 0.
  rewrite in_itv/= => /andP[ay yb].
  apply: (cdg' y) => /=; last by rewrite gt_eqF.
  rewrite ltr0_norm; last by rewrite subr_lt0.
  rewrite opprB ltrBlDl (lt_trans yb)//.
  near: b; apply: nbhs_right_lt.
  by rewrite ltrDl.
move=> fgal.
have L : \forall x \near a^'+,
  exists2 c, c \in `]a, x[%R & df c / dg c = f x / g x.
  near=> x.
  have /andP[ax xb] : a < x < b by exact/andP.
  have {}fdf' y : y \in `]a, x[%R -> is_derive y 1 f (df y).
    rewrite !in_itv/= => /andP[ay yx].
    by apply: fdf'; rewrite in_itv/= ay/= (lt_trans yx).
  have {}gdg' y : y \in `]a, x[%R -> is_derive y 1 g (dg y).
    rewrite !in_itv/= => /andP[ay yx].
    by apply: gdg'; rewrite in_itv/= ay/= (lt_trans yx).
  have {}dg0 y : y \in `]a, x[%R -> dg y != 0.
    rewrite in_itv/= => /andP[ya yx].
    by apply: dg0; rewrite in_itv/= ya/= (lt_trans yx).
  have {}axf : {within `[a, x], continuous f}.
    rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[ay yx].
    by apply: abf; rewrite in_itv/= xb andbT.
  have {}axg : {within `[a, x], continuous g}.
    rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[ay yx].
    by apply: abg; rewrite in_itv/= xb andbT.
  have := @cauchy_MVT _ f df g dg _ _ ax axf axg fdf' gdg' dg0.
  by rewrite fa0 ga0 2!subr0.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : fgal.
move=> /(_ _ e0)[r'/= r'0 fagl].
case: L => d /= d0 L.
near=> t.
have /= := L t.
have atd : `|a - t| < d.
  rewrite ltr0_norm; last by rewrite subr_lt0.
  rewrite opprB ltrBlDl.
  near: t; apply: nbhs_right_lt.
  by rewrite ltrDl.
have at_ : a < t by [].
move=> /(_ atd)/(_ at_)[c]; rewrite in_itv/= => /andP[ac ct <-].
apply: fagl => //=.
rewrite ltr0_norm; last by rewrite subr_lt0.
rewrite opprB ltrBlDl (lt_trans ct)//.
near: t; apply: nbhs_right_lt.
by rewrite ltrDl.
Unshelve. all: by end_near. Qed.

Lemma lhopital_left (l : R) :
  df x / dg x @[x --> a^'-] --> l -> f x / g x @[x --> a^'-] --> l.
Proof.
case: cdg => r/= r0 cdg'.
move: Ua; rewrite filter_of_nearI => -[D /= D0 aDU].
near a^'- => b.
have baf x : x \in `]b, a[%R -> {within `[x, a], continuous f}.
  rewrite in_itv/= => /andP[bx xa].
  apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[xy ya].
  apply: ex_derive.
  apply: fdf.
  rewrite inE; apply: aDU => /=.
  rewrite ger0_norm ?subr_ge0//.
  rewrite ltrBlDr -ltrBlDl (lt_le_trans _ xy)// (le_lt_trans _ bx)//.
  near: b; apply: nbhs_left_ge.
  by rewrite ltrBlDl ltrDr.
have bag x : x \in `]b, a[%R -> {within `[x, a], continuous g}.
  rewrite in_itv/= => /andP[bx xa].
  apply: derivable_within_continuous => y; rewrite in_itv/= => /andP[xy ya].
  apply: ex_derive.
  apply: gdg.
  rewrite inE; apply: aDU => /=.
  rewrite ger0_norm ?subr_ge0//.
  rewrite ltrBlDr -ltrBlDl (lt_le_trans _ xy)// (lt_trans _ bx)//.
  near: b; apply: nbhs_left_gt.
  by rewrite ltrBlDl ltrDr.
have fdf' y : y \in `]b, a[%R -> is_derive y 1 f (df y).
  rewrite in_itv/= => /andP[by_ ya]; apply: fdf.
  rewrite inE.
  apply: aDU => /=.
  rewrite gtr0_norm ?subr_gt0//.
  rewrite ltrBlDl -ltrBlDr (le_lt_trans _ by_)//.
  near: b; apply: nbhs_left_ge.
  by rewrite ltrBlDr ltrDl.
have gdg' y : y \in `]b, a[%R -> is_derive y 1 g (dg y).
  rewrite in_itv/= => /andP[by_ ya]; apply: gdg.
  rewrite inE; apply: aDU => /=.
  rewrite gtr0_norm ?subr_gt0//.
  rewrite ltrBlDl -ltrBlDr (le_lt_trans _ by_)//.
  near: b; apply: nbhs_left_ge.
  by rewrite ltrBlDr ltrDl.
have {}dg0 y : y \in `]b, a[%R -> dg y != 0.
  rewrite in_itv/= => /andP[by_ ya].
  apply: (cdg' y) => /=; last by rewrite lt_eqF.
  rewrite gtr0_norm; last by rewrite subr_gt0.
  rewrite ltrBlDr -ltrBlDl (lt_trans _ by_)//.
  near: b; apply: nbhs_left_gt.
  by rewrite ltrBlDl ltrDr.
move=> fgal.
have L : \forall x \near a^'-,
  exists2 c, c \in `]x, a[%R & df c / dg c = f x / g x.
  near=> x.
  have /andP[bx xa] : b < x < a by exact/andP.
  have {}fdf' y : y \in `]x, a[%R -> is_derive y 1 f (df y).
    rewrite in_itv/= => /andP[xy ya].
    by apply: fdf'; rewrite in_itv/= ya andbT (lt_trans bx).
  have {}gdg' y : y \in `]x, a[%R -> is_derive y 1 g (dg y).
    rewrite in_itv/= => /andP[xy ya].
    by apply: gdg'; rewrite in_itv/= ya andbT (lt_trans _ xy).
  have {}dg0 y : y \in `]x, a[%R -> dg y != 0.
    rewrite in_itv/= => /andP[xy ya].
    by apply: dg0; rewrite in_itv/= ya andbT (lt_trans bx).
  have {}xaf : {within `[x, a], continuous f}.
    rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[xy ya].
    by apply: baf; rewrite in_itv/= bx.
  have {}xag : {within `[x, a], continuous g}.
    rewrite continuous_subspace_in => y; rewrite inE/= in_itv/= => /andP[xy ya].
    by apply: bag; rewrite in_itv/= bx.
  have := @cauchy_MVT _ f df g dg _ _ xa xaf xag fdf' gdg' dg0.
  by rewrite fa0 ga0 !sub0r divrN mulNr opprK.
apply/cvgrPdist_le => /= e e0.
move/cvgrPdist_le : fgal.
move=> /(_ _ e0)[r'/= r'0 fagl].
case: L => d /= d0 L.
near=> t.
have /= := L t.
have atd : `|a - t| < d.
  rewrite gtr0_norm; last by rewrite subr_gt0.
  rewrite ltrBlDr -ltrBlDl.
  near: t; apply: nbhs_left_gt.
  by rewrite ltrBlDl ltrDr.
have ta : t < a by [].
move=> /(_ atd)/(_ ta)[c]; rewrite in_itv/= => /andP[tc ca <-].
apply: fagl => //=.
rewrite gtr0_norm; last by rewrite subr_gt0.
rewrite ltrBlDr -ltrBlDl (lt_trans _ tc)//.
near: t; apply: nbhs_left_gt.
by rewrite ltrBlDl ltrDr.
Unshelve. all: by end_near. Qed.

End lhopital.
