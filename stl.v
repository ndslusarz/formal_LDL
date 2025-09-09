From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences exp measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral hoelder realfun.
Require Import mathcomp_extra analysis_extra ldl.

(**md**************************************************************************)
(* # STL alternative                                                          *)
(*                                                                            *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldNormedType.Exports.

HB.instance Definition _ (R : realType)  f1 f2 f3 f4 :=
  @gen_eqMixin (@expr R (boolT f1 f2 f3 f4)).

Section stl_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable nu : R.
Hypothesis nu0 : 0 < nu.

Lemma andI_stl (e : expr (boolT_def impl_undef m_undef l_def)) :
  nu.-[[e `/\ e]]_stl = nu.-[[e]]_stl.
Proof.
rewrite /= /stl_and /stl_and_gt0 /stl_and_lt0 /min_dev.
rewrite !big_ord_recl !big_ord0/= !tnthS !tnth0/= !minrxyx.
set a_min := minr (nu.-[[e]]_stl) (nu.-[[e]]_stl).
set a := (nu.-[[e]]_stl - a_min) * a_min^-1.
have a_min_e : a_min = nu.-[[e]]_stl.
  by rewrite /a_min /minr; repeat case: ifPn => //; rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0.
  by rewrite /a a_min_e subrr ?mul0r.
rewrite !addr0 !mulr0 expR0 !mulr1/= a_min_e.
have -> : ((nu.-[[e]]_stl + nu.-[[e]]_stl) * (1 + 1)^-1) = nu.-[[e]]_stl.
  have -> : 1 + 1 = (2 : R) by lra.
  by rewrite mulrDl -splitr.
case: ifPn => //h1.
case: ifPn => //h2.
by apply le_anti; rewrite !leNgt; rewrite h1 h2.
Qed.

Lemma andC_stl (e1 e2 : expr (boolT_def impl_undef m_undef l_def)) :
  nu.-[[e1 `/\ e2]]_stl = nu.-[[e2 `/\ e1]]_stl.
Proof.
rewrite /= /stl_and /stl_and_gt0 /stl_and_lt0 /min_dev.
rewrite !big_ord_recl !big_ord0/= !tnthS !tnth0 !addr0/=.
set a_min := minr (nu.-[[e1]]_stl) (minr (nu.-[[e2]]_stl) (nu.-[[e1]]_stl)).
have -> : minr (nu.-[[e2]]_stl) (minr (nu.-[[e1]]_stl) (nu.-[[e2]]_stl)) = a_min.
  by rewrite /a_min/minr; repeat case: ifPn => //; lra.
set a1 := (nu.-[[e1]]_stl - a_min) * a_min^-1.
set a2 := (nu.-[[e2]]_stl - a_min) * a_min^-1.
case: ifPn; first by rewrite [X in X / _]addrC [X in _ / X]addrC.
case: ifPn; first by rewrite addrC (addrC (expR (- nu * a1)) (expR (- nu * a2))) .
lra.
Qed.

Lemma orI_stl (e : expr (boolT_def impl_undef m_undef l_def)) :
  nu.-[[e `\/ e]]_stl = nu.-[[e]]_stl.
Proof.
rewrite /= /stl_or /stl_or_gt0 /stl_or_lt0 /max_dev !big_ord_recl !big_ord0/= !tnthS !tnth0.
rewrite !addr0 !maxrxyx.
set a_max := maxr (nu.-[[e]]_stl) (nu.-[[e]]_stl).
set a :=  ((a_max - nu.-[[e]]_stl) / a_max).
have a_max_e : a_max = nu.-[[e]]_stl.
  by rewrite /a_max /maxr; repeat case: ifPn => //; rewrite -leNgt leye_eq => /eqP ->.
have -> : a = 0.
  by rewrite /a a_max_e subrr ?mul0r.
rewrite !mulr0 expR0 !mulr1/= a_max_e.
have -> : ((nu.-[[e]]_stl + nu.-[[e]]_stl) * (1 + 1)^-1) = nu.-[[e]]_stl.
  have -> : 1 + 1 = (2 : R) by lra.
  by rewrite mulrDl -splitr.
case: ifPn => //h1.
case: ifPn => //h2.
by apply le_anti; rewrite !leNgt h1 h2.
Qed.

Lemma orC_stl (e1 e2 : expr (boolT_def impl_undef m_undef l_def)) :
  nu.-[[e1 `\/ e2]]_stl  = nu.-[[e2 `\/ e1]]_stl.
Proof.
rewrite /= /stl_or /stl_or_gt0 /stl_or_lt0 /max_dev !big_ord_recl !big_ord0/= !tnthS !tnth0.
rewrite !addr0.
set a_max := maxr (nu.-[[e1]]_stl) (maxr (nu.-[[e2]]_stl) (nu.-[[e1]]_stl)).
have -> : maxr (nu.-[[e2]]_stl) (maxr (nu.-[[e1]]_stl) (nu.-[[e2]]_stl)) = a_max.
  by rewrite /a_max/maxr; repeat case: ifPn => //; lra.
set a1 := (a_max - nu.-[[e1]]_stl) * a_max^-1.
set a2 := (a_max - nu.-[[e2]]_stl) * a_max^-1.
set d1 := expR (nu * a1) + expR (nu * a2).
have -> : expR (nu * a2) + expR (nu * a1) = d1 by rewrite addrC.
case: ifPn; first by rewrite addrC.
by case: ifPn; first by rewrite addrC.
Qed.

Lemma stl_translations_coincide t (e : @expr R t) n m j :
  (t = realT \/ t = vectorT n \/ t = indexT n \/ t = funT n m \/ t = fun2T n m j) ->
  nu.-[[ e ]]_stl ~= [[ e ]]_B.
Proof.
dependent induction e using expr_ind' => //=; move=> [|[|[|[|]]]]t0//.
- rewrite (JMeq_eq (IHe1 n m j _)); last by (right; right; right; left).
  by rewrite (JMeq_eq (IHe2 n m j _)); last by (right; left).
- rewrite (JMeq_eq (IHe1 n m l _)); last by (right; right; right; right).
  rewrite (JMeq_eq (IHe2 n m l _)); last by (right; left).
  by rewrite (JMeq_eq (IHe3 m n l _)); last by (right; left).
- rewrite (JMeq_eq (IHe1 n m j _)); last by (right; left).
  by rewrite (JMeq_eq (IHe2 n m j _)); last by (right; right; left).
Qed.

Lemma stl_translations_Fun_coincide n m (e : expr (funT n m)) :
  nu.-[[ e ]]_stl = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(stl_translations_coincide _ _ n m 0); right;right;right;left.
Qed.

Lemma stl_translations_Vector_coincide n (e : @expr R (vectorT n)) :
  nu.-[[ e ]]_stl = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(stl_translations_coincide _ _ n 0 0); right;left.
Qed.

Lemma stl_translations_Index_coincide n (e : expr (indexT n)) :
  nu.-[[ e ]]_stl = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(stl_translations_coincide _ _ n 0 0); right;right;left.
Qed.

Lemma stl_translations_Real_coincide (e : expr realT):
  nu.-[[ e ]]_stl = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(stl_translations_coincide _ _ 0 0 0); left.
Qed.

Definition is_stl b (x : R) := if b then x >= 0 else x < 0.

Lemma stl_nary_inversion_andE1 n (Es : 'I_n -> (expr (boolT_undef impl_undef m_undef l_def))) :
  is_stl true (nu.-[[ ldl_and Es ]]_stl) ->
    forall i, is_stl true (nu.-[[ Es i ]]_stl).
Proof.
move: Es; case: n => [Es _|n Es]; first by case.
rewrite /is_stl /= /stl_and /stl_and_gt0 /stl_and_lt0 /min_dev.
set a_min := \big[minr/nu.-[[Es ord0]]_stl]_(i < n.+1) nu.-[[Es i]]_stl.
case: ifPn=>[hminlt0|].
  rewrite pmulr_lge0; last first.
    by rewrite invr_gt0// sumr_gt0//; exists ord0; split; rewrite ?mem_index_enum// expR_gt0.
  rewrite leNgt sumr_lt0//=.
    by move => i _ _; rewrite -mulrA !nmulr_rle0 ?expR_ge0// (le_lt_trans _ hminlt0).
  by exists ord0; rewrite mem_index_enum !nmulr_rlt0 ?expR_gt0.
rewrite -leNgt; move/bigmin_geP =>/= [h0 hi].
by case: ifPn => _ _ i; exact/hi.
Qed.

Lemma stl_nary_inversion_andE0 n (Es : 'I_n -> (expr (boolT_undef impl_undef m_undef l_def))) :
  is_stl false (nu.-[[ ldl_and Es ]]_stl) ->
    exists i, is_stl false (nu.-[[ Es i ]]_stl).
Proof.
move: Es; case: n => [Es|n Es]//=; first by rewrite ltr10.
rewrite /is_stl /= /stl_and /=.
set a_min := \big[minr/nu.-[[Es ord0]]_stl]_(i < n.+1) nu.-[[Es i]]_stl.
case: ifPn=>[hminlt0 _|].
  have [x xmem hlt0] := minrltx hminlt0.
  by exists x.
rewrite -leNgt => hminge0.
case: ifPn => _; last by rewrite ltxx.
rewrite ltNge divr_ge0// big_ord_recl/= addr_ge0//= ?mulr_ge0 ?expR_ge0 ?sumr_ge0//=.
  by apply: (minrgex hminge0); rewrite mem_head.
by move=> i _; rewrite mulr_ge0// (le_trans hminge0)// bigmin_le.
Qed.

Lemma stl_nary_inversion_orE1 n (Es : 'I_n -> (expr (boolT_undef impl_undef m_undef l_def))) :
  is_stl true (nu.-[[ ldl_or Es ]]_stl) ->
    exists i, is_stl true (nu.-[[ Es i ]]_stl).
Proof.
move: Es; case: n => [Es|n Es]/=; first by rewrite /= ler0N1.
rewrite/is_stl/= /stl_or/stl_or_gt0/stl_or_lt0 /max_dev.
set a_max := \big[maxr/nu.-[[Es ord0]]_stl]_(i < n.+1) nu.-[[Es i]]_stl.
case: ifPn=> [hmaxgt0 _|].
  have [x xmem hgt0] := maxrgtx hmaxgt0.
  by exists x; exact/ltW.
rewrite -leNgt => hmaxle0.
case: ifPn=>[hmaxlt0|].
  rewrite leNgt nmulr_rlt0.
    by rewrite invr_gt0 sumr_gt0//; exists ord0; rewrite mem_index_enum expR_gt0.
  rewrite sumr_lt0//.
    by move=> i _ _; rewrite nmulr_rle0//= (le_lt_trans _ hmaxlt0)// le_bigmax.
  by exists ord0; rewrite mem_index_enum nmulr_rlt0 ?expR_gt0//= (le_lt_trans _ hmaxlt0)// le_bigmax.
rewrite -leNgt => hmaxge0 _.
have /= [x xmem hxge0] := maxrgex hmaxge0.
by exists x.
Qed.

Lemma stl_nary_inversion_orE0 n (Es : 'I_n -> (expr (boolT_undef impl_undef m_undef l_def))) :
  is_stl false (nu.-[[ ldl_or Es ]]_stl) ->
    forall i, is_stl false (nu.-[[ Es i ]]_stl).
Proof.
move: Es; case: n => [Es _|n Es]; first by case.
rewrite/is_stl/= /stl_or/stl_or_gt0/stl_or_lt0.
set a_max := \big[maxr/nu.-[[Es ord0]]_stl]_(i < n.+1) nu.-[[Es i]]_stl.
case: ifPn=>[hmaxgt0|].
  rewrite ltNge divr_ge0// sumr_ge0//= => i _.
  by rewrite !mulr_ge0// ltW.
rewrite -leNgt => h.
case: ifPn; last by rewrite ltxx.
move => hmaxlt0 _ i.
by rewrite (le_lt_trans _ hmaxlt0)// le_bigmax.
Qed.

Lemma stl_adequacy (e : expr (boolT_undef impl_undef m_undef l_def)) b :
  is_stl b (nu.-[[ e ]]_stl) -> [[ e ]]_B = b.
Proof.
dependent induction e using expr_ind'.
- by move: b b0 => [] [] //=; rewrite ?leNgt ?ltrN10 ?ltr10.
- move: b => []. rewrite /is_stl.
  + move/stl_nary_inversion_andE1.
    rewrite [bool_translation (ldl_and l)]/= big_all => h.
    by apply/allP => /= i _; exact/H.
  + move/stl_nary_inversion_andE0.
    rewrite [bool_translation (ldl_and l)]/= big_all => [ [i] h].
    apply/allPn; exists i; first by rewrite mem_index_enum.
    by rewrite (H i _ _ _ false).
- move: b => [|].
  + move/stl_nary_inversion_orE1.
    rewrite [bool_translation (ldl_or l)]/= big_has => [ [i] h].
    apply/hasP; exists i; first by rewrite mem_index_enum.
    exact: H.
  + move/stl_nary_inversion_orE0.
    rewrite [bool_translation (ldl_or l)]/= big_has => h.
    apply/hasPn => i _.
    by rewrite (H i _ _ _ false).
- case: c.
  + by case: b; rewrite /is_stl/= ?lee_fin ?lte_fin ?ltNge subr_ge0 !stl_translations_Real_coincide// => /negbTE.
  + case: b; rewrite /is_stl/= ?lee_fin ?lte_fin !stl_translations_Real_coincide.
    by rewrite oppr_ge0 normr_le0 subr_eq0.
    by rewrite oppr_lt0 normr_gt0 subr_eq0 => /negbTE.
Qed.

From mathcomp Require Import perm.

Lemma andC_stl_nary n (s1 s2 : 'I_n -> (expr (boolT_def impl_undef m_undef l_def))) :
  (exists pi : {perm 'I_n}, s1 = s2 \o pi) -> nu.-[[ldl_and s1]]_stl = nu.-[[ldl_and s2]]_stl.
(* Proof. *)
(* case: s1; first by rewrite perm_sym => /perm_nilP ->. *)
(* move=> a1 l1; case: s2; first by move/perm_nilP. *)
(* move=> a2 l2 pi. *)
(* rewrite /=. *)
(* have pi2 := @perm_map _ _ (stl_translation nu) _ _ pi. *)
(* rewrite (perm_eq_big_min pi2)/=. *)
(* rewrite /stl_and/= !big_map !map_cons. *)
(* case: ifPn => // ?. *)
(*   rewrite /stl_and_lt0 !big_map. *)
(*   congr (_ / _). *)
(*     rewrite (perm_big _ pi)/=. *)
(*     apply: eq_bigr => i _. *)
(*     congr (_ * _). *)
(*       congr(_ * _). *)
(*         rewrite !map_cons !big_map. *)
(*         exact: perm_big. *)
(*       by rewrite !map_cons /min_dev !big_map (perm_big _ pi). *)
(*     by rewrite !map_cons /min_dev !big_map (perm_big _ pi). *)
(*   rewrite (perm_big _ pi)/=. *)
(*   apply: eq_bigr => i _. *)
(*   by rewrite !map_cons /min_dev !big_map (perm_big _ pi). *)
(* case: ifPn => // ?. *)
(* rewrite /stl_and_gt0 !big_map. *)
(* congr (_ / _). *)
(*   rewrite (perm_big _ pi)/=. *)
(*   apply: eq_bigr => i _. *)
(*   by rewrite /min_dev !map_cons !big_map (perm_big _ pi). *)
(* rewrite (perm_big _ pi)/=. *)
(* apply: eq_bigr => i _. *)
(* by rewrite /min_dev !map_cons !big_map (perm_big _ pi). *)
(* Qed. *)
Admitted.

End stl_lemmas.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Lemma cvg_sum {K : numFieldType} {V : pseudoMetricNormedZmodType K}
  {T : Type} (F : set_system T) (A : eqType) (v : seq A) (P : pred A) : Filter F ->
  forall (f : A -> T -> V) (a : V),
  (forall (i : A), P i ->  f i x @[x --> F] --> a) ->
  \sum_(i <- v | P i) f i x @[x --> F] --> \sum_(i <- v | P i) a.
Proof.
elim: v => [FF f a fa|h t IH FF f a fa].
  rewrite big_nil.
  under eq_fun do rewrite big_nil.
  exact: cvg_cst.
rewrite big_cons.
under eq_fun do rewrite big_cons.
case: ifPn => Ph.
  apply: cvgD.
    exact: fa.
  exact: IH.
exact: IH.
Qed.

Section stl_and_conv_lattice.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Context {R : realType}.

Lemma cvg_addrl_Ny (M : R) : M + r @[r --> -oo] --> -oo.
Proof.
move=> P [r [rreal rP]]; exists (r - M); split.
  by rewrite realB// num_real.
by move=> m/=; rewrite ltrBrDl => /rP.
Qed.

Variables (nu : R) (M : nat).

Local Notation seq_of_rV := (@MatrixFormula.seq_of_rV _ M.+1).

Lemma minr_le_l (x y : R) : minr x y <= x.
Proof. rewrite /minr; case: ifP; lra. Qed.

Lemma minr_le_r (x y : R)  : minr x y <= y.
Proof. rewrite /minr; case: ifP; lra. Qed.

Lemma minr_gt0 (x y : R) : 0 < x -> 0 < y -> 0 < minr x y.
Proof. move=> hx hy; rewrite /minr; case: ifP=> //= _; exact: hy. Qed.

Lemma min_dev_gt0 n (v : 'I_n.+1 -> R) i :
  (forall j, 0 < v j) ->
  v i != \big[minr/v ord0]_(j < n.+1) v j ->
  min_dev i v > 0.
Proof.
rewrite eq_le !negb_and -!ltNge /min_dev => h0 /orP[h1|h1].
  by rewrite pmulr_lgt0 ?invr_gt0 ?subr_gt0// lt_bigmin.
suff: \big[minr/v ord0]_(j < n.+1) v j <= v i by lra.
exact/bigmin_le.
Qed.

Lemma stl_and_gt0_cvg_infty (p : R) n (v : 'I_n.+1 -> R)  :
  (forall x, v x > 0) ->
  (stl_and_gt0 p v) @[p --> +oo] --> \big[minr/v ord0]_(i < n.+1) v i.
Proof.
move => vnil v0.
rewrite /stl_and_gt0.
set min_val := \big[minr/v ord0]_(i < n.+1) v i.
have sum_spl1 : forall (x : R),   \sum_(a < n.+1) v a * expR (- x * min_dev a v)
  =  \sum_(a < n.+1 | v a == min_val) v a  * expR (- x * min_dev a v)
    + \sum_(a < n.+1 | v a != min_val) v a * expR (- x * min_dev a v)
    by move => x0; exact/bigID.
(*top sum*)
have sum_top : (\sum_(a < n.+1) v a * expR (- p0 * min_dev a v)) @[p0 --> +oo] -->
              (min_val) * (\sum_(a < n.+1 | v a == min_val) 1).
  apply/cvgrPdist_le => /= e e0.
  near=> t.
  rewrite sum_spl1.
  near: t; move: e e0; apply/cvgrPdist_le.
  (*top sum non-minimum elements*)
  have sum_top_rest :
      (\sum_(a < n.+1 | v a != min_val) v a * expR (- t * min_dev a v))%R @[t --> +oo] --> 0.
    rewrite [X in _ --> X](_ : _ = \sum_(a < n.+1 | v a != min_val) 0); last by rewrite big1.
    apply/cvgrPdist_le => /= e e0.
    near=> t.
    rewrite big_seq_cond [X in _ - X]big_seq_cond.
    near: t; move: e e0; apply/cvgrPdist_le.
    apply: cvg_sum => a /andP [av amin].
    rewrite -(mulr0 (v a)).
    apply: cvgM => //.
      by exact: cvg_cst.
    under eq_fun do rewrite mulrC.
    apply: (@cvg_comp _ _ _ _ _ _ -oo).
      apply/gt0_cvgMrNy; first by rewrite min_dev_gt0 ?min_val_eq.
      exact/cvgNrNy.
    exact/cvgNy_compNP/cvgr_expR.
  rewrite -(addr0 (min_val * (\sum_(a < n.+1 | v a == min_val) 1))).
  apply: cvgD; last by exact sum_top_rest.
  apply/cvgrPdist_le => /= e e0.
  near=> t.
  near: t; move: e e0; apply/cvgrPdist_le.
  rewrite mulr_sumr mulr1 /min_dev.
  apply: cvg_sum => /=a /eqP ->.
  rewrite subrr mul0r.
  under eq_fun do rewrite mulr0 expR0 mulr1.
  exact: cvg_cst.
(*bottom sum*)
have sum_spl2 : forall (x : R), (\sum_(a < n.+1) expR (- x * min_dev a v))
  = \sum_(a < n.+1 | v a == min_val) expR (- x * min_dev a v)
    + \sum_(a < n.+1 | v a != min_val) expR (- x * min_dev a v)
    by move=> i; exact/bigID.
have sum_bot : (\sum_(a < n.+1) expR (- p0 * min_dev a v)) @[p0 --> +oo] -->
                 ((\sum_(a < n.+1 | v a == min_val) 1): R).
  apply/cvgrPdist_le => /= e e0.
  near=> t.
  rewrite sum_spl2.
  near: t; move: e e0; apply/cvgrPdist_le.
  (*top sum non-minimum elements*)
  have sum_bot_rest :
      (\sum_(a < n.+1 | v a != min_val)  expR (- t * min_dev a v))%R @[t --> +oo] --> 0.
    rewrite [X in _ --> X](_ : _ = \sum_(a < n.+1 | v a != min_val) 0); last by rewrite big1.
    apply/cvgrPdist_le => /= e e0.
    near=> t.
    rewrite big_seq_cond.
    rewrite [X in _ - X]big_seq_cond.
    near: t; move: e e0; apply/cvgrPdist_le.
    apply: cvg_sum => a /andP [av amin].
    under eq_fun do rewrite mulrC.
    apply: (@cvg_comp _ _ _ _ _ _ -oo).
      apply/gt0_cvgMrNy; first by rewrite min_dev_gt0 ?min_val_eq.
      exact/cvgNrNy/cvg_id.
    exact/cvgNy_compNP/cvgr_expR.
  rewrite -(addr0 ((\sum_(a < n.+1 | v a == min_val) 1))).
  apply: cvgD; last by exact sum_bot_rest.
  apply/cvgrPdist_le => /= e e0.
  near=> t.
  near: t; move: e e0; apply/cvgrPdist_le.
  rewrite /min_dev.
  apply: cvg_sum => i /eqP ->.
  rewrite subrr mul0r.
  under eq_fun do rewrite mulr0 expR0.
  exact: cvg_cst.
have gt0 : ((\sum_(a < n.+1 | v a == min_val) 1) : R) > 0.
  rewrite sumr_gt0//=.
  exists (extremum <=%R ord0 xpredT v).
  split => //; first by rewrite mem_index_enum.
  case: (@extremumP _ _ ler ord0 xpredT v lexx le_trans le_total isT) => i _/= h.
  by rewrite eq_le !le_bigmin ?h//= bigmin_le.
have sum_inv : (\sum_(a < n.+1) expR (- p0 * min_dev a v))^-1 @[p0 --> +oo] --> 
                  ((\sum_(a < n.+1 | v a == min_val) 1): R)^-1.
  apply: cvgV; first exact/lt0r_neq0. 
  exact/sum_bot.
have l :=  (@cvgM _ _ _ _ _ _ _ _ sum_top sum_inv).
rewrite -fctM in l.
have helper : min_val * (\sum_(a < n.+1 | v a == min_val) 1) / (\sum_(a < n.+1 | v a == min_val) 1) = min_val.
  rewrite mulrK//=.
  rewrite unitfE. 
  by apply lt0r_neq0; exact gt0.
rewrite helper in l.
apply: l.
Unshelve. all: end_near.
Qed.

Lemma min_dev_lt0 n (v : 'I_n.+1 -> R) :
  (exists i, v i < 0) ->
  forall i, v i != \big[minr/v ord0]_(j < n.+1) v j ->
  min_dev i v < 0.
Proof.
move=> [j Hpos] i Hvi.
have minlt0 : \big[minr/v ord0]_(i0 < n.+1) v i0 < 0 by apply/bigmin_ltP; right; exists j.
by rewrite mulr_lt0 subr_eq0 Hvi/= subr_lt0 lt_eqF ?invr_lt0//= ltNge bigmin_le.
Qed.

Lemma stl_and_lt0_cvg_infty (p : R) n (v : 'I_n.+1 -> R)  : 
  (exists x, v x < 0) ->
  (stl_and_lt0 p v) @[p --> +oo] --> \big[minr/v ord0]_(i < n.+1) v i.
Proof.
move => vnil v0.
rewrite /stl_and_lt0.
set (min_val := \big[minr/v ord0]_(i < n.+1) v i) in *.
have sum_spl1 : forall (x : R),
    \sum_(a < n.+1) \big[minr/v ord0]_(i < n.+1) v i * expR (min_dev a v) * expR (x * min_dev a v) =
      \sum_(a < n.+1 | v a == min_val) \big[minr/v ord0]_(i < n.+1) v i  * expR (min_dev a v) * expR (x * min_dev a v)
      + \sum_(a < n.+1 | v a != min_val) \big[minr/v ord0]_(i < n.+1) v i * expR (min_dev a v) * expR (x * min_dev a v).
  by move => x1; exact/bigID.
(*top sum*)
have sum_top :
  (\sum_(a < n.+1) \big[minr/v ord0]_(i < n.+1) v i * expR (min_dev a v) * expR (p0 * min_dev a v)) @[p0 --> +oo] --> 
    (min_val) * (\sum_(a < n.+1 | v a == min_val) 1). 
  apply/cvgrPdist_le => /= e e0.
  near=> t.
  rewrite sum_spl1.
  near: t; move: e e0; apply/cvgrPdist_le.
  (*top sum non-minimum elements*)
  have sum_top_rest :
      (\sum_(a < n.+1 | v a != min_val) \big[minr/v ord0]_(i < n.+1) v i * expR (min_dev a v)
       * expR (t * min_dev a v))%R @[t --> +oo] --> 0.
    rewrite [X in _ --> X](_ : _ = \sum_(a < n.+1 | v a != min_val) 0); last by rewrite big1.
    apply/cvgrPdist_le => /= e e0.
    near=> t.
    near: t; move: e e0; apply/cvgrPdist_le.
    apply: cvg_sum => a amin.
    rewrite -(mulr0 (\big[minr/v ord0]_(i < n.+1) v i)). 
    apply/cvgrPdist_le => /= e e0.
    near=> t.
    rewrite -mulrA -expRD.
    near: t; move: e e0; apply/cvgrPdist_le.
    apply: cvgM => //; first exact: cvg_cst.
    apply/(@cvg_comp _ _ _ _ _ _ -oo); last exact/cvgNy_compNP/cvgr_expR.
    apply/(@cvg_comp _ _ _ _ _ _ -oo); last exact/cvg_addrl_Ny.
    rewrite -cvgNry.
    under eq_cvg do rewrite -mulrN.
    apply: gt0_cvgMly => //.
    by rewrite oppr_gt0 min_dev_lt0.
  rewrite -(addr0 (min_val * (\sum_(a < n.+1 | v a == min_val) 1))).
  apply: cvgD; last by exact sum_top_rest.
  apply/cvgrPdist_le => /= e e0.
  near=> t.
  near: t; move: e e0; apply/cvgrPdist_le.
  rewrite [X in _ --> X](_ : _ = (\sum_(i < n.+1 | v i == min_val) min_val));
    last first.
  - rewrite -(mulr1 min_val) {1}mulr1. rewrite -mulr_sumr.
    by rewrite //; congr (_ * _); apply: eq_bigr => i _; rewrite natr1.
  - apply: cvg_sum => a /eqP amin.
    rewrite /min_dev amin subrr mul0r expR0 mulr1.
    under eq_fun do rewrite mulr0 !expR0 !mulr1.
    exact: cvg_cst.
(*bottom sum*)
have sum_spl2 : forall (x : R),   (\sum_(a < n.+1)  expR (x * min_dev a v))
  = \sum_(a < n.+1 | v a == min_val)  expR (x * min_dev a v)
    + \sum_(a < n.+1 | v a != min_val)  expR (x * min_dev a v)
  by move => x0; exact/bigID.
have sum_bot : (\sum_(a < n.+1) expR (p0 * min_dev a v)) @[p0 --> +oo] -->
                 ((\sum_(a < n.+1| v a == min_val) 1) : R).
  apply/cvgrPdist_le => /= e e0.
  near=> t.
  rewrite sum_spl2.
  near: t; move: e e0; apply/cvgrPdist_le.
  (*bot sum non-minimum elements*)
  have sum_bot_rest :
      (\sum_(a < n.+1 | v a != min_val)  expR (t * min_dev a v))%R @[t --> +oo] --> 0.
    rewrite [X in _ --> X](_ : _ = \sum_(a < n.+1 | v a != min_val) 0); last by rewrite big1.
    apply/cvgrPdist_le => /= e e0.
    near=> t.
    rewrite big_seq_cond [X in _ - X]big_seq_cond.
    near: t; move: e e0; apply/cvgrPdist_le.
    apply: cvg_sum => a /andP [av amin].
    apply: (@cvg_comp _ _ _ _ _ _ -oo); last exact/cvgNy_compNP/cvgr_expR.
    apply/cvgy_compNP.
    under eq_cvg => x do rewrite /=mulNr -mulrN mulrC.
    apply/gt0_cvgMrNy => //.
    rewrite oppr_gt0.
    exact/min_dev_lt0.
  rewrite -(addr0 ((\sum_(a < n.+1 | v a == min_val) 1))).
  apply: cvgD; last by exact sum_bot_rest.
  apply/cvgrPdist_le => /= e e0.
  near=> t.
  near: t; move: e e0; apply/cvgrPdist_le.
  apply: cvg_sum => a /eqP amin.
  rewrite /min_dev amin subrr mul0r.
  under eq_fun do rewrite mulr0 expR0.
  exact: cvg_cst.
have gt0 : ((\sum_(a < n.+1 | v a == min_val) 1) : R) > 0.
  rewrite sumr_gt0//=.
  exists (extremum <=%R ord0 xpredT v).
  split => //; first by rewrite mem_index_enum.
  case: (@extremumP _ _ ler ord0 xpredT v lexx le_trans le_total isT) => i _/= h.
  by rewrite eq_le !le_bigmin ?h//= bigmin_le.
have sum_inv : (\sum_(a < n.+1) expR ( p0 * min_dev a v))^-1 @[p0 --> +oo] -->
                  ((\sum_(a < n.+1 | v a == min_val) 1): R)^-1.
  apply: cvgV; first exact/lt0r_neq0/gt0. 
  exact sum_bot.
have l := (@cvgM _ _ _ _ _ _ _ _ sum_top sum_inv).
rewrite -fctM in l.
have helper : min_val * (\sum_(a < n.+1 | v a == min_val) 1) / (\sum_(a < n.+1 | v a == min_val) 1) = min_val.
  by rewrite mulrK//= unitfE; apply lt0r_neq0; exact gt0.
rewrite helper in l.
apply: l.
Unshelve. all: end_near.
Qed.

End stl_and_conv_lattice.

Section stl_and_lemmas.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (nu : R) (M : nat).

Definition fun_of_rV := (fun v j => @fun_of_matrix R 1 M.+1 v ord0 j).

Lemma fun_of_rV_const (p : R) :
  fun_of_rV (const_mx p) = fun=> p.
Proof. by apply/funext => i; rewrite /fun_of_rV mxE. Qed.

Lemma min_dev_const (a : 'I_M.+1) (p : R) : min_dev a (fun=> p) = 0.
Proof.
rewrite /min_dev.
suff -> : \big[minr/p]_(j < M.+1) p = p by rewrite subrr mul0r.
exact/eqP/bigmin_eqP.
Qed.

Lemma stl_and_gt0_const p : stl_and_gt0 nu (fun_of_rV (const_mx p)) = p.
Proof.
rewrite /stl_and_gt0/= fun_of_rV_const.
under eq_bigr => i _ do rewrite min_dev_const mulr0 expR0 mulr1.
under [X in _ / X]eq_bigr => i _ do rewrite min_dev_const mulr0 expR0.
rewrite !big_const_ord !iter_addr !addr0.
by rewrite -(mulr_natr p) -mulrA divff ?mulr1.
Qed.

Lemma stl_and_lt0_const p : stl_and_lt0 nu (fun_of_rV (const_mx p)) = p.
Proof.
rewrite /stl_and_lt0/= fun_of_rV_const.
under eq_bigr => i _.
  rewrite !min_dev_const mulr0 expR0 !mulr1.
  have -> : \big[minr/p]_(j < M.+1) p = p by exact/eqP/bigmin_eqP.
  over.
under [X in _ / X]eq_bigr => i _ do rewrite min_dev_const mulr0 expR0.
rewrite !big_const_ord !iter_addr !addr0.
by rewrite -(mulr_natr p) -mulrA divff ?mulr1.
Qed.

End stl_and_lemmas.

Section shadow_lifting_stl_and.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variable nu : R.
Variable M : nat.

Local Notation stl_and_gt0 := (stl_and_gt0 nu).
Local Notation stl_and_lt0 := (stl_and_lt0 nu).

(* technical lemmas *)
Lemma mip_at_right (p h : R) i : 0 < h ->
  let v := (const_mx p + h *: err_vec i)%E ord0 in
  \big[minr/v ord0]_(i0 < M.+2) v i0 = p.
Proof.
move=> h0/=.
rewrite (bigminD1 i)// !mxE eqxx mulr1.
rewrite (eq_bigr (fun=> p)); last first.
  by move=> /= j ji; rewrite !mxE eq_sym (negbTE ji) mulr0 addr0.
rewrite big_const/= iter_minr//; last 2 first.
- by rewrite card_ordS.
- by rewrite lerDl// mulr_ge0// ltW.
by rewrite /minr ltNge lerDl (ltW h0).
Qed.

Lemma mip_at_left (p h : R) i : h < 0 ->
  let v := (const_mx p + h *: err_vec i)%E ord0 in
  \big[minr/v ord0]_(i < M.+2) v i = p + h.
Proof.
move=> h0 /=.
rewrite (bigminD1 i)// !mxE eqxx mulr1.
rewrite (eq_bigr (fun=> p)); last first.
  by move=> /= j ji; rewrite !mxE eq_sym (negbTE ji) mulr0 addr0.
rewrite big_const/= iter_minr'//; last 2 first.
- by rewrite card_ordS.
- by rewrite gerDl// mulr_le0_ge0// ltW.
rewrite /minr; case: ifPn => //.
have [_|_]/= := eqVneq i ord0.
  by rewrite !mulr1.
by rewrite !mulr0 !addr0 gtrDl h0.
Qed.

Lemma mip'_at_right (p h : R) i : h > 0 ->
  let v := (const_mx p + h *: err_vec i)%E ord0 in
  \big[minr/v ord0]_(i0 < M.+2) v i0 = p.
Proof.
move=> h0 /=.
rewrite (bigminD1 i)// !mxE eqxx mulr1.
rewrite (eq_bigr (fun=> p)); last first.
  by move=> /= j ji; rewrite !mxE eq_sym (negbTE ji) mulr0 addr0.
rewrite big_const/= iter_minr//; last 2 first.
- by rewrite card_ordS.
- by rewrite lerDl// mulr_ge0// ltW.
by rewrite /minr ltNge lerDl (ltW h0).
Qed.

Lemma mip'_at_left (p h : R) i : h < 0 ->
  let v := (const_mx p + h *: err_vec i)%E ord0 in
  \big[minr/v ord0]_(i0 < M.+2) v i0 = p + h.
Proof.
move=> h0 /=.
rewrite (bigminD1 i)// !mxE eqxx mulr1.
rewrite (eq_bigr (fun=> p)); last first.
  by move=> /= j ji; rewrite !mxE eq_sym (negbTE ji) mulr0 addr0.
rewrite big_const/= iter_minr'//; last 2 first.
- by rewrite card_ordS.
- by rewrite gerDl// mulr_le0_ge0// ltW.
rewrite /minr; case: ifPn => //.
have [_|_]/= := eqVneq i ord0.
  by rewrite !mulr1.
by rewrite !mulr0 !addr0 gtrDl h0.
Qed.

Lemma shadowlifting_stl_and_gt0_cvg_at_right (p : R) i : 0 < p ->
  h^-1 *
  (stl_and_gt0 (fun_of_rV M.+1 (const_mx p + h *: err_vec i)) -
   stl_and_gt0 (fun_of_rV M.+1 (const_mx p))) @[h --> 0^'+] --> (M.+2%:R : R)^-1.
Proof.
move=> p0.
rewrite /= stl_and_gt0_const.
have H h : h > 0 ->
  stl_and_gt0 (fun_of_rV _ (const_mx p + h *: err_vec i)) =
  (p * M.+1%:R + (p + h) * expR (- nu * (h / p))) / (M.+1%:R + expR (-nu * (h / p))).
  move=> h0.
  rewrite /stl_and_gt0/=.
  congr (_ / _).
    rewrite (bigD1 i)//=.
    rewrite /fun_of_rV !mxE eqxx mulr1.
    rewrite (_ : min_dev _ _ = h / p); last first.
      rewrite /min_dev !mip_at_right// !mxE eqxx/= mulr1.
      by rewrite -addrA addrCA subrr addr0.
    rewrite (eq_bigr (fun=> p)); last first.
      move=> j /negbTE ji.
      rewrite !mxE eq_sym ji mulr0 addr0.
      rewrite (_ : min_dev _ _ = 0); last first.
        rewrite /min_dev mip'_at_right// !mxE eq_sym ji/=.
        by rewrite mulr0 addr0 subrr mul0r.
      by rewrite mulr0 expR0 mulr1.
    rewrite big_const/= iter_addr addr0 card_ordS.
    by rewrite addrC mulr_natr.
  rewrite (bigD1 i)//=.
  under eq_bigr => j /negbTE ji do
    rewrite /min_dev mip_at_right// /fun_of_rV !mxE eq_sym ji mulr0 addr0 subrr mul0r mulr0 expR0.
  rewrite /min_dev mip_at_right// /fun_of_rV !mxE eqxx mulr1 big_const iter_addr/= addr0 card_ordS.
  by rewrite addrAC subrr add0r addrC.
apply/cvgrPdist_le => /= e e0; near=> t.
rewrite H//= -[X in (_ / _ - X)](mul1r p).
rewrite -[X in (_ / _ - X * _)](@divff _ (M.+1%:R + expR (- nu * (t / p)))); last first.
  by rewrite lt0r_neq0// addr_gt0// ?expR_gt0// ltr0n lt0n.
rewrite (mulrAC _ (_^-1) p) -mulrBl.
have -> : ((p * M.+1%:R) + ((p + t) * expR (- nu * (t / p)))) -
          (M.+1%:R + expR (- nu * (t / p))) * p = t * expR (- nu * (t / p)) by lra.
rewrite !mulrA mulVf// mul1r -(mul1r (M.+2%:R^-1)).
have -> : expR (- nu * t / p) / (M.+1%:R + expR (- nu * t / p)) =
  ((fun t => expR (- nu * t / p)) \*
   (fun t => (M.+1%:R + expR (- nu * t / p)) ^-1)) t by [].
near: t; move: e e0; apply/cvgrPdist_le.
apply: cvgM.
  by under eq_fun do rewrite mulrAC; exact: expR_cvg0.
apply: cvgV; first by rewrite lt0r_neq0.
rewrite -!natr1; apply: cvgD; first exact: cvg_cst.
by under eq_fun do rewrite mulrAC; exact: expR_cvg0.
Unshelve. all: end_near. Qed.

Lemma shadowlifting_stl_and_gt0_cvg_at_left (p : R) i : 0 < p ->
  h^-1 *
  (stl_and_gt0 (fun_of_rV M.+1 (const_mx p + h *: err_vec i)) -
   stl_and_gt0 (fun_of_rV M.+1 (const_mx p))) @[h --> 0^'-] --> (M.+2%:R : R)^-1.
Proof.
move=> p0.
have H h : h < 0 -> (stl_and_gt0 (fun_of_rV _ (const_mx p + h *: err_vec i))) =
    (p * M.+1%:R * expR (- nu * (- h / (p + h))) + (p + h)) / (M.+1%:R * expR (- nu * (- h / (p + h))) + 1).
  move=> h0.
  rewrite /stl_and_gt0/= (bigD1 i)//=.
  congr (_ / _).
    rewrite /fun_of_rV !mxE eqxx mulr1 (_ : min_dev _ _ = 0); last first.
      by rewrite /min_dev mip_at_left// !mxE eqxx/=; lra.
    rewrite mulr0 expR0 mulr1 addrC.
    rewrite (eq_bigr (fun=> p * expR (- nu * (- h / (p + h))))); last first.
      move=> j /negbTE ji.
      rewrite !mxE eq_sym ji mulr0 addr0.
      rewrite (_ : min_dev _ _ = - h / (p + h))//.
      by rewrite /min_dev mip'_at_left// !mxE eq_sym ji/=; lra.
    rewrite big_const/= iter_addr addr0 card_ordS.
    by rewrite -[in LHS]mulr_natr mulrAC.
  rewrite /= (bigD1 i)//=.
  rewrite (_ : min_dev _ _ = 0); last first.
    by rewrite /min_dev /fun_of_rV mip_at_left// !mxE/= eqxx/=; lra.
  rewrite (eq_bigr (fun=> (expR (- nu * (- h / (p + h)))))); last first.
    move=> j /negbTE ji.
    by rewrite /min_dev mip'_at_left// /fun_of_rV !mxE eq_sym ji/= mulr0 addr0 opprD addrA subrr sub0r.
  rewrite big_const/= iter_addr addr0 card_ordS.
  by rewrite mulr0 expR0 addrC -[in LHS]mulr_natr mulrC.
apply/cvgrPdist_le => /= e e0; near=> t.
rewrite H//=.
rewrite /= stl_and_gt0_const.
rewrite -[X in (_ / _ - X)](mul1r p).
rewrite -[X in (_ / _ - X * _)](@divff _ (M.+1%:R * expR (- nu * (- t / (p + t))) + 1)); last first.
  rewrite lt0r_neq0// addr_gt0// ?expR_gt0// mulr_gt0//.
  rewrite (mulrAC _ (_^-1) p) -mulrBl.
  have -> : ((p * M.+1%:R * expR (- nu * (- t / (p + t)))) + (p + t)) -
   ((M.+1%:R * expR (- nu * (- t / (p + t)))) + 1) * p = t by lra.
  have -> : t^-1 * (t / ((M.+1%:R * expR (- nu * (- t / (p + t)))) + 1)) =
    1 / ((M.+1%:R * expR (- nu * (- t / (p + t)))) + 1).
    by rewrite (mulrA (t^-1)) mulVf.
  rewrite div1r.
  near: t; move: e e0; apply/cvgrPdist_le.
  apply: cvgV.
    by rewrite gt_eqF.
  rewrite -[X in _ --> X]natr1; apply: cvgD; last exact: cvg_cst.
  rewrite -[X in _ --> X]mulr1; apply: cvgM; first exact: cvg_cst.
  rewrite -expR0; apply: continuous_cvg; first exact: continuous_expR.
  rewrite -[X in _ --> X](mulr0 (- nu)).
  apply: cvgM; first exact: cvg_cst.
  rewrite [X in _ --> X](_ : _ = (- 0) * p^-1); last by rewrite oppr0 mul0r.
  apply: cvgM.
    apply: cvgN.
    by apply: cvg_at_left_filter; exact: cvg_id.
  apply: cvgV; first by rewrite gt_eqF.
  rewrite -[X in _ --> X]addr0.
  apply: cvgD; first exact: cvg_cst.
  by apply: cvg_at_left_filter; exact: cvg_id.
Unshelve. all: end_near. Qed.

Lemma shadowlifting_stl_and_gt0_cvg (p : R) i : 0 < p ->
  h^-1 *
  (stl_and_gt0 (fun_of_rV M.+1 (const_mx p + h *: err_vec i)) -
   stl_and_gt0 (fun_of_rV M.+1 (const_mx p))) @[h --> 0^'] --> (M.+2%:R : R)^-1.
Proof.
move=> p0; apply/cvg_at_right_left_dnbhs.
- exact/shadowlifting_stl_and_gt0_cvg_at_right.
- exact/shadowlifting_stl_and_gt0_cvg_at_left.
Qed.

Lemma shadowlifting_stl_and_gt0 (p : R) : p > 0 -> forall i,
  ('d (@stl_and_gt0 M.+1 \o @fun_of_rV _ M.+1) '/d i) (const_mx p) = M.+2%:R^-1.
Proof.
move=> p0 i.
rewrite /partial /= stl_and_gt0_const.
have := shadowlifting_stl_and_gt0_cvg _ i p0.
rewrite stl_and_gt0_const => /cvg_lim.
by apply; exact: Rhausdorff.
Qed.

Let num' (p x : R) : R := M.+1%:R * expR (- x / (p + x)) +
  expR (- x / (p + x)) * x * M.+1%:R * (x / (x + p)^+2 - (x + p)^-1) +
  expR (- x / (p + x)) * M.+1%:R * p * (x / (x + p)^+2 - (x + p)^-1).

Let px_neq0 (p y : R) : y \in (ball 0 p : set R) -> (p + y) != 0.
Proof.
rewrite inE /ball/= sub0r normrN lter_norml => /andP[Npx xp].
by rewrite gt_eqF// -ltrBlDl sub0r.
Qed.

Let derivableDV (p y : R) : y \in (ball 0 p : set R) ->
  derivable (fun x0 => (p + x0)^-1) y 1.
Proof.
by move=> y0p; apply: derivableV; [exact: px_neq0|exact: derivable_addr].
Qed.

Let derivableVD (p y : R) : y \in (ball 0 p : set R) ->
    derivable (fun x0 : R => - x0 / (p + x0)) y 1.
Proof.
move=> y0p; apply: derivableM; last exact: derivableDV.
by apply: derivableN; exact: derivable_id.
Qed.

Let derivable_DVexpR (p y : R) : y \in (ball 0 p : set R) ->
  derivable (fun x0 : R => expR (- x0 / (p + x0))) y 1.
Proof.
move=> y0p.
by apply: derivable_comp; [exact: derivable_expR|exact: derivableVD].
Qed.

Lemma is_derive_num' (x : R) p : x \in (ball 0 p : set R) ->
  is_derive x 1 (fun z => M.+1%:R * (p + z) * expR (- z / (p + z)) - M.+1%:R * p)
    (num' p x).
Proof.
move=> x0p.
have Mp : derivable (fun z => M.+1%:R * (p + z)) x 1.
  apply: derivableM; first exact: derivable_cst.
  by apply: derivableD; [exact: derivable_cst|exact: derivable_id].
rewrite -[X in is_derive _ _ _ X]subr0; apply: is_deriveB.
apply: DeriveDef.
  by apply: derivableM; [exact: Mp|exact: derivable_DVexpR].
rewrite deriveM; [|exact: Mp|exact: derivable_DVexpR].
rewrite deriveM; [|exact: derivable_cst|exact: derivable_addr].
rewrite derive_comp; [|exact: derivableVD|exact: derivable_expR].
rewrite (_ : 'D_1 expR _ = expR (- x / (p + x))); last first.
  by rewrite -[in RHS]derive_expR.
rewrite deriveD; [| exact: derivable_cst|exact: derivable_id].
rewrite derive_cst add0r.
rewrite derive_id [M.+1%:R%:A]scaler1.
rewrite derive_cst scaler0 addr0.
rewrite deriveM/=; [|exact: derivable_subr|exact: derivableDV].
rewrite deriveV; [|exact: px_neq0|exact: derivable_addr].
rewrite deriveD; [|exact: derivable_cst|exact: derivable_id].
rewrite derive_cst add0r.
rewrite derive_id.
set pxA := (X in - x *: X).
rewrite (_ : pxA = (- (p + x) ^- 2))//; last by rewrite /pxA /GRing.scale/= mulr1.
rewrite deriveN; last exact: derivable_id.
rewrite derive_id scalerN1.
rewrite [X in X + _ = _]scalerAl scalerCA -[LHS]mulrDr.
rewrite [X in _ = X + _ + _]mulrC -!mulrA -2!mulrDr; congr *%R.
rewrite [in LHS]addrC -!addrA; congr +%R.
rewrite [in RHS]mulrCA -mulrDr -[LHS]mulrA; congr *%R.
rewrite -mulrDl (addrC p); congr (_ * (_ - _)).
by rewrite scaleNr -mulrN opprK.
Qed.

Let den' (p x : R) : R := expR (nu * (x / (x + p))) +
  M.+1%:R +
  expR (nu * (x / (x + p))) * x * (- x * nu / (x + p)^+2 + nu / (x + p)).

Lemma is_derive_den' (x : R) p :
  x \in (ball 0 p : set R) ->
  is_derive x 1 (fun x => x * (M.+1%:R + (expR (nu * - x / (p + x)))^-1))
    (den' p x).
Proof.
move=> x0p.
have expnup : derivable (fun y => expR (nu * - y / (p + y))) x 1.
  apply: derivable_comp; first exact: derivable_expR.
  apply: derivableM; last exact: derivableDV.
  by apply: derivableM; [exact: derivable_cst|exact: derivable_subr].
apply: DeriveDef.
  apply: derivableM; first exact: derivable_id.
  apply: derivableD; first exact: derivable_cst.
  by apply: derivableV; [by rewrite expR_eq0|exact: expnup].
rewrite /den' deriveM; last 2 first.
  exact: derivable_id.
  apply: derivableD; first exact: derivable_cst.
  by apply: derivableV; [by rewrite expR_eq0|exact: expnup].
rewrite deriveD; last 2 first.
  exact: derivable_cst.
  by apply: derivableV; [by rewrite expR_eq0|exact: expnup].
rewrite derive_cst add0r/=.
rewrite deriveV/=; [|by rewrite expR_eq0|exact: expnup].
rewrite derive_comp; last 2 first.
  under eq_fun.
    move=> z.
    rewrite -mulrA.
    over.
  apply: (@derivableM _ _ (cst nu)); first exact: derivable_cst.
  exact: derivableVD.
  exact: derivable_expR.
rewrite (_ : 'D_1 expR _ = expR (nu * - x / (p + x))); last first.
  by rewrite -[in RHS](@derive_expR R).
rewrite deriveM; last 2 first.
  by apply: derivableM; [exact: derivable_cst|exact: derivable_subr].
  exact: derivableDV.
rewrite deriveV; [|exact: px_neq0|exact: derivable_addr].
rewrite deriveM; [|exact: derivable_cst|exact: derivable_subr].
rewrite derive_cst scaler0 addr0.
rewrite deriveN; last exact: derivable_id.
rewrite deriveD; [|exact: derivable_cst|exact: derivable_id].
rewrite derive_id derive_cst add0r.
rewrite scalerN1.
rewrite [X in _ + X = _]/GRing.scale/= mulr1.
rewrite addrCA.
rewrite -[RHS]addrA [RHS]addrCA; congr +%R.
rewrite [LHS]addrC; congr +%R.
  by rewrite -expRN mulrN mulNr opprK (addrC p) mulrA.
rewrite -[RHS]mulrA [RHS]mulrCA; congr *%R.
rewrite [in LHS]scaleNr [X in - X]mulrA -[in LHS]mulrN; congr *%R.
  rewrite !(mulrN,mulNr) !expRN.
  rewrite -exprVn invrK expr2.
  rewrite -[LHS]mulrA divff ?mulr1 ?expR_eq0//.
  by rewrite (addrC p)// mulrA.
rewrite !(mulrN,mulNr,scaleNr,scalerN,opprK) opprB.
rewrite [RHS]addrC; congr (_ - _).
  by rewrite [LHS]mulrC (addrC p).
by rewrite (mulrC nu) scalerA (addrC p) scaler1.
Qed.

Lemma shadowlifting_stl_and_lt0_cvg_at_right (p : R) i : p > 0 ->
  h^-1 *
  (stl_and_lt0 (fun_of_rV M.+1 (const_mx p + h *: err_vec i)) -
   stl_and_lt0 (fun_of_rV M.+1 (const_mx p))) @[h --> 0^'+] --> (M.+2%:R : R)^-1.
Proof.
move=> p0.
rewrite /= stl_and_lt0_const.
have H h : h > 0 ->
  stl_and_lt0 (fun_of_rV M.+1 (const_mx p + h *: err_vec i)) =
  (M.+1%:R  * p + p * expR (h / p) * expR (nu * (h / p))) /
  (M.+1%:R + expR (nu * (h / p))).
  move=> h0.
  rewrite /stl_and_lt0/=.
  congr (_ / _).
    rewrite (bigD1 i)//= /fun_of_rV.
    rewrite (_ : min_dev _ _ = h / p); last first.
      by rewrite /min_dev mip_at_right// !mxE eqxx/=; lra.
    rewrite mip_at_right//.
    rewrite (eq_bigr (fun=> p)); last first.
      move=> j /negbTE ji.
      rewrite (_ : min_dev _ _ = 0); last first.
        by rewrite /min_dev mip'_at_right// !mxE eq_sym ji mulr0 addr0 subrr mul0r.
      by rewrite mulr0 expR0 !mulr1.
    rewrite big_const/= iter_addr addr0 card_ordS addrC.
    by rewrite (mulrC M.+1%:R p) mulr_natr.
  rewrite (bigD1 i)//=.
  rewrite (_ : min_dev _ _ = h / p); last first.
    by rewrite /min_dev mip_at_right// /fun_of_rV !mxE eqxx mulr1 addrAC subrr add0r.
  rewrite addrC; congr (_ + _).
  rewrite (eq_bigr (fun=> 1)).
    by rewrite big_const/= card_ordS iter_addr addr0.
  move=> j /negbTE ji.
  rewrite (_ : min_dev _ _ = 0); last first.
    by rewrite /min_dev mip'_at_right// /fun_of_rV !mxE eq_sym ji mulr0 addr0 subrr mul0r.
  by rewrite mulr0 expR0.
apply/cvgrPdist_le => /= eps eps0; near=> x.
rewrite [X in normr (_ - X)](_ : _ =
    (M.+1%:R + expR (nu * (x / p)))^-1 *
    expR (nu * (x / p)) *
    ((expR (x / p) - 1) / (x / p))); last first.
  rewrite H//.
  set a := expR (x / p).
  set b := expR (nu * (x / p)).
  rewrite invf_div !mulrA mulrC.
  congr (_ / _).
  rewrite -[X in _ - X](mulr1 p).
  rewrite -[X in _ - (_ * X)](@mulVf _ (M.+1%:R + b)).
    rewrite mulrCA mulrC -mulrBr -!mulrA.
    congr (_ * _).
    rewrite -mulrC -mulrDr -mulrBr.
    nra.
  by rewrite gt_eqF// addr_gt0// ?ltr0n ?lt0n// expR_gt0.
near: x; move: eps eps0; apply/cvgrPdist_le.
rewrite -(mulr1 M.+2%:R^-1).
rewrite -(mulr1 (M.+2%:R^-1 * 1)).
apply: cvgM.
  apply: cvgM.
    apply: cvgV; first by [].
    rewrite -(natr1 (M.+1)); apply: cvgD; first exact: cvg_cst.
    by under eq_fun do rewrite mulrCA mulrC; exact: expR_cvg0.
  by under eq_fun do rewrite mulrCA mulrC; exact: expR_cvg0.
have MpV (x : R) : is_derive x 1 ( *%R^~ p^-1) p^-1.
  rewrite [X in is_derive _ _ X _](_ : _ = p^-1 *: id); last first.
    by apply/funext => y /=; rewrite mulrC.
  rewrite [X in is_derive _ _ _ X](_ : _ = p^-1 *: (1:R))//.
    exact: is_deriveZ.
  by rewrite scaler1.
apply: (@lhopital_at_right R (fun x => expR (x / p) - 1)
    (fun x => p^-1 * expR (x / p)) (fun x => x / p) (fun=> p^-1) _ _ _ p0).
- move=> x; rewrite in_itv/= => /andP[x0 xp].
  rewrite -[X in is_derive _ _ _ X]subr0; apply: is_deriveB => /=.
  by rewrite mulrC; exact: is_derive1_comp.
- rewrite -[X in _ --> X](subrr 1).
  apply: cvgB; last exact: cvg_cst.
  by under eq_fun do rewrite mulrC; exact: expR_cvg0.
- rewrite -[X in _ --> X](mul0r p^-1).
  by apply: cvgMr_tmp; exact: cvg_at_right_filter.
- move=> x; rewrite in_itv/= => /andP[x0 xp].
  by rewrite gt_eqF// invr_gt0 (lt_trans x0).
- rewrite -expR0.
  under eq_fun.
    move=> x; rewrite mulrAC divff ?gt_eqF ?invr_gt0// mul1r.
    over.
  apply: continuous_cvg; first exact: continuous_expR.
  rewrite -[X in _ --> X](mul0r p^-1).
  by apply: cvgM; [exact/cvg_at_right_filter|exact: cvg_cst].
Unshelve. all: end_near. Qed.

Lemma shadowlifting_stl_and_lt0_cvg_at_left (p : R) i : p > 0 ->
  h^-1 *
  (stl_and_lt0 (fun_of_rV M.+1 (const_mx p + h *: err_vec i)) -
   stl_and_lt0 (fun_of_rV M.+1 (const_mx p))) @[h --> 0^'-] --> (M.+2%:R : R)^-1.
Proof.
move=> p0.
rewrite /= stl_and_lt0_const.
have H h : h < 0 ->
  stl_and_lt0 (fun_of_rV _ (const_mx p + h *: err_vec i)) =
  (((p + h) * M.+1%:R * expR (- h / (p + h)) * expR (nu * (- h / (p + h))) + p + h) /
  (M.+1%:R * expR (nu * (- h / (p + h))) + 1)).
  move=> h0.
  rewrite /stl_and_lt0/= (bigD1 i)//=.
  congr (_ / _).
    rewrite (_ : min_dev _ _ = 0); last first.
      by rewrite /min_dev mip_at_left// /fun_of_rV !mxE eqxx/=; lra.
    rewrite mulr0 expR0 !mulr1 addrC.
    rewrite (eq_bigr (fun=> (p + h) * expR (- h / (p + h)) *
                            expR (nu * (- h / (p + h))))); last first.
      move=> j /negbTE ji.
      rewrite (_ : min_dev _ _ = -h / (p + h)); last first.
        by rewrite /min_dev mip'_at_left// /fun_of_rV !mxE/= eq_sym ji/=; lra.
      by rewrite mip'_at_left.
    rewrite big_const/= iter_addr addr0 card_ordS mip_at_left//.
    by rewrite -[in LHS]mulr_natl !mulrA (mulrC (M.+1%:R)) addrA.
  rewrite /= (bigD1 i)//=.
  rewrite (_ : min_dev _ _ = 0); last first.
    by rewrite /min_dev mip_at_left// /fun_of_rV !mxE eqxx/=; lra.
  rewrite (eq_bigr (fun=> expR (nu * (- h / (p + h))))); last first.
    move=> j /negbTE ji.
    rewrite /min_dev mip'_at_left//.
    by rewrite /fun_of_rV !mxE eq_sym ji mulr0 addr0 opprD addrA subrr sub0r.
  rewrite big_const/= iter_addr addr0 card_ordS.
  by rewrite mulr0 expR0 addrC -[in LHS]mulr_natr mulrC.
apply/cvgrPdist_le => /= eps eps0; near=> x.
pose a x := expR (nu * - x / (p + x)).
pose b x := expR (- x / (p + x)).
pose num x := M.+1%:R * (p + x) * b x - M.+1%:R * p.
pose den x := x * (M.+1%:R + (a x)^-1).
have ? : a x != 0 by rewrite ?gt_eqF ?expR_gt0.
have ? : (M.+1%:R * a x) + 1 != 0.
  by rewrite gt_eqF// addr_gt0// mulr_gt0// ?expR_gt0// ltr0n// lt0n.
rewrite [X in normr (_ - X)](_ : _ =
    (a x * (M.+1%:R + (a x)^-1))^-1 + num x / den x); last first.
  rewrite /= H// mulrA -/(b x) -/(a x).
  rewrite -[X in _ - X](mul1r p) -[X in _ - (X * p)](@mulfV _ (((M.+1%:R * a x) + 1)))//.
  rewrite -(mulrAC _ p) -mulrBl (mulrDl _ _ p) mul1r opprD !addrA.
  rewrite [X in _ * (X / _)](_ : _ =
    (p + x) * M.+1%:R * b x * a x + x - M.+1%:R * a x * p); last first.
    by rewrite -!addrA !(addrC p) -!addrA (addrC (-p)) subrr addr0.
  rewrite (_ : _ / _ = a x * ((p + x) * M.+1%:R * b x + x * (a x)^-1 - M.+1%:R * p)
                       / (a x * (M.+1%:R + (a x)^-1))); last first.
    congr (_ / _); last by rewrite mulrDr mulfV// mulrC.
    rewrite !mulrDr (mulrC (a x) (_ / _)) -(mulrA x) (@mulVf _ (a x))// mulr1.
    by rewrite !mulrN {1}(mulrC (a x)) [in RHS](mulrC (a x)) -!mulrA (mulrC p).
  rewrite -addrAC mulrDr (mulrC (a x) (_ / _)) -(mulrA x) (@mulVf _ (a x))// mulr1.
  rewrite mulrA (mulrDr (x^-1)) mulrDl addrC.
  congr (_ + _).
    by rewrite mulVf// mul1r.
  rewrite !invrM'// (mulrC (a x)) !mulrA; congr(_/_).
  rewrite -mulrA mulfV// mulr1 mulrC; congr(_/_).
  by rewrite /num; lra.
near: x; move: eps eps0; apply/cvgrPdist_le.
have a01 : a x @[x --> nbhs 0^'-] --> (1:R).
  rewrite /a -expR0; apply: continuous_cvg; first apply: continuous_expR.
  rewrite -[X in _ --> X](mul0r p^-1).
  apply: cvgM; last first.
    apply: cvgV; first by rewrite gt_eqF.
    rewrite -{2}(addr0 p).
    apply: cvgD; first exact: cvg_cst.
    exact/cvg_at_left_filter/cvg_id.
  rewrite -{2}(mulr0 nu) -{2}oppr0.
  apply: cvgM; first exact: cvg_cst.
  apply: cvgN.
  exact/cvg_at_left_filter/cvg_id.
rewrite -[X in _ --> X]addr0.
apply: cvgD.
  apply: cvgV; first by [].
  rewrite -(mul1r (M.+2%:R)).
  apply: cvgM; first exact: a01.
  rewrite -(natr1 M.+1).
  apply: cvgD; first exact: cvg_cst.
  rewrite -invr1 /a.
  exact: cvgV.
rewrite /num /den /a /b.
have H1 : - x * nu / (x + p) ^+ 2 @[x --> 0] --> - 0 * nu / (0 + p) ^+ 2.
  apply: cvgM.
    apply: cvgM.
      by apply: cvgN; exact: cvg_id.
     exact: cvg_cst.
  apply: continuous_cvg.
    apply: continuousV; last exact: cvg_id.
    by rewrite add0r sqrf_eq0 gt_eqF.
  rewrite expr2.
  under eq_fun do rewrite expr2.
  apply: cvgM.
    by apply: cvgD; [exact: cvg_id|exact: cvg_cst].
  by apply: cvgD; [exact: cvg_id|exact: cvg_cst].
have H2 : (*(expR (nu * (x / (x + p))) + M.+1%:R +
    expR (nu * (x / (x + p))) * x * (- x * nu / (x + p) ^+ 2 + nu / (x + p)))*) den' p x
    @[x --> (0:R)^'] --> ((1:R) + M.+1%:R).
  rewrite -[X in _ --> X]addr0.
  have H2 : nu * (x0 / (x0 + p)) @[x0 --> 0^'] --> 0.
    rewrite -[X in _ --> X](mulr0 nu).
    apply: cvgM; first exact: cvg_cst.
    rewrite -[X in _ --> X](mul0r p^-1).
    apply: cvgM.
      by apply/continuous_withinNx; exact: cvg_id.
    apply: cvgV; first by rewrite gt_eqF.
    rewrite -[X in _ --> X](add0r p).
    by apply: cvgD; [exact/continuous_withinNx/cvg_id|exact: cvg_cst].
  apply: cvgD.
    apply: cvgD; last exact: cvg_cst.
    rewrite -[X in _ --> X]expR0.
    by apply: continuous_cvg; [exact: continuous_expR|exact: H2].
  rewrite [X in _ --> X](_ : _ = 1 * 0 * (nu / p)); last first.
    by rewrite mulr0 mul0r.
  apply: cvgM.
    apply: cvgM; last exact/continuous_withinNx/cvg_id.
    rewrite -expR0.
    by apply: continuous_cvg; [exact: continuous_expR|exact: H2].
  rewrite -[X in _ --> X]add0r.
  apply: cvgD.
    rewrite [X in _ --> X](_ : _ = (- 0) * nu / (0 + p) ^+ 2); last first.
      by rewrite oppr0 mul0r mul0r.
    by apply: cvg_within_filter; exact: H1.
  apply: cvgM; first exact: cvg_cst.
  apply: cvgV; first by rewrite gt_eqF.
  rewrite -[X in _ --> X](add0r p).
  apply: cvgD; last exact: cvg_cst.
  exact/continuous_withinNx/cvg_id.
have M10 : (1%R + M.+1%:R)%E != 0 :> R by rewrite gt_eqF.
have [e/= e0 ep] := @cvgr_neq0 _ _ _ _ (dnbhs_filter 0) _ _ H2 M10.
near (0:R)^'+ => q.
apply: (@lhopital_at_left R _ (num' p) _ (den' p) (- q)).
- by rewrite ltrNl oppr0.
- move=> x; rewrite in_itv/= => /andP[px x0].
  apply: is_derive_num'.
  rewrite inE /ball/= sub0r normrN ltr0_norm// ltrNl.
  by rewrite (lt_trans _ px)// ltrN2//.
- move=> x; rewrite in_itv/= => /andP[px x0].
  apply: is_derive_den'.
  rewrite inE /ball/= sub0r normrN ltr0_norm// ltrNl//.
  by rewrite (lt_trans _ px)// ltrN2//.
- rewrite -[X in _ --> X](subrr (M.+1%:R * p)).
  apply: cvgB; last exact: cvg_cst.
  under eq_fun do rewrite -mulrA.
  apply: cvgMl_tmp.
  rewrite -[X in _ --> X]mulr1.
  apply: cvgM.
    rewrite -[X in _ --> X]addr0.
    apply: cvgD; first exact: cvg_cst.
    exact: cvg_at_left_filter.
  rewrite -[X in _ --> X]expR0.
  apply: continuous_cvg; first exact: continuous_expR.
  rewrite -[X in _ --> X](mul0r p^-1); apply: cvgM.
    apply: cvg_at_left_filter => /=.
    by rewrite -[X in _ --> X]oppr0; exact: cvgN.
  apply: cvgV; first by rewrite gt_eqF.
  apply: cvg_at_left_filter.
  rewrite -[X in _ --> X]addr0.
  apply: cvgD.
    exact: cvg_cst.
  exact: cvg_id.
- rewrite -[X in _ --> X](mul0r (M.+1%:R + 1^-1)).
  apply: cvgM.
    apply: cvg_at_left_filter.
    exact: cvg_id.
  apply: cvgD.
    apply: cvg_at_left_filter.
    exact: cvg_cst.
  by apply: cvgV => //.
- move=> x; rewrite in_itv/= => /andP[xp x0].
  rewrite /den'.
  apply: ep; last first.
   by rewrite lt_eqF.
  rewrite /ball_/= sub0r normrN ltr0_norm//.
  rewrite ltrNl.
  rewrite (lt_trans _ xp)//.
  by rewrite ltrN2//.
- rewrite -{2}(mul0r (den' p 0)^-1).
  have H3 : expR (nu * (x / (x + p))) @[x --> 0^'-] -->
            expR (nu * (0 / (0 + p))).
    apply: continuous_cvg; first exact: continuous_expR.
    apply: cvgM; first exact: cvg_cst.
    apply: cvgM. exact/cvg_at_left_filter/cvg_id.
    apply: cvgV; first by rewrite add0r gt_eqF.
    by apply: cvgD; [exact/cvg_at_left_filter/cvg_id|exact: cvg_cst].
  apply: cvgM; last first.
    apply: cvgV.
      by rewrite /den' !mul0r !mulr0 !mul0r addr0 gt_eqF// addr_gt0// ?expR_gt0 ?ltr0n ?lt0n.
    apply: cvgD.
      by apply: cvgD; [exact: H3|exact: cvg_cst].
    apply: cvgM.
      by apply: cvgM; [exact: H3|exact/cvg_at_left_filter/cvg_id].
    apply: cvgD.
      by apply: cvg_at_left_filter; exact: H1.
    apply: cvgM; first exact: cvg_cst.
    apply: cvgV; first by rewrite add0r gt_eqF.
    by apply: cvgD; [exact/cvg_at_left_filter/cvg_id|exact: cvg_cst].
  rewrite /num'.
  pose c x := expR (nu * (x / (x + p))).
  rewrite -{2}(mulr0 (M.+1%:R * b 0 / (0 + p))).
  apply: cvg_trans.
    apply: (@near_eq_cvg _ _ _ _ (fun (x : R) => M.+1%:R * b x / (x + p) * x)).
    near=> x.
    have px_neq0' : p + x != 0.
      apply: px_neq0. rewrite inE/ball/= sub0r normrN ltr0_norm// ltrNl.
      near: x; apply: nbhs_left_gt.
      by rewrite ltrNl oppr0.
    apply/esym.
    rewrite -/(b x) -/(c x).
    rewrite -addrA -mulrDl -mulrA.
    rewrite (mulrC x) mulrA -mulrDr.
    rewrite -mulrA mulrDr mulrN mulfV; last by rewrite addrC px_neq0'.
    rewrite mulrDr mulrN1 addrCA (mulrC _ M.+1%:R) subrr addr0.
    rewrite mulrA (mulrC x) expr2 invrM'; last by rewrite addrC px_neq0'.
    by rewrite !mulrA -(mulrA _ (x + p)) mulfV ?mulr1// addrC px_neq0'.
  apply: cvgM; last first. exact/cvg_at_left_filter/cvg_id.
  apply: cvgM; last first.
    apply: cvgV; first by rewrite gt_eqF ?add0r.
    by apply: cvgD; [exact/cvg_at_left_filter/cvg_id|exact: cvg_cst].
  apply: cvgM; first exact: cvg_cst.
  apply: continuous_cvg; first exact: continuous_expR.
  apply: cvgM; first by apply: cvgN; exact/cvg_at_left_filter/cvg_id.
  apply: cvgV; first by rewrite gt_eqF ?addr0.
  by apply: cvgD; [exact: cvg_cst|exact/cvg_at_left_filter/cvg_id].
Unshelve. all: end_near. Qed.

Lemma shadowlifting_stl_and_lt0_cvg (p : R) i : p > 0 ->
  h^-1 *
  (stl_and_lt0 (fun_of_rV M.+1 (const_mx p + h *: err_vec i)) -
   stl_and_lt0 (fun_of_rV M.+1 (const_mx p))) @[h --> 0^'] --> (M.+2%:R : R)^-1.
Proof.
move=> p0.
apply/cvg_at_right_left_dnbhs.
- exact/shadowlifting_stl_and_lt0_cvg_at_right.
- exact/shadowlifting_stl_and_lt0_cvg_at_left.
Unshelve. all: end_near. Qed.

Lemma shadowlifting_stl_and_lt0 (p : R) : p > 0 -> forall i,
  ('d (@stl_and_lt0 M.+1 \o @fun_of_rV _ _) '/d i) (const_mx p) = M.+2%:R^-1.
Proof.
move=> p0 i.
rewrite /partial.
apply/cvg_lim => //=.
by apply: shadowlifting_stl_and_lt0_cvg.
Qed.

End shadow_lifting_stl_and.
