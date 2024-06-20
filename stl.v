From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences exp measure.
From mathcomp Require Import lebesgue_measure lebesgue_integral hoelder realfun.
Require Import mathcomp_extra analysis_extra ldl.

(**md**************************************************************************)
(* # STL alternative                                                          *)
(*                                                                            *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Section stl_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable nu : R.
Hypothesis nu0 : 0 < nu.

Lemma andI_stl (e : expr Bool_T_def) : nu.-[[e `/\ e]]_stl = nu.-[[e]]_stl.
Proof.
rewrite /= /stl_and /stl_and_gt0 /stl_and_lt0 /min_dev /sumR.
rewrite !big_cons !big_nil/=.
rewrite !minrxxx.
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

Lemma andC_stl (e1 e2 : expr Bool_T_def) :
  nu.-[[e1 `/\ e2]]_stl = nu.-[[e2 `/\ e1]]_stl.
Proof.
rewrite /= /stl_and /stl_and_gt0 /stl_and_lt0 /min_dev /sumR.
rewrite !big_cons !big_nil/= !addr0/=.
rewrite !minrxyx !minxx.
set a_min := minr (nu.-[[e1]]_stl) (nu.-[[e2]]_stl).
have -> : (minr (nu.-[[e2]]_stl) (nu.-[[e1]]_stl)) = a_min.
  by rewrite /a_min/minr; case: ifPn => h1; case: ifPn => h2//; lra.
set a1 := (nu.-[[e1]]_stl - a_min) * a_min^-1.
set a2 := (nu.-[[e2]]_stl - a_min) * a_min^-1.
set d1 := expR (nu * a1) + expR (nu * a2).
have -> : expR (nu * a2) + expR (nu * a1) = d1 by rewrite addrC.
case: ifPn; first by rewrite addrC .
case: ifPn; first by rewrite addrC (addrC (expR (- nu * a1)) (expR (- nu * a2))) .
lra.
Qed.

Lemma orI_stl (e : expr Bool_T_def) : nu.-[[e `\/ e]]_stl = nu.-[[e]]_stl.
Proof.
rewrite /= /stl_or /stl_or_gt0 /stl_or_lt0 /max_dev
/sumR !big_cons !big_nil/= !addr0.
rewrite !maxrxxx.
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

Lemma orC_stl (e1 e2 : expr Bool_T_def) :
  nu.-[[e1 `\/ e2]]_stl  = nu.-[[e2 `\/ e1]]_stl.
Proof.
rewrite /= /stl_or /stl_or_gt0 /stl_or_lt0 /max_dev
/sumR !big_cons !big_nil/= !addr0.
rewrite !maxrxyx !maxxx.
set a_max := maxr (nu.-[[e2]]_stl) (nu.-[[e1]]_stl).
have -> : maxr (nu.-[[e1]]_stl) (nu.-[[e2]]_stl) = a_max.
  by rewrite /a_max/maxr; case: ifPn => //; case: ifPn => //; lra.
set a1 := (a_max - nu.-[[e1]]_stl) * a_max^-1.
set a2 := (a_max - nu.-[[e2]]_stl) * a_max^-1.
set d1 := expR (nu * a1) + expR (nu * a2).
have -> : expR (nu * a2) + expR (nu * a1) = d1 by rewrite addrC.
case: ifPn; first by rewrite addrC.
by case: ifPn; first by rewrite addrC.
Qed.

Lemma stl_translations_Vector_coincide : forall n (e : @expr R (Vector_T n)),
  nu.-[[ e ]]_stl = [[ e ]]_B.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ _ e2 erefl JMeq_refl).
Qed.

Lemma stl_translations_Index_coincide : forall n (e : expr (Index_T n)),
  nu.-[[ e ]]_stl = [[ e ]]_B.
Proof. by dependent induction e. Qed.

Lemma stl_translations_Real_coincide (e : expr Real_T):
  nu.-[[ e ]]_stl = [[ e ]]_B.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl)
        ?(IHe2 e2 erefl JMeq_refl)
        ?(IHe e erefl JMeq_refl) //=.
by rewrite stl_translations_Vector_coincide stl_translations_Index_coincide.
Qed.

Definition is_stl b (x : R) := if b then x >= 0 else x < 0.

Lemma stl_nary_inversion_andE1 (Es : seq (expr Bool_T_undef)) :
  is_stl true (nu.-[[ ldl_and Es ]]_stl) ->
  forall i, (i < size Es)%N ->
    is_stl true (nu.-[[ nth (ldl_bool undef false) Es i ]]_stl).
Proof.
case: Es => // a l.
rewrite /is_stl /= /stl_and /stl_and_gt0 /stl_and_lt0 /min_dev.
rewrite /sumR !map_cons !big_map.
set a_min := \big[minr/nu.-[[a]]_stl]_(j <- l) nu.-[[j]]_stl.
case: ifPn=>[hminlt0|].
  have /=[y ymem ylt0] := minrltx hminlt0.
  rewrite !big_seq.
  under eq_bigr => i il do rewrite map_cons big_map big_min_cons//.
  under [X in _ / X]eq_bigr => i il do rewrite map_cons big_map big_min_cons//.
  rewrite/= leNgt.
  rewrite pmulr_llt0 ?invr_gt0; last first.
    rewrite sumr_gt0//=.
      by move => i _ _; rewrite expR_ge0.
    by exists y; rewrite ymem expR_gt0.
  rewrite sumr_lt0//.
    by move => i _ _; rewrite nmulr_rle0 ?expR_ge0// nmulr_rlt0// expR_gt0.
  by exists y; rewrite !nmulr_rlt0 ?expR_gt0//.
rewrite -leNgt; move/minrgex => h.
by case: ifPn => _ _ i isize; rewrite h// mem_nth.
Qed.

Lemma stl_nary_inversion_andE0 (Es : seq (expr Bool_T_undef)) :
  is_stl false (nu.-[[ ldl_and Es ]]_stl) ->
  exists2 i, is_stl false (nu.-[[ nth (ldl_bool undef false) Es i ]]_stl) &
             (i < size Es)%N.
Proof.
case: Es => [|a l]; first by rewrite /= ltr10.
rewrite /is_stl /= /stl_and /= big_map.
set a_min := \big[minr/nu.-[[a]]_stl]_(j <- l) nu.-[[j]]_stl.
case: ifPn=>[hminlt0 _|].
  have [x xmem hlt0] := minrltx hminlt0.
  exists (index x (a :: l)).
    by rewrite nth_index ?xmem// hlt0.
  by rewrite  index_mem xmem.
rewrite -leNgt => hminge0.
case: ifPn => _; last by rewrite lt_irreflexive.
rewrite ltNge mulr_ge0// ?invr_ge0 /sumR big_cons !big_map big_seq_cond addr_ge0 ?mulr_ge0 ?expR_ge0 ?sumr_ge0//=.
  by apply: (minrgex hminge0); rewrite mem_head.
all: move=> i /andP[il _]; rewrite ?mulr_ge0 ?expR_ge0//.
by apply: (minrgex hminge0); rewrite in_cons il orbT.
Qed.

Lemma stl_nary_inversion_orE1 (Es : seq (expr Bool_T_undef)) :
  is_stl true (nu.-[[ ldl_or Es ]]_stl) ->
  exists2 i, is_stl true (nu.-[[ nth (ldl_bool _ false) Es i ]]_stl) &
             (i < size Es)%N.
Proof.
case: Es => [|a l]; first by rewrite /= ler0N1.
rewrite/is_stl/= /stl_or/stl_or_gt0/stl_or_lt0/max_dev /sumR !map_cons !big_map.
set a_max := \big[maxr/nu.-[[a]]_stl]_(j <- l) nu.-[[j]]_stl.
case: ifPn=> [hmaxgt0 _|].
  have [x xmem hgt0] := maxrgtx hmaxgt0.
  exists (index x (a :: l)).
    by rewrite nth_index ?xmem// (ltW hgt0).
  by rewrite index_mem xmem.
rewrite -leNgt => hmaxle0.
case: ifPn=>[hmaxlt0|].
  have /= := maxrltx hmaxlt0.
  rewrite !big_seq.
  under eq_bigr => i il do rewrite map_cons big_map big_max_cons//.
  under [X in _ / X]eq_bigr => i il do rewrite map_cons big_map big_max_cons//.
  rewrite leNgt=> hilt0.
  rewrite pmulr_llt0 ?invr_gt0; last first.
    rewrite sumr_gt0//=.
      by move => i _ _; rewrite expR_ge0.
    by exists a; rewrite mem_head expR_gt0.
  rewrite sumr_lt0//.
    by move => i imem _; rewrite nmulr_rle0 ?expR_ge0 ?hilt0.
  exists a.
  by rewrite mem_head nmulr_rlt0 ?expR_gt0 ?hilt0 ?mem_head.
rewrite -leNgt => hmaxge0 _.
have /= [x xmem hxge0] := maxrgex hmaxge0.
exists (index x (a :: l)).
  by rewrite nth_index ?xmem// hxge0.
by rewrite index_mem xmem.
Qed.

Lemma stl_nary_inversion_orE0 (Es : seq (expr Bool_T_undef)) :
  is_stl false (nu.-[[ ldl_or Es ]]_stl) ->
  forall i, (i < size Es)%N ->
    is_stl false (nu.-[[ nth (ldl_bool undef false) Es i ]]_stl).
Proof.
case: Es => // a l.
rewrite/is_stl/= /stl_or/stl_or_gt0/stl_or_lt0 big_map.
set a_max := \big[maxr/nu.-[[a]]_stl]_(j <- l) nu.-[[j]]_stl.
case: ifPn=>[hmaxgt0|].
  rewrite !map_cons/sumR !big_map!big_seq.
  under eq_bigr => i il do rewrite big_map big_max_cons// -/a_max.
  by rewrite ltNge mulr_ge0// /sumR ?invr_ge0 ?sumr_ge0// => [i _/=|i _/=]; rewrite ?mulr_ge0// ?expR_ge0// ltW.
rewrite -leNgt => h.
case: ifPn; last by rewrite ltxx.
move => hmaxlt0 _ i isize.
by apply: (maxrltx hmaxlt0); rewrite mem_nth.
Qed.

Lemma stl_soundness (e : expr Bool_T_undef) b :
  is_stl b (nu.-[[ e ]]_stl) -> [[ e ]]_B = b.
Proof.
dependent induction e using expr_ind'.
- by move: b b0 => [] [] //=; rewrite ?leNgt ?ltrN10 ?ltr10.
- rewrite List.Forall_forall in H.
  move: b => []. rewrite /is_stl.
  + move/stl_nary_inversion_andE1.
    rewrite [bool_translation (ldl_and l)]/= big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    by apply: H => //; rewrite ?h// -In_in mem_nth.
  + move/stl_nary_inversion_andE0.
    rewrite [bool_translation (ldl_and l)]/= big_map big_all.
    elim=>// i i0 isize.
    apply/allPn; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    by rewrite -In_in mem_nth.
- rewrite List.Forall_forall in H.
  move: b => [|].
  + move/stl_nary_inversion_orE1.
    rewrite [bool_translation (ldl_or l)]/= big_map big_has.
    elim=>// i i0 isize.
    apply/hasP; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
  + move/stl_nary_inversion_orE0.
    rewrite [bool_translation (ldl_or l)]/= big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    by apply/negPf; apply: H => //; rewrite ?h// -In_in mem_nth.
- case: c.
  + by case: b; rewrite /is_stl/= ?lee_fin ?lte_fin ?ltNge subr_ge0 !stl_translations_Real_coincide// => /negbTE.
  + case: b; rewrite /is_stl/= ?lee_fin ?lte_fin !stl_translations_Real_coincide.
    by rewrite oppr_ge0 normr_le0 subr_eq0.
    by rewrite oppr_lt0 normr_gt0 subr_eq0 => /negbTE.
Qed.

Lemma andC_stl_nary (s1 s2 : seq (expr Bool_T_def)) :
  perm_eq s1 s2 -> nu.-[[ldl_and s1]]_stl = nu.-[[ldl_and s2]]_stl.
Proof.
case: s1; first by rewrite perm_sym => /perm_nilP ->.
move=> a1 l1; case: s2; first by move/perm_nilP.
move=> a2 l2 pi.
rewrite /=.
have pi2 := @perm_map _ _ (stl_translation nu) _ _ pi.
rewrite (perm_big_minr3 pi2)/=.
rewrite /stl_and/= !big_map !map_cons.
case: ifPn => // ?.
  rewrite /stl_and_lt0 /sumR !big_map.
  congr (_ / _).
    rewrite (perm_big _ pi)/=.
    apply: eq_bigr => i _.
    congr (_ * _).
      congr(_ * _).
        rewrite !map_cons !big_map.
        exact: perm_big.
      by rewrite !map_cons /min_dev !big_map (perm_big _ pi).
    by rewrite !map_cons /min_dev !big_map (perm_big _ pi).
  rewrite (perm_big _ pi)/=.
  apply: eq_bigr => i _.
  by rewrite !map_cons /min_dev !big_map (perm_big _ pi).
case: ifPn => // ?.
rewrite /stl_and_gt0 /sumR !big_map.
congr (_ / _).
  rewrite (perm_big _ pi)/=.
  apply: eq_bigr => i _.
  by rewrite /min_dev !map_cons !big_map (perm_big _ pi).
rewrite (perm_big _ pi)/=.
apply: eq_bigr => i _.
by rewrite /min_dev !map_cons !big_map (perm_big _ pi).
Qed.

End stl_lemmas.

Section stl_and_lemmas.
Local Open Scope ring_scope.
Context {R : realType}.
Variables (nu : R) (M : nat).

Local Notation seq_of_rV := (@MatrixFormula.seq_of_rV _ M.+1).

Lemma stl_and_gt0_const p : stl_and_gt0 nu (seq_of_rV (const_mx p)) = p.
Proof.
rewrite /stl_and_gt0/= {1}/sumR big_map seq_of_rV_const big_nseq.
rewrite min_dev_nseq.
rewrite mulr0 expR0 mulr1.
rewrite iter_addr addr0.
rewrite /sumR big_map big_nseq.
rewrite min_dev_nseq mulr0 expR0 iter_addr addr0.
by rewrite -(mulr_natr p) -mulrA divff ?mulr1.
Qed.

Lemma stl_and_lt0_const p : stl_and_lt0 nu (seq_of_rV (const_mx p)) = p.
Proof.
rewrite /stl_and_lt0/= {1}/sumR big_map seq_of_rV_const big_nseq.
rewrite min_dev_nseq.
rewrite mulr0 expR0 !mulr1.
rewrite iter_addr addr0.
rewrite /sumR big_map !big_nseq.
rewrite min_dev_nseq mulr0 expR0 iter_addr addr0.
rewrite iter_minr//.
by rewrite -(mulr_natr p) -mulrA divff ?mulr1.
Qed.

End stl_and_lemmas.

Section shadow_lifting_stl_and.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variable nu : R.
Variable M : nat.
Hypothesis M0 : M != 0%N.

Local Notation seq_of_rV := (@MatrixFormula.seq_of_rV _ M.+1).
Local Notation stl_and_gt0 := (stl_and_gt0 nu).
Local Notation stl_and_lt0 := (stl_and_lt0 nu).

(* technical lemmas *)
Lemma mip_at_right (p h : R) i : 0 < h ->
  \big[minr/(p + h)]_(i <- seq_of_rV (const_mx p + h *: err_vec i)) i = p.
Proof.
move=> h0.
rewrite big_map/= big_enum/= (bigminD1 i)// ffunE !mxE eqxx mulr1.
rewrite (eq_bigr (fun=> p)); last first.
  by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
rewrite big_const/= iter_minr//; last 2 first.
  by rewrite card_ordS.
  by rewrite lerDl// ltW.
by rewrite /minr ltNge lerDl (ltW h0).
Qed.

Lemma mip_at_left (p h : R) i : h < 0 ->
  \big[minr/(p + h)]_(i <- seq_of_rV (const_mx p + h *: err_vec i)) i = p + h.
Proof.
move=> h0; rewrite big_map/= big_enum/= (bigminD1 i)//.
rewrite ffunE !mxE eqxx mulr1.
rewrite (eq_bigr (fun=> p)); last first.
  by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
by rewrite big_const/= card_ordS iter_minr' ?minxx// gerDl ltW.
Qed.

Lemma mip'_at_right (p h : R) i : h > 0 ->
  \big[minr/p]_(i0 <- seq_of_rV (const_mx p + h *: err_vec i)) i0 = p.
Proof.
move=> h0; rewrite big_map/= big_enum/= (bigminD1 i)//.
rewrite ffunE !mxE eqxx mulr1.
rewrite (eq_bigr (fun=> p)); last first.
  by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
rewrite big_const/=.
rewrite iter_minr//; last by rewrite card_ordS.
by rewrite /minr ltNge lerDl (ltW h0).
Qed.

Lemma mip'_at_left (p h : R) i : h < 0 ->
  \big[minr/p]_(i0 <- seq_of_rV (const_mx p + h *: err_vec i)) i0 = p + h.
Proof.
move=> h0; rewrite big_map/= big_enum/= (bigminD1 i)//.
rewrite ffunE !mxE eqxx mulr1.
rewrite (eq_bigr (fun=> p)); last first.
  by move=> /= j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
by rewrite big_const/= card_ordS iter_minr'// /minr ifT// gtrDl.
Qed.

Lemma shadowlifting_stl_and_gt0_cvg_at_right (p : R) i : 0 < p ->
  h^-1 *
  (stl_and_gt0 (seq_of_rV (const_mx p + h *: err_vec i)) -
   stl_and_gt0 (seq_of_rV (const_mx p))) @[h --> 0^'+] --> (M.+1%:R : R)^-1.
Proof.
move=> p0.
rewrite /= stl_and_gt0_const.
have H h : h > 0 ->
  stl_and_gt0 (seq_of_rV (const_mx p + h *: err_vec i)) =
  (p * M%:R + (p + h) * expR (- nu * (h / p))) / (M%:R + expR (-nu * (h / p))).
  move=> h0.
  rewrite /stl_and_gt0/= {1}/sumR big_map.
  congr (_ / _).
    rewrite big_map/= big_enum/= (bigD1 i)//=.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (_ : min_dev _ _ = h / p); last first.
      rewrite /min_dev mip_at_right//.
      by rewrite -addrA addrCA subrr addr0.
    rewrite (eq_bigr (fun=> p)); last first.
      move=> j ji.
      rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
      rewrite (_ : min_dev _ _ = 0); last first.
        by rewrite /min_dev mip'_at_right// subrr mul0r.
      by rewrite mulr0 expR0 mulr1.
    rewrite big_const/= iter_addr addr0 card_ordS.
    by rewrite addrC mulr_natr.
  rewrite /sumR !big_map/= -enumT /= big_enum/= (bigD1 i)//=.
  rewrite ffunE !mxE eqxx mulr1.
  rewrite (_ : min_dev _ _ = h / p); last first.
    rewrite /min_dev mip_at_right//.
    by rewrite -addrA addrCA subrr addr0.
  rewrite (eq_bigr (fun=> 1)); last first.
    move=> j ji.
    rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite (_ : min_dev _ _ = 0); last first.
      by rewrite /min_dev mip'_at_right// subrr mul0r.
    by rewrite mulr0 expR0.
  rewrite big_const/= iter_addr addr0 card_ordS.
  by rewrite [LHS]addrC.
apply/cvgrPdist_le => /= e e0; near=> t.
rewrite H//= -[X in (_ / _ - X)](mul1r p).
rewrite -[X in (_ / _ - X * _)](@divff _ (M%:R + expR (- nu * (t / p)))); last first.
  by rewrite lt0r_neq0// addr_gt0// ?expR_gt0// ltr0n lt0n.
rewrite (mulrAC _ (_^-1) p) -mulrBl.
have -> : ((p * M%:R) + ((p + t) * expR (- nu * (t / p)))) -
          (M%:R + expR (- nu * (t / p))) * p = t * expR (- nu * (t / p)) by lra.
rewrite !mulrA mulVf// mul1r -(mul1r (M.+1%:R^-1)).
have -> : expR (- nu * t / p) / (M%:R + expR (- nu * t / p)) =
  ((fun t => expR (- nu * t / p)) \*
   (fun t => (M%:R + expR (- nu * t / p)) ^-1)) t by [].
near: t; move: e e0; apply/cvgrPdist_le.
apply: cvgM.
  by under eq_fun do rewrite mulrAC; exact: expR_cvg0.
apply: cvgV; first by rewrite lt0r_neq0.
rewrite -natr1; apply: cvgD; first exact: cvg_cst.
by under eq_fun do rewrite mulrAC; exact: expR_cvg0.
Unshelve. all: end_near. Qed.

Lemma shadowlifting_stl_and_gt0_cvg_at_left (p : R) i : 0 < p ->
  h^-1 *
  (stl_and_gt0 (seq_of_rV (const_mx p + h *: err_vec i)) -
   stl_and_gt0 (seq_of_rV (const_mx p))) @[h --> 0^'-] --> (M.+1%:R : R)^-1.
Proof.
move=> p0.
have H h : h < 0 -> (stl_and_gt0 (seq_of_rV  (const_mx p + h *: err_vec i))) =
                     (p * M%:R * expR (- nu * (- h / (p + h))) + (p + h))
                     /
                     (M%:R * expR (- nu * (- h / (p + h))) + 1).
  move=> h0.
  rewrite /stl_and_gt0/= /sumR/= !big_map -enumT !big_enum/= (bigD1 i)//=.
  congr (_ / _).
    rewrite ffunE !mxE eqxx mulr1 (_ : min_dev _ _ = 0); last first.
      by rewrite /min_dev mip_at_left; lra.
    rewrite mulr0 expR0 mulr1 addrC.
    rewrite (eq_bigr (fun=> p * expR (- nu * (- h / (p + h))))); last first.
      move=> j ji.
      rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
      rewrite (_ : min_dev _ _ = - h / (p + h))//.
      by rewrite /min_dev mip'_at_left//; lra.
    rewrite big_const/= iter_addr addr0 card_ordS.
    by rewrite -[in LHS]mulr_natr mulrAC.
  rewrite /= (bigD1 i)//=.
  rewrite ffunE !mxE eqxx mulr1.
  rewrite (_ : min_dev _ _ = 0); last first.
    by rewrite /min_dev mip_at_left//; lra.
  rewrite (eq_bigr (fun=> (expR (- nu * (- h / (p + h)))))); last first.
    move=> j ji.
    rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite (_ : min_dev _ _ = -h / (p + h))//.
    by rewrite /min_dev mip'_at_left; lra.
  rewrite big_const/= iter_addr addr0 card_ordS.
  by rewrite mulr0 expR0 addrC -[in LHS]mulr_natr mulrC.
apply/cvgrPdist_le => /= e e0; near=> t.
rewrite H//=.
rewrite /= stl_and_gt0_const.
rewrite -[X in (_ / _ - X)](mul1r p).
rewrite -[X in (_ / _ - X * _)](@divff _ (M%:R * expR (- nu * (- t / (p + t))) + 1)); last first.
  rewrite lt0r_neq0// addr_gt0// ?expR_gt0// mulr_gt0//.
    by rewrite ltr0n lt0n.
    by rewrite expR_gt0.
  rewrite (mulrAC _ (_^-1) p) -mulrBl.
  have -> : ((p * M%:R * expR (- nu * (- t / (p + t)))) + (p + t)) -
   ((M%:R * expR (- nu * (- t / (p + t)))) + 1) * p = t by lra.
  have -> : t^-1 * (t / ((M%:R * expR (- nu * (- t / (p + t)))) + 1)) =
    1 / ((M%:R * expR (- nu * (- t / (p + t)))) + 1).
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
  (stl_and_gt0 (seq_of_rV (const_mx p + h *: err_vec i)) -
   stl_and_gt0 (seq_of_rV (const_mx p))) @[h --> 0^'] --> (M.+1%:R : R)^-1.
Proof.
move=> p0; apply/cvg_at_right_left_dnbhs.
- exact/shadowlifting_stl_and_gt0_cvg_at_right.
- exact/shadowlifting_stl_and_gt0_cvg_at_left.
Qed.

Lemma shadowlifting_stl_and_gt0 (p : R) : p > 0 -> forall i,
  ('d (stl_and_gt0 \o seq_of_rV) '/d i) (const_mx p) = M.+1%:R^-1.
Proof.
move=> p0 i.
rewrite /partial /= stl_and_gt0_const.
have := shadowlifting_stl_and_gt0_cvg _ i p0.
rewrite stl_and_gt0_const => /cvg_lim.
by apply; exact: Rhausdorff.
Qed.

Let num' (p x : R) : R := M%:R * expR (- x / (p + x)) +
  expR (- x / (p + x)) * x * M%:R * (x / (x + p)^+2 - (x + p)^-1) +
  expR (- x / (p + x)) * M%:R * p * (x / (x + p)^+2 - (x + p)^-1).

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
  is_derive x 1 (fun x0 => M%:R * (p + x0) * expR (- x0 / (p + x0)) - M%:R * p)
    (num' p x).
Proof.
move=> x0p.
have H1 : derivable (fun x0 => M%:R * (p + x0)) x 1.
  apply: derivableM; first exact: derivable_cst.
  by apply: derivableD; [exact: derivable_cst|exact: derivable_id].
rewrite /num'.
rewrite -[X in is_derive _ _ _ X]subr0.
apply: is_deriveB.
apply: DeriveDef.
  by apply: derivableM; [exact: H1|exact: derivable_DVexpR].
rewrite deriveM; last 2 first.
  exact: H1.
  exact: derivable_DVexpR.
rewrite deriveM; last 2 first.
  exact: derivable_cst.
  exact: derivable_addr.
rewrite derive_comp; last 2 first.
  exact: derivableVD.
  exact: derivable_expR.
rewrite (_ : 'D_1 expR (- x / (p + x)) = expR (- x / (p + x))); last first.
  by rewrite -[in RHS](@derive_expR R).
rewrite deriveD; last 2 first.
  exact: derivable_cst.
  exact: derivable_id.
rewrite derive_cst add0r.
rewrite derive_id.
set MRA := GRing.scale (GRing.natmul (V:=R) (GRing.one R) M) (GRing.one R).
rewrite (_ : MRA = M%:R)//; last by rewrite /MRA /GRing.scale/= mulr1.
rewrite {MRA}.
rewrite derive_cst scaler0 addr0.
rewrite deriveM/=; [|exact: derivable_subr|exact: derivableDV].
rewrite deriveV; last 2 first.
  exact: px_neq0.
  exact: derivable_addr.
rewrite deriveD; last 2 first.
  exact: derivable_cst.
  exact: derivable_id.
rewrite derive_cst add0r.
rewrite derive_id.
set pxA := (X in - x *: X).
rewrite (_ : pxA = (- (p + x) ^- 2))//; last by rewrite /pxA /GRing.scale/= mulr1.
rewrite deriveN; last exact: derivable_id.
rewrite derive_id.
rewrite scalerN1.
rewrite [X in X + _ = _]scalerAl.
rewrite scalerCA.
rewrite -[LHS]mulrDr.
rewrite [X in _ = X + _ + _]mulrC.
rewrite -!mulrA.
rewrite -2!mulrDr.
congr (_ * _).
rewrite [in LHS]addrC.
rewrite -!addrA; congr (_ + _).
rewrite mulrCA -mulrDr.
rewrite -[LHS]mulrA.
congr (M%:R * _).
rewrite -mulrDl (addrC p).
congr (_ * _).
congr (_ - _).
rewrite scaleNr.
rewrite -mulrN.
by rewrite opprK.
Qed.

Let den' (p x : R) : R := expR (nu * (x / (x + p))) +
  M%:R +
  expR (nu * (x / (x + p))) * x * (- x * nu / (x + p)^+2 + nu / (x + p)).

Lemma is_derive_den' (x : R) p :
  x \in (ball 0 p : set R) ->
  is_derive x 1 (fun x => x * (M%:R + (expR (nu * - x / (p + x)))^-1))
    (den' p x).
Proof.
move=> x0p.
have H1 : derivable (fun y => expR (nu * - y / (p + y))) x 1.
  apply: derivable_comp; first exact: derivable_expR.
  apply: derivableM; last exact: derivableDV.
  by apply: derivableM; [exact: derivable_cst|exact: derivable_subr].
apply: DeriveDef.
  apply: derivableM; first exact: derivable_id.
  apply: derivableD; first exact: derivable_cst.
  by apply: derivableV; [by rewrite expR_eq0|exact: H1].
rewrite /den' deriveM; last 2 first.
  exact: derivable_id.
  apply: derivableD; first exact: derivable_cst.
  by apply: derivableV; [by rewrite expR_eq0|exact: H1].
rewrite deriveD; last 2 first.
  exact: derivable_cst.
  by apply: derivableV; [by rewrite expR_eq0|exact: H1].
rewrite derive_cst add0r/=.
rewrite deriveV/=; last 2 first.
  by rewrite expR_eq0.
  exact: H1.
rewrite derive_comp; last 2 first.
  under eq_fun.
    move=> z.
    rewrite -mulrA.
    over.
  apply: (@derivableM _ _ (cst nu)).
    exact: derivable_cst.
  exact: derivableVD.
  exact: derivable_expR.
rewrite (_ : 'D_1 expR (nu * - x / (p + x)) = expR (nu * - x / (p + x))); last first.
  by rewrite -[in RHS](@derive_expR R).
rewrite deriveM; last 2 first.
  apply: derivableM; first exact: derivable_cst.
  exact: derivable_subr.
  exact: derivableDV.
rewrite deriveV; last 2 first.
  exact: px_neq0.
  exact: derivable_addr.
rewrite deriveM; last 2 first.
  exact: derivable_cst.
  exact: derivable_subr.
rewrite derive_cst scaler0 addr0.
rewrite deriveN; last exact: derivable_id.
rewrite deriveD; last 2 first.
  exact: derivable_cst.
  exact: derivable_id.
rewrite derive_id derive_cst add0r.
rewrite scalerN1.
rewrite [X in _ + X = _]/GRing.scale/= mulr1.
rewrite addrCA.
rewrite -[RHS]addrA [RHS]addrCA.
congr (_ + _).
rewrite [LHS]addrC.
congr (_ + _).
  rewrite -expRN mulrN mulNr opprK (addrC p).
  by rewrite mulrA.
rewrite -[RHS]mulrA.
rewrite [RHS]mulrCA.
congr (_ * _).
rewrite [in LHS]scaleNr.
rewrite [X in - X]mulrA.
rewrite -[in LHS]mulrN.
congr (_ * _).
  rewrite !(mulrN,mulNr) !expRN.
  rewrite -exprVn invrK expr2.
  rewrite -[LHS]mulrA divff ?mulr1//.
  rewrite (addrC p)//.
  by rewrite mulrA.
  by rewrite expR_eq0.
rewrite !(mulrN,mulNr,scaleNr,scalerN,opprK) opprB.
rewrite [RHS]addrC; congr (_ - _).
  by rewrite [LHS]mulrC (addrC p).
rewrite (mulrC nu) scalerA (addrC p).
by rewrite /GRing.scale/= mulr1.
Qed.

Lemma shadowlifting_stl_and_lt0_cvg_at_right (p : R) i : p > 0 ->
  h^-1 *
  (stl_and_lt0 (seq_of_rV (const_mx p + h *: err_vec i)) -
   stl_and_lt0 (seq_of_rV (const_mx p))) @[h --> 0^'+] --> (M.+1%:R : R)^-1.
Proof.
move=> p0.
rewrite /= stl_and_lt0_const.
have H h : h > 0 ->
  stl_and_lt0 (seq_of_rV (const_mx p + h *: err_vec i)) =
  (M%:R  * p + p * expR (h / p) * expR (nu * (h / p))) /
  (M%:R + expR (nu * (h / p))).
  move=> h0.
  rewrite /stl_and_lt0/= {1}/sumR big_map.
  congr (_ / _).
    rewrite big_map/= big_enum/= (bigD1 i)//=.
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (_ : min_dev _ _ = h / p); last first.
      rewrite /min_dev mip_at_right//.
      by rewrite -addrA addrCA subrr addr0.
    rewrite mip_at_right//.
    rewrite (eq_bigr (fun=> p)); last first.
      move=> j ji.
      rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
      rewrite (_ : min_dev _ _ = 0); last first.
        by rewrite /min_dev mip'_at_right// subrr mul0r.
      by rewrite mip'_at_right// mulr0 expR0 !mulr1.
    rewrite big_const/= iter_addr addr0 card_ordS addrC.
    by rewrite (mulrC M%:R p) mulr_natr.
  rewrite /sumR !big_map/= -enumT big_enum/= (bigD1 i)//=.
  rewrite ffunE !mxE eqxx mulr1.
  rewrite (_ : min_dev _ _ = h / p); last first.
    by rewrite /min_dev mip_at_right// -addrA addrCA subrr addr0.
  rewrite addrC; congr (_ + _).
  rewrite (eq_bigr (fun=> 1)).
    by rewrite big_const/= card_ordS iter_addr addr0.
  move=> j ji; rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
  rewrite (_ : min_dev _ _ = 0); last first.
    by rewrite /min_dev mip'_at_right// subrr mul0r.
  by rewrite mulr0 expR0.
apply/cvgrPdist_le => /= eps eps0; near=> x.
rewrite [X in normr (_ - X)](_ : _ =
    (M%:R + expR (nu * (x / p)))^-1 *
    expR (nu * (x / p)) *
    ((expR (x / p) - 1) / (x / p))); last first.
  rewrite H//.
  set a := expR (x / p).
  set b := expR (nu * (x / p)).
  rewrite invf_div !mulrA mulrC.
  congr (_ / _).
  rewrite -[X in _ - X](mulr1 p).
  rewrite -[X in _ - (_ * X)](@mulVf _ (M%:R + b)).
    rewrite mulrCA mulrC -mulrBr -!mulrA.
    congr (_ * _).
    rewrite -mulrC -mulrDr -mulrBr.
    nra.
  by rewrite gt_eqF// addr_gt0// ?ltr0n ?lt0n// expR_gt0.
near: x; move: eps eps0; apply/cvgrPdist_le.
rewrite -(mulr1 M.+1%:R^-1).
rewrite -(mulr1 (M.+1%:R^-1 * 1)).
apply: cvgM.
  apply: cvgM.
    apply: cvgV; first by [].
    rewrite -natr1; apply: cvgD; first exact: cvg_cst.
    by under eq_fun do rewrite mulrCA mulrC; exact: expR_cvg0.
  by under eq_fun do rewrite mulrCA mulrC; exact: expR_cvg0.
have H1 (x : R) : is_derive x 1 ( *%R^~ p^-1) p^-1.
  rewrite [X in is_derive _ _ X _](_ : _ = p^-1 *: id); last first.
    by apply/funext => y /=; rewrite mulrC.
  rewrite [X in is_derive _ _ _ X](_ : _ = p^-1 *: (1:R))//.
    exact: is_deriveZ.
  by rewrite /GRing.scale/= mulr1.
apply: (@lhopital_right R (fun x => expR (x / p) - 1)
    (fun x => p^-1 * expR (x / p)) (fun x => x / p) (fun=> p^-1) 0 _
    (nbhsx_ballx _ _ ltr01)).
- move=> x xU.
  rewrite -[X in is_derive _ _ _ X]subr0.
  apply: is_deriveB => /=.
  rewrite mulrC.
  exact: is_derive1_comp.
- by rewrite mul0r expR0 subrr.
- by rewrite mul0r.
- by near=> t; rewrite gt_eqF// invr_gt0.
- under eq_fun.
    move=> x; rewrite mulrAC divff ?gt_eqF ?invr_gt0// mul1r.
    over.
  rewrite -expR0; apply: continuous_cvg; first exact: continuous_expR.
  rewrite -[X in _ --> X](mul0r p^-1).
  apply: cvgM; last exact: cvg_cst.
  exact/cvg_at_right_filter/cvg_id.
Unshelve. all: end_near. Qed.

Lemma shadowlifting_stl_and_lt0_cvg_at_left (p : R) i : p > 0 ->
  h^-1 *
  (stl_and_lt0 (seq_of_rV (const_mx p + h *: err_vec i)) -
   stl_and_lt0 (seq_of_rV (const_mx p))) @[h --> 0^'-] --> (M.+1%:R : R)^-1.
Proof.
move=> p0.
rewrite /= stl_and_lt0_const.
have H h : h < 0 ->
  stl_and_lt0 (seq_of_rV (const_mx p + h *: err_vec i)) =
  (((p + h) * M%:R * expR (- h / (p + h)) * expR (nu * (- h / (p + h))) + p + h) /
  (M%:R * expR (nu * (- h / (p + h))) + 1)).
  move=> h0.
  rewrite /stl_and_lt0/= /sumR/= !big_map -enumT !big_enum/= (bigD1 i)//=.
  congr (_ / _).
    rewrite ffunE !mxE eqxx mulr1.
    rewrite (_ : min_dev _ _ = 0); last by rewrite /min_dev mip_at_left//; lra.
    rewrite mulr0 expR0 !mulr1 addrC.
    rewrite (eq_bigr (fun=> (p + h) * expR (- h / (p + h)) *
                            expR (nu * (- h / (p + h))))); last first.
      move=> j ji.
      rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
      rewrite (_ : min_dev _ _ = -h / (p + h)); last first.
        by rewrite /min_dev mip'_at_left//; lra.
      by rewrite mip'_at_left.
    rewrite big_const/= iter_addr addr0 card_ordS mip_at_left//.
    by rewrite -[in LHS]mulr_natl !mulrA (mulrC (M%:R)) addrA.
  rewrite /= (bigD1 i)//=.
  rewrite ffunE !mxE eqxx mulr1.
  rewrite (_ : min_dev _ _ = 0); last by rewrite /min_dev mip_at_left; lra.
  rewrite (eq_bigr (fun=> expR (nu * (- h / (p + h))))); last first.
    move=> j ji.
    rewrite ffunE !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite (_ : min_dev _ _ = -h / (p + h))//.
    by rewrite /min_dev mip'_at_left//; lra.
  rewrite big_const/= iter_addr addr0 card_ordS.
  by rewrite mulr0 expR0 addrC -[in LHS]mulr_natr mulrC.
apply/cvgrPdist_le => /= eps eps0; near=> x.
pose a x := expR (nu * - x / (p + x)).
pose b x := expR (- x / (p + x)).
pose num x := M%:R * (p + x) * b x - M%:R * p.
pose den x := x * (M%:R + (a x)^-1).
have ? : a x != 0 by rewrite ?gt_eqF ?expR_gt0.
have ? : (M%:R * a x) + 1 != 0.
  by rewrite gt_eqF// addr_gt0// mulr_gt0// ?expR_gt0// ltr0n// lt0n.
rewrite [X in normr (_ - X)](_ : _ =
    (a x * (M%:R + (a x)^-1))^-1 + num x / den x); last first.
  rewrite /= H// mulrA -/(b x) -/(a x).
  rewrite -[X in _ - X](mul1r p) -[X in _ - (X * p)](@mulfV _ (((M%:R * a x) + 1)))//.
  rewrite -(mulrAC _ p) -mulrBl (mulrDl _ _ p) mul1r opprD !addrA.
  rewrite [X in _ * (X / _)](_ : _ =
    (p + x) * M%:R * b x * a x + x - M%:R * a x * p); last first.
    by rewrite -!addrA !(addrC p) -!addrA (addrC (-p)) subrr addr0.
  rewrite (_ : _ / _ = a x * ((p + x) * M%:R * b x + x * (a x)^-1 - M%:R * p)
                       / (a x * (M%:R + (a x)^-1))); last first.
    congr (_ / _); last by rewrite mulrDr mulfV// mulrC.
    rewrite !mulrDr (mulrC (a x) (_ / _)) -(mulrA x) (@mulVf _ (a x))// mulr1.
    by rewrite !mulrN {1}(mulrC (a x)) [in RHS](mulrC (a x)) -!mulrA (mulrC p).
  rewrite -addrAC mulrDr (mulrC (a x) (_ / _)) -(mulrA x) (@mulVf _ (a x))// mulr1.
  rewrite mulrA (mulrDr (x^-1)) mulrDl addrC.
  congr (_ + _).
    by rewrite mulVf// mul1r.
  rewrite !invrM'// (mulrC (a x)) !mulrA; congr(_/_).
  rewrite -mulrA mulfV// mulr1 mulrC; congr(_/_).
  by rewrite /num [in RHS](mulrC (M%:R)).
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
  rewrite -(mul1r (M.+1%:R)).
  apply: cvgM; first exact: a01.
  rewrite -natr1.
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
apply: (@lhopital_left R _ (num' p) _ (den' p) 0 _ (nbhsx_ballx _ _ p0)).
- by move=> x; apply: is_derive_num'.
- by move=> x; exact: is_derive_den'.
- by rewrite oppr0 mul0r expR0 mulr1 addr0 subrr.
- by rewrite mul0r.
- have H2 : (expR (nu * (x / (x + p))) + M%:R +
      expR (nu * (x / (x + p))) * x * (- x * nu / (x + p) ^+ 2 + nu / (x + p)))
      @[x --> (0:R)^'] --> ((1:R) + M%:R).
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
  by apply: cvgr_neq0; [exact: H2|rewrite gt_eqF].
- rewrite -{2}(mul0r (den' p 0)^-1).
  have H2 : expR (nu * (x / (x + p))) @[x --> 0^'-] -->
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
      by apply: cvgD; [exact: H2|exact: cvg_cst].
    apply: cvgM.
      by apply: cvgM; [exact: H2|exact/cvg_at_left_filter/cvg_id].
    apply: cvgD.
      by apply: cvg_at_left_filter; exact: H1.
    apply: cvgM; first exact: cvg_cst.
    apply: cvgV; first by rewrite add0r gt_eqF.
    by apply: cvgD; [exact/cvg_at_left_filter/cvg_id|exact: cvg_cst].
  rewrite /num'.
  pose c x := expR (nu * (x / (x + p))).
  rewrite -{2}(mulr0 (M%:R * b 0 / (0 + p))).
  apply: cvg_trans.
    apply: (@near_eq_cvg _ _ _ _ (fun (x : R) => M%:R * b x / (x + p) * x)).
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
    rewrite mulrDr mulrN1 addrCA (mulrC _ M%:R) subrr addr0.
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
  (stl_and_lt0 (seq_of_rV (const_mx p + h *: err_vec i)) -
   stl_and_lt0 (seq_of_rV (const_mx p))) @[h --> 0^'] --> (M.+1%:R : R)^-1.
Proof.
move=> p0.
apply/cvg_at_right_left_dnbhs.
- exact/shadowlifting_stl_and_lt0_cvg_at_right.
- exact/shadowlifting_stl_and_lt0_cvg_at_left.
Unshelve. all: end_near. Qed.

Lemma shadowlifting_stl_and_lt0 (p : R) : p > 0 -> forall i,
  ('d (stl_and_lt0 \o seq_of_rV) '/d i) (const_mx p) = M.+1%:R^-1.
Proof.
move=> p0 i.
rewrite /partial.
apply/cvg_lim => //=.
by apply: shadowlifting_stl_and_lt0_cvg.
Qed.

Definition stl_and (v : 'rV[R]_M.+1) :=
  let A := map (stl_translation nu \o ldl_real) (seq_of_rV v) in
  let a0 := stl_translation nu (ldl_real (v ``_ 0)) in
  let a_min : R := \big[minr/a0]_(i <- A) i in
  if a_min < 0 then
    stl_and_lt0 (a0 :: A)
  else if a_min > 0 then
    stl_and_gt0 (a0 :: A)
  else 0.

End shadow_lifting_stl_and.
