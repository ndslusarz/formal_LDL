From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical reals ereal signed topology derive.
From mathcomp Require Import normedtype sequences exp measure lebesgue_measure.
From mathcomp Require Import lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra ldl.

(**md**************************************************************************)
(* # Goedel                                                                   *)
(*                                                                            *)
(* - product_and v with v : 'rV_n                                             *)
(*   $\Pi_{i < n} v_i$                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Section translation_lemmas.
Local Open Scope ring_scope.
Local Open Scope ldl_scope.
Context {R : realType}.
Variables (l : DL) (p : R).
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (@translation R l p _ e).

Lemma translations_Network_coincide:
  forall n m (e : expr (Fun_T n m)), [[ e ]]_l = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  [[ e ]]_l = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ p1 _ e2 erefl JMeq_refl).
Qed.

Lemma translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_l = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma translations_Real_coincide (e : expr Real_T):
  [[ e ]]_l = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite translations_Vector_coincide translations_Index_coincide.
Qed.

Lemma translate_Bool_T_01 dl (e : expr Bool_N) :
  0 <= [[ e ]]_ dl <= 1.
Proof.
dependent induction e using expr_ind'.
- rewrite /=; case b; lra.
- move: H. case: dl; rewrite /=; move=> /List.Forall_forall H.
  + rewrite /sumR/maxr. case: ifP.
    * by lra.
    * move=> /negbT; rewrite -leNgt => -> /=.
      rewrite big_map -lerBrDr subrr subr_le0 sum_01// => e el0.
      by rewrite (andP (H e _ _ _ _)).2 //; exact/In_in.
  + rewrite /sumR/maxr. case: ifP.
    * by lra.
    * move=> /negbT; rewrite -leNgt => -> /=.
      by rewrite big_map gerBl ?powR_ge0.
  + apply/andP; split.
    * rewrite /minR big_seq.
      rewrite le_bigmin// => i /mapP[x xl0 ->].
      by apply: (andP (@H _ _ _ _ _)).1 => //; rewrite -In_in.
    * rewrite /minR big_map big_seq.
      rewrite bigmin_idl.
      suff : forall (x y : R), minr x y <= x => // x y.
      by rewrite /minr; case: ifPn; lra.
  + rewrite /prodR.
    apply: prod01 => e.
    move/mapP => [x xl0 ->].
    by apply: H _ _ _ _ _ => //; rewrite -In_in.
- move: H. case: dl; rewrite /=; move=> /List.Forall_forall H.
  + rewrite /sumR/minr. case: ifP.
    * move=> /ltW ->.
      rewrite andbT big_map big_seq sumr_ge0// => e.
      by move=> /In_in/H /(_ e erefl) /(_ _)/andP[|].
    * by lra.
  + rewrite /sumR/minr. case: ifP.
    * move=> /ltW ->.
      by rewrite andbT big_map big_seq powR_ge0.
    * by lra.
  + rewrite /maxR big_map big_seq.
    apply/andP; split.
    * rewrite bigmax_idl.
      suff : forall (x y : R), x <= maxr x y => // x y.
      by rewrite /maxr; case: ifPn; lra.
    * rewrite bigmax_le ?ler01// => i il0.
      by apply: (andP (H _ _ _ _ _)).2 => //; rewrite -In_in.
  + rewrite /product_dl_prod big_map product_dl_mul_seq_01=> //i il0.
    by apply: H => //; rewrite -In_in.
(*- move/List.Forall_forall in H.
  have [il0|il0] := ltP i (size l0).
    rewrite (H (nth (Bool c false) l0 i))//.
    by apply/In_in; rewrite mem_nth.
  by rewrite nth_default//= lexx ler01.*)
- move: IHe => /(_ e erefl JMeq_refl).
  case dl => //=; set a := [[e]]_ _; lra.
- case: c => /=; case: ifP => ?.
  - by case: ([[e1]]_dl <= [[e2]]_dl)%R; rewrite lexx ler01.
  - by rewrite le_maxr lexx orbT/= le_maxl ler01 gerBl// le_maxr lexx orbT.
  - by case: ([[e1]]_dl == [[e2]]_dl); rewrite lexx ler01.
  - by rewrite le_maxr lexx orbT/= le_maxl ler01 gerBl// normr_ge0 andTb.
Qed.

Lemma nary_inversion_andE1 (Es : seq (expr (Bool_N)) ) :
  [[ ldl_and Es ]]_ l = 1 -> (forall i, (i < size Es)%N -> [[ nth (ldl_bool _ false) Es i ]]_ l = 1).
Proof.
have H := translate_Bool_T_01 l. move: H.
case: l => /=; move => H.
- move/eqP. rewrite maxr01 /sumR eq_sym -subr_eq subrr eq_sym subr_eq0.
  move/eqP; rewrite big_map psumr_eqsize.
  + move => h i iEs.
    move: h => /(_ (nth (ldl_bool _ false) Es i)).
    apply.
    apply/(nthP (ldl_bool _ false)).
    by exists i.
  + move => i //=.
    move: (H i); set a := [[i]]_ _; lra.
- move/eqP.
  rewrite maxr01 eq_sym addrC -subr_eq subrr eq_sym oppr_eq0 powR_eq0 invr_eq0 => /andP [+ _].
  + rewrite /sumR big_map psumr_eq0.
    move => /allP h i iEs.
    apply/eqP.
    move: h => /(_ (nth (ldl_bool _ false) Es i)).
    rewrite implyTb powR_eq0 subr_eq0 eq_sym (gt_eqF (lt_le_trans _ p1))// ?andbT.
    apply.
    apply/(nthP (ldl_bool _ false)).
    by exists i.
  + move => i //=.
    move: (H i). rewrite le_pow_01.
    * lra.
    * move: (H i); set a := [[i]]_ _; lra.
- move/eqP.
  rewrite /minR big_map=>/bigmin_eqP/= => h i iEs.
  apply/eqP.
  rewrite eq_sym eq_le.
  rewrite ((andP (H _)).2) h//.
  exact: mem_nth.
- move/eqP. rewrite /prodR big_map.
  move => h i iEs.
  apply (@prod1_01 _ (map (@translation R product p (Bool_T _)) Es)) => // [e||].
  - by move=> /mapP[x _ ->].
  - by apply/eqP; rewrite big_map.
  - by apply/mapP; eexists; last reflexivity; exact: mem_nth.
Qed.

Lemma nary_inversion_andE0 (Es : seq (expr (Bool_N)) ) :
  l <> Lukasiewicz -> l <> Yager ->
    [[ ldl_and Es ]]_ l = 0 -> (exists (i : nat), ([[ nth (ldl_bool _ false) Es i ]]_ l == 0) && (i < size Es)%nat).
Proof.
have H := translate_Bool_T_01. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move => l1 l2; move/eqP.
  rewrite /minR big_map.
  elim: Es.
  + by rewrite big_nil oner_eq0.
  + move=> a l0 IH.
    rewrite big_cons {1}/minr.
    case: ifPn => _; first by exists 0%nat; rewrite ltn0Sn andbT.
    move/IH => [i i0].
    by exists i.+1.
- move=> l1 l2 /eqP.
  rewrite /prodR big_map prodf_seq_eq0 => /hasP[e eEs/= /eqP e0].
  move/(nthP (ldl_bool _ false)) : eEs => [i iEs ie].
  by exists i; rewrite ie e0 eqxx.
Qed.

Lemma nary_inversion_orE1 (Es : seq (expr (Bool_N)) ) :
  l <> Lukasiewicz -> l <> Yager ->
    [[ ldl_or Es ]]_ l = 1 -> (exists i, ([[ nth (ldl_bool _ false) Es i ]]_ l == 1) && (i < size Es)%nat).
Proof.
have H := translate_Bool_T_01 l. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move => l1 l2; move/eqP.
  rewrite /maxR big_map big_seq.
  elim: Es.
  + by rewrite big_nil eq_sym oner_eq0.
  + move=> a l0 IH.
    rewrite -big_seq big_cons {1}/maxr.
    case: ifPn => [_|_ a1]; last by exists 0%nat; rewrite a1 ltn0Sn.
    rewrite big_seq; move/IH => [i i1].
    by exists i.+1.
- move => l1 l2 /eqP.
  rewrite /product_dl_prod big_map big_seq.
  elim: Es.
  + by rewrite big_nil eq_sym oner_eq0.
  + move=> a l0 IH.
    rewrite -big_seq big_cons {1}/product_dl_mul.
    move/product_dl_mul_inv => [|||/eqP].
    * exact: H.
    * by apply: product_dl_mul_seq_01.
    * by exists 0%nat; rewrite a0 eq_refl ltn0Sn.
    * by rewrite big_seq; move/IH => [x ?]; exists x.+1.
Qed.

Lemma nary_inversion_orE0 (Es : seq (expr (Bool_N)) ) :
    [[ ldl_or Es ]]_ l  = 0 -> (forall i, (i < size Es)%nat -> [[ nth (ldl_bool _ false) Es i ]]_ l = 0).
Proof.
have H := translate_Bool_T_01 l. move: H.
have p0 := lt_le_trans ltr01 p1.
case: l => //=; move => H.
- move/eqP. rewrite minr10 /sumR.
  rewrite big_map.
  rewrite (@bigsum_0x R _ _ Es) => h i.
    by move=> iEs; apply: h; rewrite mem_nth.
  exact: (andP (translate_Bool_T_01 _ _)).1.
- move/eqP; rewrite minr10 /sumR powR_eq0.
  move/andP => [].
  rewrite (@gt_eqF _ _ (p^-1)) ?invr_gt0//.
  rewrite big_seq big_map psumr_eq0=>[|i]; last by rewrite powR_ge0.
  move/allP => h _ i iEs.
  apply/eqP.
  suff: ([[nth (ldl_bool _ false) Es i]]_Yager == 0) && (p != 0).
    by move/andP=>[].
  rewrite -powR_eq0.
  apply: (implyP (h (nth (ldl_bool _ false) Es i) _)).
    by rewrite mem_nth.
  apply/mapP; exists (nth (ldl_bool _ false) Es i) => //.
    by rewrite mem_nth.
- rewrite /maxR/product_dl_prod.
  elim: Es => [h i|a l0 IH h]; first by rewrite nth_nil.
  elim => /=[_|].
  + move: h.
    rewrite big_cons big_map {1}/maxr.
    case: ifPn => // /[swap] ->.
    have := H a; set b := [[_]]_ _; lra.
  + move=> n h' nl0.
    apply: IH => //.
    move: h; rewrite !big_map big_cons {1}/maxr.
    case: ifPn => // /[swap] ->; rewrite -leNgt => bigle0.
    by apply/eqP; rewrite eq_le bigle0 bigmax_idl le_maxr lexx.
- rewrite /product_dl_prod big_map.
  elim: Es => // a l0 IH.
  rewrite big_cons => /eqP /product_dl_prod_inv0 h.
  case => /=[_|i].
  + apply: (h _ _).1 => //.
    exact: product_dl_mul_seq_01.
  + rewrite ltnS => isize.
    apply: IH =>//.
    apply: (h _ _).2 => //.
    exact: product_dl_mul_seq_01.
Qed.

Lemma soundness (e : expr (Bool_N)) b :
  l <> Lukasiewicz -> l <> Yager ->
    [[ e ]]_ l = [[ ldl_bool _ b ]]_ l -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind' => ll ly.
- move: b b0 => [] [] //=; lra.
- rewrite List.Forall_forall in H.
  rewrite [ [[ldl_bool _ b]]_l ]/=.
  move: b => [].
  + move/nary_inversion_andE1.
    rewrite /= big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    by apply: H  => //; rewrite ?h// -In_in mem_nth.
  + move/nary_inversion_andE0.
    rewrite /= big_map big_all.
    elim=>// i /andP[/eqP i0 isize].
    apply/allPn; exists (nth (ldl_bool _ false) l0 i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    by rewrite -In_in mem_nth.
- rewrite List.Forall_forall in H.
  rewrite [ [[ldl_bool _ b]]_l]/=.
  move: b => [].
  + move/nary_inversion_orE1.
    rewrite /= big_map big_has.
    elim=>// i /andP[/eqP i0 isize].
    apply/hasP; exists (nth (ldl_bool _ false) l0 i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
  + move/nary_inversion_orE0.
    rewrite /= big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    by apply/negPf; apply: H => //; rewrite ?h// -In_in mem_nth.
- move=>/=h; rewrite (IHe e erefl JMeq_refl (~~ b) ll ly) ?negbK//.
  move: h; case: b => /=; lra.
- case: c; rewrite //=; rewrite -!translations_Real_coincide;
  set t1 := _ e1; set t2 := _ e2.
  + case: ifPn => [/eqP ->|e12eq].
    have [] := leP (-t2) t2 => /=; case: b; lra.
    rewrite /maxr.
    have ? : 0 < `|t1 + t2| by rewrite normr_gt0 addr_eq0.
    have ? : 0 < `|t1 + t2|^-1 by rewrite invr_gt0.
    case: b; repeat case: ifPn; try lra; rewrite -?leNgt.
    * rewrite pmulr_llt0; lra.
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
      rewrite eq_sym eqr_norml; lra.
  + case: ifP => [/eqP ->|e12eq].
    have [] := eqVneq (-t2) t2 => /=; case: b; lra.
    rewrite /maxr.
    case: b; case: ifPn; try lra; rewrite -?leNgt.
    * move=> _ H.
      have : `|(t1 - t2) / (t1 + t2)|%R == 0.
        clear -H.
        simpl in *.
        by lra.
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

End translation_lemmas.

Section shadow_lifting_product_and.
Context {R : realType}.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Variable M : nat.
Hypothesis M0 : M != 0%N.

Definition product_and {R : fieldType} {n} (u : 'rV[R]_n) : R :=
  \prod_(i < n) u ``_ i.

Lemma shadowlifting_product_andE p : p > 0 ->
  forall i, ('d (@product_and R M.+1) '/d i) (const_mx p) = p ^+ M.
Proof.
move=> p0 i.
rewrite /partial.
have /cvg_lim : h^-1 * (product_and (const_mx p + h *: err_vec i) -
                        @product_and _ M.+1 (const_mx p))
       @[h --> (0:R)^'] --> p ^+ M.
  rewrite /product_and.
  have H : forall h : R, h != 0 ->
      \prod_(x < M.+1) (const_mx p + h *: err_vec i) 0 x -
      \prod_(x < M.+1) const_mx (m:=M.+1) p 0 x = h * p ^+ M.
    move=> h h0; rewrite [X in X - _](bigD1 i)//= !mxE eqxx mulr1.
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

Corollary shadow_lifting_product_and :
  shadow_lifting (@product_and R M.+1).
Proof.
by move=> p p0 i; rewrite shadowlifting_product_andE// exprn_gt0.
Qed.

End shadow_lifting_product_and.


Section Lukasiewicz_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Lukasiewicz_andC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_and s1]]_Lukasiewicz = [[ldl_and s2]]_Lukasiewicz.
Proof.
by move=> pi; rewrite /=/sumR !big_map (perm_big _ pi)/= (perm_size pi).
Qed.

Lemma Lukasiewicz_andC (e1 e2 : expr Bool_N) :
  [[ e1 `/\ e2 ]]_Lukasiewicz = [[ e2 `/\ e1 ]]_Lukasiewicz.
Proof.
rewrite /=/sumR ?big_cons ?big_nil.
by rewrite addr0 addr0 (addrC (_ e1)).
Qed.

Lemma Lukasiewicz_orC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_or s1]]_Lukasiewicz = [[ldl_or s2]]_Lukasiewicz.
Proof.
by move=> pi; rewrite /=/sumR !big_map (perm_big _ pi)/=.
Qed.

Lemma Lukasiewicz_orC (e1 e2 : expr Bool_N) :
  [[ e1 `\/ e2 ]]_Lukasiewicz = [[ e2 `\/ e1 ]]_Lukasiewicz.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
by rewrite /= addr0 addr0 (addrC (_ e1)).
Qed.

Lemma Lukasiewicz_orA (e1 e2 e3 : expr Bool_N) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_Lukasiewicz = [[ ((e1 `\/ e2) `\/ e3) ]]_Lukasiewicz.
Proof.
have := translate_Bool_T_01 p Lukasiewicz e1.
have := translate_Bool_T_01 p Lukasiewicz e2.
have := translate_Bool_T_01 p Lukasiewicz e3.
rewrite /=/sumR/minR?big_cons ?big_nil.
rewrite /minr.
repeat case: ifP; set a := [[_]]__; set b := [[_]]__; set c := [[_]]__; lra.
Qed.

Theorem Lukasiewicz_andA (e1 e2 e3 : expr Bool_N) : (0 < p)%R ->
  [[ (e1 `/\ e2) `/\ e3]]_Lukasiewicz = [[ e1 `/\ (e2 `/\ e3) ]]_Lukasiewicz.
Proof.
have := translate_Bool_T_01 p Lukasiewicz e1.
have := translate_Bool_T_01 p Lukasiewicz e2.
have := translate_Bool_T_01 p Lukasiewicz e3.
rewrite /=/sumR/maxR/minR/product_dl_prod ?big_cons ?big_nil.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
rewrite /maxr.
by repeat case: ifP; lra.
Qed.

End Lukasiewicz_lemmas.

Section Yager_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.
Hypothesis p1 : 1 <= p.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Yager_andC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_and s1]]_Yager = [[ldl_and s2]]_Yager.
Proof.
by move=> pi; rewrite /=/sumR !big_map (perm_big _ pi)/=.
Qed.

Lemma Yager_andC (e1 e2 : expr Bool_N) :
  [[ e1 `/\ e2 ]]_Yager = [[ e2 `/\ e1 ]]_Yager.
Proof.
rewrite /=/sumR ?big_cons ?big_nil.
by rewrite /= addr0 addr0 (addrC (_ `^ _)).
Qed.

Lemma Yager_orC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_or s1]]_Yager = [[ldl_or s2]]_Yager.
Proof.
by move=> pi; rewrite /=/sumR !big_map (perm_big _ pi)/=.
Qed.

Lemma Yager_orC (e1 e2 : expr Bool_N) :
  [[ e1 `\/ e2 ]]_Yager = [[ e2 `\/ e1 ]]_Yager.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
by rewrite /= addr0 addr0 (addrC (_ `^ _)).
Qed.

Lemma Yager_orA (e1 e2 e3 : expr Bool_N) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_Yager = [[ ((e1 `\/ e2) `\/ e3) ]]_Yager.
Proof.
have p0 : 0 < p by rewrite (lt_le_trans ltr01).
have ? : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 p Yager e1.
have := translate_Bool_T_01 p Yager e2.
have := translate_Bool_T_01 p Yager e3.
rewrite /=/sumR/maxR/minR/product_dl_prod ?big_cons ?big_nil.
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

Theorem Yager_andA (e1 e2 e3 : expr Bool_N) : (0 < p) ->
  [[ (e1 `/\ e2) `/\ e3]]_Yager = [[ e1 `/\ (e2 `/\ e3) ]]_Yager.
Proof.
move=> p0.
have pneq0 : p != 0 by exact: lt0r_neq0.
have := translate_Bool_T_01 p Yager e1.
have := translate_Bool_T_01 p Yager e2.
have := translate_Bool_T_01 p Yager e3.
rewrite /=/sumR/maxR/minR/product_dl_prod ?big_cons ?big_nil.
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
  by rewrite -!powRrM !mulVf// powR1 powRr1//; apply; rewrite inE/= in_itv/= ?ler01 ?powR_ge0.
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

End Yager_lemmas.

Section Godel_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma Godel_andI (e : expr Bool_N) : [[ e `/\ e ]]_Godel = [[ e ]]_Godel.
Proof.
rewrite /=/minR ?big_cons ?big_nil.
have := translate_Bool_T_01 p Godel e.
set t1 := _ e.
move => h.
rewrite /=/minr; repeat case: ifP; lra.
Qed.

Lemma Godel_orI (e : expr Bool_N) : [[ e `\/ e ]]_Godel = [[ e ]]_Godel.
Proof.
rewrite /= /maxR !big_cons big_nil.
have /max_idPl -> : 0 <= [[ e ]]_Godel.
  by have /andP[] := translate_Bool_T_01 p Godel e.
by rewrite maxxx.
Qed.

Lemma Godel_andC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_and s1]]_Godel = [[ldl_and s2]]_Godel.
Proof.
by move=> pi; rewrite /=/minR !big_map (perm_big _ pi)/=.
Qed.

Lemma Godel_andC (e1 e2 : expr Bool_N) :
  [[ e1 `/\ e2 ]]_Godel = [[ e2 `/\ e1 ]]_Godel.
Proof.
rewrite /=/minR ?big_cons ?big_nil.
by rewrite /=/minr; repeat case: ifP; lra.
Qed.

Lemma Godel_orC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_or s1]]_Godel = [[ldl_or s2]]_Godel.
Proof.
by move=> pi; rewrite /=/maxR !big_map (perm_big _ pi)/=.
Qed.

Lemma Godel_orC (e1 e2 : expr Bool_N) :
  [[ e1 `\/ e2 ]]_Godel = [[ e2 `\/ e1 ]]_Godel.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
rewrite /=/maxr; repeat case: ifP; lra.
Qed.

Lemma Godel_orA (e1 e2 e3 : expr Bool_N) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_Godel = [[ ((e1 `\/ e2) `\/ e3) ]]_Godel.
Proof.
rewrite /=/sumR/maxR ?big_cons ?big_nil.
rewrite /maxr.
by repeat case: ifPn => //; lra.
Qed.

Theorem Godel_andA (e1 e2 e3 : expr Bool_N) : (0 < p) ->
  [[ (e1 `/\ e2) `/\ e3]]_Godel = [[ e1 `/\ (e2 `/\ e3) ]]_Godel.
Proof.
rewrite /=/sumR/minR !big_cons !big_nil.
have := translate_Bool_T_01 p Godel e1.
have := translate_Bool_T_01 p Godel e2.
have := translate_Bool_T_01 p Godel e3.
set t1 := _ e1.
  set t2 := _ e2.
  set t3 := _ e3.
move => h1 h2 h3 p0.
rewrite /minr. 
by repeat case: ifPn => //; lra.
Qed.

End Godel_lemmas.

Section product_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_ l" := (translation l p e).

Lemma product_andC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_and s1]]_Godel = [[ldl_and s2]]_Godel.
Proof.
by move=> pi; rewrite /=/minR !big_map (perm_big _ pi)/=.
Qed.

Lemma product_andC (e1 e2 : expr Bool_N) :
  [[ e1 `/\ e2 ]]_product = [[ e2 `/\ e1 ]]_product.
Proof.
rewrite /=/prodR ?big_cons ?big_nil.
by rewrite /= mulr1 mulr1 mulrC.
Qed.

Lemma product_orC_nary (s1 s2 : seq (expr Bool_N)) :
  perm_eq s1 s2 -> [[ldl_or s1]]_Godel = [[ldl_or s2]]_Godel.
Proof.
by move=> pi; rewrite /=/maxR !big_map (perm_big _ pi)/=.
Qed.

Lemma product_orC (e1 e2 : expr Bool_N) :
  [[ e1 `\/ e2 ]]_product = [[ e2 `\/ e1 ]]_product.
Proof.
rewrite /=/sumR/maxR/product_dl_prod ?big_cons ?big_nil.
by rewrite /=/product_dl_mul addr0 addr0 mulr0 mulr0 subr0 subr0 mulrC -(addrC (_ e2)).
Qed.

Lemma product_orA (e1 e2 e3 : expr Bool_N) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_product = [[ ((e1 `\/ e2) `\/ e3) ]]_product.
Proof.
rewrite /=/sumR/product_dl_prod ?big_cons ?big_nil.
rewrite /product_dl_mul !addr0 !mulr0 !subr0.
lra.
Qed.

Theorem product_andA (e1 e2 e3 : expr Bool_N) : 0 < p ->
  [[ (e1 `/\ e2) `/\ e3]]_product = [[ e1 `/\ (e2 `/\ e3) ]]_product.
Proof.
rewrite /=/sumR/maxR/minR/product_dl_prod ?big_cons ?big_nil.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
rewrite /prodR/= !big_cons !big_nil.
lra.
Qed.

End product_lemmas.
