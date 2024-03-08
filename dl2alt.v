From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import util ldl.

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.


Section shadow_lifting_dl2_and.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variable M : nat.
Hypothesis M0 : M != 0%N.

Locate "_ --> _".

Definition dl2_and {R : fieldType} {n} (v : 'rV[R]_n) :=
  \sum_(i < n) v ``_ i.

Lemma shadowlifting_dl2_andE (p : R) : p > 0 ->
  forall i, ('d (@dl2_and _ M.+1) '/d i) (const_mx p) = 1.
Proof.
move=> p0 i.
rewrite /partial.
have /cvg_lim : h^-1 * (dl2_and (const_mx p + h *: err_vec i) -
                        dl2_and (n:=M.+1) (const_mx p))
       @[h --> (0:R)^'] --> (1:R)%R.
  rewrite /dl2_and.
  have H : forall h, h != 0 ->
      \sum_(x < M.+1) (const_mx p + h *: err_vec i) ``_ x -
      \sum_(x < M.+1) (const_mx (n:=M.+1) (m:=1) p) ``_ x = h.
    move=> h h0; rewrite [X in X - _](bigD1 i)//= !mxE eqxx mulr1.
    rewrite (eq_bigr (fun=> p)); last first.
      by move=> j ji; rewrite !mxE eq_sym (negbTE ji) mulr0 addr0.
    rewrite [X in _ - X](eq_bigr (fun=> p)); last by move=> *; rewrite mxE.
    rewrite [X in _ - X](bigD1 i)//= (addrC p h) -addrA.
    by rewrite addrA -(addrA h) addrK.
  have : h^-1 * h @[h --> (0:R)^'] --> (1:R)%R.
    have : {near (0:R)^', (fun=> 1) =1 (fun h => h^-1 * h)}.
      near=> h; rewrite mulVf//.
      by near: h;  exact: nbhs_dnbhs_neq.
    by move/near_eq_cvg/cvg_trans; apply; exact: cvg_cst.
  apply: cvg_trans; apply: near_eq_cvg => /=; near=> k.
  by rewrite H//; near: k; exact: nbhs_dnbhs_neq.
by apply; exact: Rhausdorff.
Unshelve. all: by end_near. Qed.

Corollary shadow_lifting_dl2_and :  shadow_lifting (@dl2_and R M.+1).
Proof. by move=> p p0 i; rewrite shadowlifting_dl2_andE. Qed.

End shadow_lifting_dl2_and.

Section dl2_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_dl2'" := (@dl2_translation_alt R _ e).

Lemma dl2_andC (e1 e2 : expr Bool_N) : [[ e1 `/\ e2 ]]_dl2' = [[ e2 `/\ e1 ]]_dl2'.
Proof.
by rewrite /=/sumR ?big_cons ?big_nil /= addr0 addr0 addrC.
Qed.

Lemma dl2_andA (e1 e2 e3 : expr Bool_P) :
  [[ e1 `/\ (e2 `/\ e3) ]]_dl2' = [[ (e1 `/\ e2) `/\ e3 ]]_dl2'.
Proof.
by rewrite /=/sumR ?big_cons ?big_nil !addr0 addrA.
Qed.

Lemma dl2_orC (e1 e2 : expr Bool_P) :
  [[ e1 `\/ e2 ]]_dl2' = [[ e2 `\/ e1 ]]_dl2'.
Proof.
rewrite /=/prodR !big_cons big_nil !mulr1; congr *%R.
by rewrite mulrC.
Qed.

Lemma dl2_orA (e1 e2 e3 : expr Bool_P) :
  [[ e1 `\/ (e2 `\/ e3) ]]_dl2' = [[ (e1 `\/ e2) `\/ e3 ]]_dl2'.
Proof.
rewrite /=/prodR !big_cons big_nil !mulr1.
congr *%R.
rewrite mulrCA.
by rewrite !mulrA.
Qed.

Lemma prodr_seq_eq0 {I : Type} (r : seq I) (P : pred I)
    (F : I -> R) :
  (\big[*%R/1]_(i <- r | P i) F i == 0) = has (fun i => P i && (F i == 0)) r.
Proof.
elim: r => /= [|h t ih]; first by rewrite big_nil oner_eq0.
rewrite big_cons; case: ifPn => Ph /=; last by rewrite ih.
by rewrite mulf_eq0 ih.
Qed.

Lemma dl2_translation_le0 e :
  ([[ e ]]_dl2' <= 0 :> type_translation Bool_P).
Proof.
dependent induction e using expr_ind' => /=.
- by case: b.
- rewrite /sumR big_map big_seq sumr_le0// => t tl.
  move/List.Forall_forall : H => /(_ t); apply => //.
  exact/In_in.
- rewrite /prodR big_map big_seq; have [ol|ol] := boolP (odd (length l)).
    rewrite exprS -signr_odd ol expr1 mulrN1 opprK mul1r.
    have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2' != 0); last first.
      move/existsNP : l0 => [/= x /not_implyP[xl /negP/negPn/eqP x0]].
      rewrite le_eqVlt; apply/orP; left.
      rewrite prodr_seq_eq0; apply/hasP; exists x => //.
      by rewrite xl x0 eqxx.
    apply/ltW; rewrite -sgr_cp0 -big_seq prodrN1.
      by rewrite -signr_odd ol expr1.
    move=> /=e el; rewrite lt_neqAle l0//.
    by move/List.Forall_forall : H => /(_ e); apply => //; exact/In_in.
  rewrite exprS -signr_odd (negbTE ol) expr0 mulN1r.
  rewrite mulN1r oppr_le0.
  have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2' != 0); last first.
    move/existsNP : l0 => [/= x /not_implyP[xl /negP/negPn/eqP x0]].
    rewrite le_eqVlt; apply/orP; left.
    rewrite eq_sym prodr_seq_eq0; apply/hasP; exists x => //.
    by rewrite xl x0 eqxx.
  apply/ltW; rewrite -sgr_gt0 -big_seq prodrN1.
    by rewrite -signr_odd (negbTE ol) expr0.
  move=> e el; rewrite lt_neqAle l0//=.
  by move/List.Forall_forall : H => /(_ e); apply => //; exact/In_in.
- case: c => //=.
  by rewrite oppr_le0 le_maxr lexx orbT.
Qed.

Definition is_dl2 b (x : R) := (if b then x == 0 else x < 0).

Lemma dl2_nary_inversion_andE1 (s : seq (expr (Bool_P))) :
  is_dl2 true ([[ ldl_and s ]]_dl2') ->
  (forall i, (i < size s)%N -> is_dl2 true ([[ nth (ldl_bool _ false) s i ]]_dl2')).
Proof.
rewrite/is_dl2.
elim: s => //= h t ih H [_|]/=.
  move: H; rewrite /sumR big_cons.
  rewrite naddr_eq0//.
  - by move=> /andP[->].
  - exact: dl2_translation_le0.
  - rewrite big_seq_cond; apply: sumr_le0 => /= x.
    by rewrite andbT => /mapP[/= e et] ->; exact: dl2_translation_le0.
move=> n; rewrite ltnS => nt /=; apply: ih => //.
move: H; rewrite /sumR big_cons.
rewrite naddr_eq0.
- by move=> /andP[_ ->].
- exact: dl2_translation_le0.
- rewrite big_seq_cond; apply: sumr_le0 => /= x.
  by rewrite andbT => /mapP[/= e et] ->; exact: dl2_translation_le0.
Qed.

Lemma naddr_lt0 (x y : R) :
  (x <= 0) -> (y <= 0) -> (x + y < 0) -> ((x < 0) || (y < 0)).
Proof.
move=> x0 y0; rewrite !ltNge -negb_and; apply: contra.
by move=> /andP[x0' y0']; rewrite addr_ge0.
Qed.

Lemma prodr_le0 (A : Type) (l : seq A) (f: A -> R) :
  (forall i, f i <= 0) ->
  (((-1) ^+ (length l).+1) * \big[*%R/1]_(j <- l) f j <= 0).
Proof.
move=> fle0.
elim: l => [|a l IH].
  by rewrite /= big_nil mulr1 expr1 lerN10.
rewrite /= big_cons exprS (mulrC (f a)) -mulrA mulN1r.
by rewrite -!mulrN mulrA mulr_le0_ge0// oppr_ge0.
Qed.

Lemma dl2_nary_inversion_andE0 (s : seq (expr (Bool_P))) :
  is_dl2 false ([[ ldl_and s ]]_dl2') ->
  (exists i, (is_dl2 false ([[ nth (ldl_bool _ false) s i ]]_dl2')) && (i < size s)%nat).
Proof.
rewrite/is_dl2.
elim: s => [|h t ih] //=; first by rewrite /sumR big_nil ltxx.
rewrite /sumR big_cons => /naddr_lt0 => /(_ (dl2_translation_le0 _)).
have : (\sum_(j <- [seq [[i]]_dl2' | i <- t]) j <= 0).
  rewrite big_seq_cond; apply: sumr_le0 => /= z.
  by rewrite andbT => /mapP[/= e et ->]; exact: dl2_translation_le0.
move=> /[swap] /[apply] /orP[H|/ih[j /andP[j0 jt]]].
  by exists 0%N; rewrite /= H.
by exists j.+1; rewrite /= j0.
Qed.

Lemma dl2_nary_inversion_orE1 (s : seq (expr (Bool_P))) :
  is_dl2 true ([[ ldl_or s ]]_dl2') ->
  exists i, ([[ nth (ldl_bool _ false) s i ]]_dl2' == 0) && (i < size s)%nat.
Proof.
elim: s => [|h t ih] /=.
  rewrite /prodR big_nil mulr1 expr1.
  by rewrite lt_eqF//.
rewrite mulf_eq0 signr_eq0/=.
rewrite /prodR big_cons mulf_eq0 => /orP[H|/eqP H].
  by exists 0%N; rewrite /= H.
have /ih[j /andP[Hj jt]] : [[ldl_or t]]_dl2' == 0 by rewrite /= /prodR H mulr0.
by exists j.+1; rewrite /= Hj.
Qed.

Lemma dl2_nary_inversion_orE0 (Es : seq (expr (Bool_P)) ) :
    is_dl2 false ([[ ldl_or Es ]]_dl2')  -> (forall i, (i < size Es)%nat -> is_dl2 false ([[ nth (ldl_bool _ false) Es i ]]_dl2')).
Proof.
elim: Es => //= a l IH.
rewrite /prodR big_cons mulrCA mulr_lt0 => /andP[aneq0]/andP[]/[swap] _.
rewrite exprS -mulrA mulN1r oppr_eq0 => lneq0.
have ale0 := dl2_translation_le0 a.
have alt0 : ([[a]]_dl2' < 0) by rewrite lt_neqAle aneq0 ale0.
elim => [_//=|i _].
rewrite ltnS => isize.
apply IH => //.
rewrite lt_neqAle lneq0/= /prodR big_map.
apply: prodr_le0 => j.
exact: dl2_translation_le0.
Qed.

Lemma dl2_translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  [[ e ]]_dl2' = [[ e ]]b.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ e2 erefl JMeq_refl).
Qed.

Lemma dl2_translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_dl2' = [[ e ]]b.
Proof.
dependent induction e => //=.
Qed.

Lemma dl2_translations_Real_coincide (e : expr Real_T):
  [[ e ]]_dl2' = [[ e ]]b.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite dl2_translations_Vector_coincide dl2_translations_Index_coincide.
Qed.

Lemma maxr0_le :
  forall x : R , (- maxr x 0) = 0 -> x <= 0.
Proof.
move => r.
rewrite /maxr. case: ifP.
- by lra.
- by move => h; case; lra.
Qed.

Lemma dl2_soundness (e : expr Bool_P) b :
  is_dl2 b ([[ e ]]_dl2') -> [[ e ]]b = b.
Proof.
dependent induction e using expr_ind'.
- move: b b0 => [] [] //=; by rewrite ?lt_irreflexive ?lt_eqF ?ltrN10.
- rewrite List.Forall_forall in H.
  move: b => [].
  + move/dl2_nary_inversion_andE1.
    rewrite [bool_translation (ldl_and l)]/= big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    apply: H => //. rewrite ?h// -In_in mem_nth//.
    by rewrite h.
  + move/dl2_nary_inversion_andE0.
    rewrite [bool_translation (ldl_and l)]/= big_map big_all.
    elim=>// i /andP[/eqP i0 isize].
    apply/allPn; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    * by rewrite -In_in mem_nth.
    * rewrite /is_dl2/=. move: i0.
      by rewrite eqb_id.
- rewrite List.Forall_forall in H.
  move: b => [].
  + move/dl2_nary_inversion_orE1.
    rewrite [bool_translation (ldl_or l)]/= big_map big_has.
    elim=>// i /andP[/eqP i0 isize].
    apply/hasP; exists (nth (ldl_bool _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
    rewrite /is_dl2/=. by rewrite i0.
  + move/dl2_nary_inversion_orE0.
    rewrite [bool_translation (ldl_or l)]/= big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (ldl_bool _ false).
    apply/negPf; apply: H => //.
    * by rewrite ?h// -In_in mem_nth.
    * by rewrite h.
- case: c; rewrite //=; rewrite -!dl2_translations_Real_coincide;
  set t1 := _ e1; set t2 := _ e2; case: b => //.
  + by rewrite/is_dl2 => /eqP; move/maxr0_le; rewrite subr_le0.
  + rewrite/is_dl2 oppr_lt0 /maxr; case: ifPn; first by rewrite lt_irreflexive.
    by rewrite subr_gt0 => _; move/lt_geF.
  + by rewrite/is_dl2=>/eqP; case=>/eqP; rewrite oppr_eq0 normr_eq0 subr_eq0.
  + rewrite/is_dl2; rewrite oppr_lt0 normr_gt0.
    by rewrite subr_eq0; move/eqP => h; apply/eqP.
Qed.

End dl2_lemmas.
