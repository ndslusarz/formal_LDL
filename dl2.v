From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra ldl.

(**md**************************************************************************)
(* # Properties of DL2                                                        *)
(*                                                                            *)
(* ## Structural properties                                                   *)
(* - dl2_mandC_nary == n-ary commutativity of conjunction                     *)
(* - dl2_mandC == commutativity of conjunction                                *)
(* - dl2_mandA == associativity of conjunction                                *)
(* - dl2_morC_nary == n-ary commutativity of disjunction                      *)
(* - dl2_morC == commutativity of disjunction                                 *)
(* - dl2_morA == associativity of disjunction                                 *)
(* - dl2_mand_unit == existance of unit element for mand                      *)
(* - dl2_residuation == residuation property                                  *)
(*                                                                            *)
(* ## Adequacy                                                                *)
(* - dl2_translation_le0 == invariant for the translation: all values are in  *)
(*                          the range $(-\infty, 0]$                          *)
(* - dl2_nary_inversion_andE1 == inversion lemma for conjunction/true         *)
(* - dl2_nary_inversion_andE0 == inversion lemma for conjuntion/false         *)
(* - dl2_translations_Vector_coincide == shows that the Boolean translation   *)
(*   and the DL2 translation coincide on expressions of type Vector_T         *)
(* - dl2_translations_Index_coincide == shows that the Boolean translation    *)
(*   and the DL2 translation coincide on expressions of type Index_T          *)
(* - dl2_translations_Real_coincide == shows that the Boolean translation and *)
(*   the DL2 translation coincide on expressions of type Real_T               *)
(*                                                                            *)
(* ## Shadow-lifting                                                          *)
(* - dl2_and v == $\sum_{i < n} v_i$                                          *)
(* - shadowlifting_dl2_andE == shadow-lifting for DL2                         *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

HB.instance Definition _ (R : realType) x y z v :=
  @gen_eqMixin (@expr R (Bool_T x y z v)).

Section dl2_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_dl2" := (@dl2_translation R _ e).

Lemma dl2_mandC_nary f1 f2 (s1 s2 : seq (expr (Bool_T_def f1 m_def f2))) :
  perm_eq s1 s2 -> [[ldl_mand s1]]_dl2 = [[ldl_mand s2]]_dl2.
Proof. by move=> pi; rewrite /= !big_map (perm_big _ pi). Qed.

Lemma dl2_mandC f1 f2 (e1 e2 : expr (Bool_T_def f1 m_def f2)) :
  [[ e1 `** e2 ]]_dl2 = [[ e2 `** e1 ]]_dl2.
Proof. by rewrite /= !big_cons !big_nil /= addr0 addr0 addrC. Qed.

Lemma dl2_mandA f1 f2 (e1 e2 e3 : expr (Bool_T_def f1 m_def f2)) :
  [[ e1 `** (e2 `** e3) ]]_dl2 = [[ (e1 `** e2) `** e3 ]]_dl2.
Proof. by rewrite /= !big_cons !big_nil !addr0 addrA. Qed.

Lemma dl2_morC_nary f1 f2 (s1 s2 : seq (expr (Bool_T_def f1 m_def f2))) :
  perm_eq s1 s2 -> [[ldl_mor s1]]_dl2 = [[ldl_mor s2]]_dl2.
Proof. by move=> pi; rewrite /= !big_map (perm_big _ pi). Qed.

Lemma dl2_morC f1 f2 (e1 e2 : expr (Bool_T_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_dl2 = [[ e2 `++ e1 ]]_dl2.
Proof. by rewrite /= !big_cons !big_nil /= addr0 addr0 addrC. Qed.

Lemma dl2_translation_le0 f e :
  [[ e ]]_dl2 <= 0 :> type_translation (Bool_T_undef f m_def l_undef).
Proof.
dependent induction e using expr_ind' => /=.
- by case: b.
- rewrite /maxr; case: ifP; move => h; lra.
- rewrite big_map big_seq sumr_le0// => t tl.
  move/List.Forall_forall : H => /(_ t); apply => //.
  exact/In_in.
- rewrite big_map big_seq sumr_le0// => t tl.
  move/List.Forall_forall : H => /(_ t); apply => //.
  exact/In_in.
- case: c => //=.
  by rewrite oppr_le0 le_max lexx orbT.
Qed.

Theorem dl2_mand_unit f1 f2 (e :  (expr (Bool_T_def f1 m_def f2))) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_dl2 = [[ e ]]_dl2.
Proof. by rewrite /= !big_cons big_nil !addr0. Qed.

Theorem dl2_residuation (e1 e2 e3 :  (expr (Bool_T_undef impl_def m_def l_undef))) :
  [[ e1 `** e2 ]]_dl2 <= [[ e3 ]]_dl2 <->
    [[ e2 ]]_dl2 <= [[ e1 `=> e3 ]]_dl2.
Proof.
split; move => /= H.
- rewrite !big_cons big_nil addr0 in H.
  rewrite/maxr; case: ifP; move => /eqP h; try lra.
  rewrite oppr0.
  exact (dl2_translation_le0 _ e2).
- rewrite !big_cons big_nil addr0.
  by move: H; rewrite/maxr;  case: ifP => ? ?; lra.
Qed.

Definition is_dl2 b (x : R) := if b then x == 0 else x < 0.

Lemma dl2_nary_inversion_mandE1 f (s : seq (expr (Bool_T_undef f m_def l_undef))) :
  is_dl2 true ([[ ldl_mand s ]]_dl2) ->
  (forall i, (i < size s)%N -> is_dl2 true ([[ nth (ldl_bool _ _ _ _ false) s i ]]_dl2)).
Proof.
rewrite/is_dl2.
elim: s => //= h t ih H [_|]/=.
  move: H; rewrite big_cons.
  rewrite naddr_eq0//.
  - by move=> /andP[->].
  - exact: dl2_translation_le0.
  - rewrite big_seq_cond; apply: sumr_le0 => /= x.
    by rewrite andbT => /mapP[/= e et] ->; exact: dl2_translation_le0.
move=> n; rewrite ltnS => nt /=; apply: ih => //.
move: H; rewrite big_cons naddr_eq0.
- by move=> /andP[_ ->].
- exact: dl2_translation_le0.
- rewrite big_seq_cond; apply: sumr_le0 => /= x.
  by rewrite andbT => /mapP[/= e et] ->; exact: dl2_translation_le0.
Qed.

Lemma dl2_nary_inversion_mandE0 f (s : seq (expr (Bool_T_undef f m_def l_undef))) :
  is_dl2 false ([[ ldl_mand s ]]_dl2) ->
  (exists i, (is_dl2 false ([[ nth (ldl_bool _ _ _ _ false) s i ]]_dl2)) && (i < size s)%nat).
Proof.
rewrite/is_dl2.
elim: s => [|h t ih] //=; first by rewrite big_nil ltxx.
rewrite big_cons => /naddr_lt0 => /(_ (dl2_translation_le0 _ _)).
have : \sum_(j <- [seq [[i]]_dl2 | i <- t]) j <= 0.
  rewrite big_seq_cond; apply: sumr_le0 => /= z.
  by rewrite andbT => /mapP[/= e et ->]; exact: dl2_translation_le0.
move=> /[swap] /[apply] /orP[H|/ih[j /andP[j0 jt]]].
  by exists 0%N; rewrite /= H.
by exists j.+1; rewrite /= j0.
Qed.

Lemma dl2_inversion_implE1 (E1 E2 : expr (Bool_T_undef impl_def m_def l_undef)) :
  is_dl2 true ([[  E1 `=> E2 ]]_dl2) ->
     is_dl2 false ([[ E1 ]]_dl2) || is_dl2 true ([[ E2 ]]_dl2).
Proof.
rewrite//=/maxr; case: ifP => H1 H2; 
have H2' := dl2_translation_le0 _ E2;
have H1' := dl2_translation_le0 _ E1; try lra.
Qed.

Lemma dl2_translations_Vector_coincide: forall n (e : @expr R (Vector_T n)),
  [[ e ]]_dl2 = [[ e ]]_B.
Proof.
dependent induction e => //=.
dependent destruction e1.
by rewrite (IHe2 _ _ e2 erefl JMeq_refl).
Qed.

Lemma dl2_translations_Index_coincide: forall n (e : expr (Index_T n)),
  [[ e ]]_dl2 = [[ e ]]_B.
Proof.
dependent induction e => //=.
Qed.

Lemma dl2_translations_Real_coincide (e : expr Real_T):
  [[ e ]]_dl2 = [[ e ]]_B.
Proof.
dependent induction e => //=;
rewrite ?(IHe1 e1 erefl JMeq_refl) ?(IHe2 e2 erefl JMeq_refl) ?(IHe e erefl JMeq_refl) //=.
by rewrite dl2_translations_Vector_coincide dl2_translations_Index_coincide.
Qed.

End dl2_lemmas.

Section shadow_lifting_dl2_and.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Context {R : realType}.
Variable M : nat.
Hypothesis M0 : M != 0%N.

Definition dl2_and {R' : fieldType} {n} (v : 'rV[R']_n) :=
  (\sum_(i < n) v ``_ i)%R.

Import MatrixFormula.

Lemma dl2_andE {n} (v : 'rV[R]_n) :
  dl2_and v = \sum_(i <- seq_of_rV v) (dl2_translation \o ldl_real) i.
Proof.
rewrite !big_map /dl2_and -enumT big_enum.
by under [in RHS]eq_bigr do rewrite ffunE.
Qed.

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

Corollary shadow_lifting_dl2_and : shadow_lifting (@dl2_and R M.+1).
Proof. by move=> p p0 i; rewrite shadowlifting_dl2_andE. Qed.

End shadow_lifting_dl2_and.
