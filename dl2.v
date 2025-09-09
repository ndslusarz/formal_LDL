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
  @gen_eqMixin (@expr R (boolT x y z v)).

Section dl2_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_dl2" := (@dl2_translation R _ e).

From mathcomp Require Import perm.

Lemma dl2_mandC_nary f1 f2 n (s1 s2 : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  (exists pi : {perm 'I_n}, s1 = s2 \o pi) -> [[ldl_mand s1]]_dl2 = [[ldl_mand s2]]_dl2.
(* Proof. by move=> pi; rewrite /= !big_map (perm_big _ pi). Qed. *)
Admitted.

Lemma dl2_mandC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `** e2 ]]_dl2 = [[ e2 `** e1 ]]_dl2.
Proof. by rewrite /= !big_ord_recl !big_ord0 /= addr0 addr0 addrC. Qed.

Lemma dl2_mandA f1 f2 (e1 e2 e3 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `** (e2 `** e3) ]]_dl2 = [[ (e1 `** e2) `** e3 ]]_dl2.
Proof. by rewrite /= !big_ord_recl /= !big_ord_recl !big_ord0 !addr0 addrA. Qed.

Lemma dl2_morC_nary f1 f2 n (s1 s2 : 'I_n -> (expr (boolT_def f1 m_def f2))) :
  (exists pi : {perm 'I_n}, s1 = s2 \o pi) -> [[ldl_mor s1]]_dl2 = [[ldl_mor s2]]_dl2.
(* Proof. by move=> pi; rewrite /= !big_map (perm_big _ pi)/= (perm_size pi). Qed. *)
Admitted.

Lemma dl2_morC f1 f2 (e1 e2 : expr (boolT_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_dl2 = [[ e2 `++ e1 ]]_dl2.
Proof.
by rewrite /= !big_ord_recl !big_ord0 /= !mulr1 [X in _ * X]mulrC.
Qed.

Lemma dl2_translation_le0 e : [[ e ]]_dl2 <= 0 :> type_translation (boolT_dl2).
Proof.
dependent induction e using expr_ind' => /=.
- by case: b.
- move: l H; case: n => // n l H.
  rewrite bigmin_idl {1}/minr; case: ifPn => h; first exact/H.
  by rewrite (@le_trans _ _ ([[l ord0]]_dl2)) ?(H ord0)//; lra.
- move: l H; case: n => // n l H.
  rewrite big_seq bigmax_le ?H//.
  exact/(H ord0).
- by move=> /= i _; exact/H.
- by rewrite lerNl oppr0 /maxr; case: ifPn => //; rewrite leNgt.
- by apply/sumr_le0 => i _; exact/H.
- move: l H; elim: n => [l H|n ih l H]; first by rewrite big_ord0 mulr1 expr1.
  rewrite exprS big_ord_recl mulrCA -mulrA mulNr mul1r mulr_le0_ge0// ?(H ord0)// lerNr oppr0 ih=> //i e0 h1 h2.
  exact/(@H _ _ h1 h2).
- by case: c; rewrite //= oppr_le0 le_max lexx orbT.
Qed.

Theorem dl2_mand_unit f1 f2 (e : (expr (boolT_def f1 m_def f2))) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_dl2 = [[ e ]]_dl2.
Proof. by rewrite /= !big_ord_recl big_ord0 !addr0. Qed.

Theorem dl2_residuation (e1 e2 e3 : expr boolT_dl2) :
  [[ e1 `** e2 ]]_dl2 <= [[ e3 ]]_dl2 <->
    [[ e2 ]]_dl2 <= [[ e1 `=> e3 ]]_dl2.
Proof.
split; move => /= H.
- rewrite !big_ord_recl big_ord0 addr0 in H.
  rewrite/maxr; case: ifP; move => /eqP h; try lra.
  rewrite oppr0.
  exact (dl2_translation_le0 e2).
- rewrite !big_ord_recl big_ord0 addr0.
  by move: H; rewrite/maxr;  case: ifP => ? ?; lra.
Qed.

Lemma dl2_prelinearity (e1 e2 e3 : @expr R boolT_dl2) :
  [[(e1 `=> e2) `\/ (e2 `=> e1)]]_dl2 = [[ldl_bool  _ _ _ _ true]]_dl2.
Proof.
rewrite//= !big_ord_recl big_ord0 /maxr; repeat case: ifP; try lra.
Admitted.


Lemma dl2_andC  (e1 e2 : expr boolT_dl2) :
  [[ e1 `/\ e2 ]]_dl2 = [[ e2 `/\ e1 ]]_dl2.
Proof.
by rewrite /=!big_ord_recl !big_ord0 /minr; repeat case: ifP; lra.
Qed.

Lemma dl2_orC (e1 e2 : expr boolT_dl2) :
  [[ e1 `\/ e2 ]]_dl2 = [[ e2 `\/ e1 ]]_dl2.
Proof.
by rewrite /=!big_ord_recl !big_ord0 /maxr; repeat case: ifP; lra.
Qed.

Lemma dl2_orA (e1 e2 e3 : expr boolT_dl2) :
  [[ (e1 `\/ (e2 `\/ e3)) ]]_dl2 = [[ ((e1 `\/ e2) `\/ e3) ]]_dl2.
Proof.
rewrite /= !big_ord_recl !big_ord0 /= !big_ord_recl !big_ord0 /maxr !tnthS !tnth0.
by repeat case: ifPn => //; lra.
Qed.

Theorem dl2_andA (e1 e2 e3 : expr boolT_dl2) : (0 < p) ->
  [[ (e1 `/\ e2) `/\ e3]]_dl2 = [[ e1 `/\ (e2 `/\ e3) ]]_dl2.
Proof.
rewrite /= !big_ord_recl !big_ord0 /= !big_ord_recl !big_ord0.
have := dl2_translation_le0 e1.
have := dl2_translation_le0 e2.
have := dl2_translation_le0 e3.
set t1 := _ e1.
set t2 := _ e2.
set t3 := _ e3.
move => h1 h2 h3 p0.
rewrite /minr.
by repeat case: ifPn => //; lra.
Qed.

Lemma dl2_and_abs (e1 e2 : expr boolT_dl2) :
  [[ e1 `/\ (e1 `\/ e2)]]_dl2 = [[ e1 ]]_dl2.
Proof.
rewrite/= !big_ord_recl !big_ord0 /= !big_ord_recl big_ord0.
have := dl2_translation_le0 e1.
have := dl2_translation_le0 e2.
rewrite/minr/maxr; repeat case: ifP; intros; try lra.
Qed.

Lemma dl2_or_abs (e1 e2 : expr boolT_dl2) :
  [[ e1 `\/ (e1 `/\ e2)]]_dl2 = [[ e1 ]]_dl2.
Proof.
rewrite//= !big_ord_recl !big_ord0 /= !big_ord_recl big_ord0.
have h1 := dl2_translation_le0 e1.
have h2 := dl2_translation_le0 e2.
have minr_le0 : forall (a : R), a <= 0 -> (minr a 0) = a.
  intros; rewrite/minr; case: ifP; lra.
rewrite/minr/maxr; repeat case: ifPn; intros; try lra.
Qed.

Lemma dl2_and_distr (e1 e2 e3 : expr boolT_dl2) :
  [[ e1 `/\ (e2 `\/ e3)]]_dl2 = [[ (e1 `/\ e2) `\/ (e1 `/\ e3)]]_dl2.
Proof.
(*have h1 := dl2_translation_le0 e1.
have h2 := dl2_translation_le0 e2.
have h3 := dl2_translation_le0 e3.
split; rewrite//=; rewrite !big_ord_recl big_ord0 ?addr0 /maxr; repeat case: ifP; intros; lra.
=======
rewrite//= /minR /maxR !big_cons !big_nil.
rewrite{1}/minr/maxr; repeat case: ifP; try lra; repeat rewrite{1}/minr; repeat case: ifP; try lra.*)
Admitted.

Definition is_dl2 b (x : R) := if b then x == 0 else x < 0.

Lemma nsumr_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> R) :
    (forall i, P i -> 0 >= F i) ->
  (\sum_(i <- r | P i) (F i) == 0) = (all (fun i => (P i) ==> (F i == 0)) r).
Proof.
elim: r=> [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
by case: ifP=> pa /=; rewrite ?naddr_eq0 ?ihr ?hr // sumr_le0.
Qed.

(* :TODO: Cyril : See which form to keep *)
Lemma psumr_eq0P (I : finType) (P : pred I) (F : I -> R) :
     (forall i, P i -> 0 >= F i) -> \sum_(i | P i) F i = 0 ->
  (forall i, P i -> F i = 0).
Proof.
move=> F_ge0 /eqP; rewrite nsumr_eq0 // -big_all big_andE => /forallP hF i Pi.
by move: (hF i); rewrite implyTb Pi /= => /eqP.
Qed.

Lemma dl2_nary_inversion_mandE1 n (s : 'I_n -> (expr (boolT_dl2))) :
  is_dl2 true ([[ ldl_mand s ]]_dl2) -> (forall i, is_dl2 true ([[ s i ]]_dl2)).
Proof.
move: s; case: n => [s _|n s/=]; first by case.
rewrite nsumr_eq0//=; last by move=> i _; exact/dl2_translation_le0.
by move/allP => h i; exact/h/mem_index_enum.
Qed.

Lemma dl2_nary_inversion_mandE0 n (s : 'I_n -> (expr boolT_dl2)) :
  is_dl2 false ([[ ldl_mand s ]]_dl2) ->
  (exists i, is_dl2 false ([[ s i ]]_dl2)).
Proof.
move: s => /=; elim: n => [s|n ih s]; first by rewrite big_ord0 ltxx.
rewrite big_ord_recl/= => /naddr_lt0.
move/(_ (dl2_translation_le0 _) (sumr_le0 _ (fun i _ => dl2_translation_le0 _))) => /orP[h|].
  by exists ord0.
by move/ih => [i ?]; exists (lift ord0 i).
Qed.

Lemma dl2_inversion_implE1 (E1 E2 : expr boolT_dl2) :
  is_dl2 true ([[  E1 `=> E2 ]]_dl2) ->
     is_dl2 false ([[ E1 ]]_dl2) || is_dl2 true ([[ E2 ]]_dl2).
Proof.
rewrite//=/maxr; case: ifP => H1 H2;
have H2' := dl2_translation_le0 E2;
have H1' := dl2_translation_le0 E1; try lra.
Qed.

Lemma dl2_translations_coincide t (e : @expr R t) n m j :
  (t = realT \/ t = vectorT n \/ t = indexT n \/ t = funT n m \/ t = fun2T n m j) ->
  [[ e ]]_dl2 ~= [[ e ]]_B.
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

Lemma dl2_translations_Fun_coincide n m (e : expr (funT n m)) :
  [[ e ]]_dl2 = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(dl2_translations_coincide _ _ n m 0); right;right;right;left.
Qed.

Lemma dl2_translations_Vector_coincide n (e : @expr R (vectorT n)) :
  [[ e ]]_dl2 = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(dl2_translations_coincide _ _ n 0 0); right;left.
Qed.

Lemma dl2_translations_Index_coincide n (e : expr (indexT n)) :
  [[ e ]]_dl2 = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(dl2_translations_coincide _ _ n 0 0); right;right;left.
Qed.

Lemma dl2_translations_Real_coincide (e : expr realT):
  [[ e ]]_dl2 = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(dl2_translations_coincide _ _ 0 0 0); left.
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
