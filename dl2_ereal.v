From HB Require Import structures.
Require Import Stdlib.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra perm.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra dl dl2.

(**md**************************************************************************)
(* # Properties of DL2 on extended reals                                      *)
(*                                                                            *)
(* ## Structural properties                                                   *)
(* - dl2_mandC_nary == n-ary commutativity of conjunction                     *)
(* - dl2_mandC == commutativity of conjunction                                *)
(* - dl2_mandA == associativity of conjunction                                *)
(* - dl2_morC_nary == n-ary commutativity of disjunction                      *)
(* - dl2_morC == commutativity of disjunction                                 *)
(* - dl2_morA == associativity of Ydisjunction                                *)
(* - dl2_mand_unit == unit element of conjunction                             *)
(* - dl2_residuation == residuation property                                  *)
(*                                                                            *)
(* ## Adequacy                                                                *)
(* - dl2_ereal_translation_le0 == invariant for the translation: all values   *)
(*                                are in the range $[-\infty, 0]$             *)
(* - dl2_nary_inversion_andE1 == inversion lemma for conjunction/true         *)
(* - dl2_nary_inversion_andE0 == inversion lemma for conjuntion/false         *)
(* - dl2_translations_Vector_coincide == shows that the Boolean translation   *)
(*   and the DL2 translation coincide on expressions of type Vector_T         *)
(* - dl2_translations_Index_coincide == shows that the Boolean translation    *)
(*   and the DL2 translation coincide on expressions of type Index_T          *)
(* - dl2_translations_Real_coincide == shows that the Boolean translation and *)
(*   the DL2 translation coincide on expressions of type Real_T               *)
(******************************************************************************)

Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Section dl2_lemmas.
Local Open Scope dl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_dl2e" := (@dl2_ereal_translation R _ e).

Lemma dl2_mandC_nary n (pi : {perm 'I_n})
    (s : 'I_n -> expr (boolT_def impl_def m_def l_def)) :
  [[dl_mand s]]_dl2e = [[dl_mand (s \o pi)]]_dl2e.
Proof.
by rewrite /= (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma dl2_mandC (e1 e2 : expr (boolT_def impl_def m_def l_def)) :
 [[ e1 `** e2 ]]_dl2e = [[ e2 `** e1 ]]_dl2e.
Proof.
by rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0 !adde0 addeC.
Qed.

Lemma dl2_mandA (e1 e2 e3 : expr (boolT_undef impl_def m_def l_def)) :
  [[ e1 `** (e2 `** e3) ]]_dl2e = [[ (e1 `** e2) `** e3 ]]_dl2e.
Proof.
by rewrite /= !big_ord_recl !big_ord0 /= !big_ord_recl !big_ord0 !tnthS !tnth0 !adde0 addeA.
Qed.

Lemma dl2_morC_nary n (pi : {perm 'I_n}) (s : 'I_n -> expr (boolT_def impl_def m_def l_def)) :
  [[dl_mor s]]_dl2e = [[dl_mor (s \o pi)]]_dl2e.
Proof.
by rewrite /= (perm_big (map pi (index_enum 'I_n))) ?big_map//= perm_eq_fun.
Qed.

Lemma dl2_morC (e1 e2 : expr (boolT_undef impl_def m_def l_undef)) :
 [[ e1 `++ e2 ]]_dl2e = [[ e2 `++ e1 ]]_dl2e.
Proof.
by rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0 !mule1 [X in (_ * X)%E](muleC).
Qed.

Lemma dl2_ereal_translation_le0 e :
  ([[ e ]]_dl2e <= 0 :> ereal_type_translation (boolT_undef impl_def m_def l_def))%E.
Proof.
dependent induction e => /=.
- by case: b.
- by rewrite bigmin_idl /mine; case: ifPn; rewrite -?leNgt.
- by apply/bigmax_le => // i _; exact/H.
- by rewrite /maxe; case: ifPn => h //=; rewrite leeNl oppe0 leNgt h.
- by apply/sume_le0 => i _; exact/H.
- elim: n e H => [e H|n ih e H]; first by rewrite expr1 big_ord0 mule1.
  rewrite exprS EFinM big_ord_recl muleCA !muleA -muleA mule_ge0_le0//.
    by rewrite mule_le0 ?(H ord0).
  by apply/ih => i e0 ? ?; exact/(H (lift ord0 i)).
- by case: c; rewrite lee_fin oppr_le0// /maxr; case: ifPn => //; rewrite -leNgt.
Qed.

Lemma dl2_morA (e1 e2 e3 : expr (boolT_undef impl_def m_def l_def)) :
  [[ e1 `++ (e2 `++ e3) ]]_dl2e = [[ (e1 `++ e2) `++ e3 ]]_dl2e.
Proof.
rewrite /= !big_ord_recl !big_ord0 /= !big_ord_recl !big_ord0 !tnthS !tnth0.
by rewrite !mule1 -muleA [X in (_ * X)%E]muleCA !muleA.
Qed.


Theorem dl2_mand_unit (e : expr (boolT_undef impl_def m_def l_def)) :
  [[ e `** dl_bool _ _ _ _ true ]]_dl2e = [[ e ]]_dl2e.
Proof.
by rewrite /= !big_ord_recl big_ord0 tnthS tnth0 !adde0.
Qed.


Theorem dl2_residuation (e1 e2 e3 : expr (boolT_undef impl_def m_def l_def)) :
  ([[ e1 `** e2 ]]_dl2e <= [[ e3 ]]_dl2e <->
   [[ e2 ]]_dl2e <= [[ e1 `=> e3 ]]_dl2e)%E.
Proof.
rewrite /= !big_ord_recl !big_ord0 !tnthS !tnth0 adde0 /maxe.
case: ifPn => [/ltW|_].
  rewrite oppe0 dl2_ereal_translation_le0.
  rewrite sube_le0=> /(leeD (dl2_ereal_translation_le0 e2)).
  by rewrite add0e addeC.
case: ([[e1]]_dl2e) => [x||]; case: ([[e2]]_dl2e) => [y||]; case: ([[e3]]_dl2e) => [z||] //=.
all: try rewrite ?leey ?addeNy ?addNye ?leNye// -EFinD !lee_fin; lra.
Qed.

Lemma dl2_ereal_translations_coincide t (e : @expr R t) n m j :
  (t = realT \/ t = vectorT n \/ t = indexT n \/ t = funT n m \/ t = fun2T n m j) ->
  [[ e ]]_dl2e ~= [[ e ]]_B.
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

Lemma dl2_ereal_translations_Fun_coincide n m (e : expr (funT n m)) :
  [[ e ]]_dl2e = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(dl2_ereal_translations_coincide _ _ n m 0); right;right;right;left.
Qed.

Lemma dl2_ereal_translations_Vector_coincide n (e : @expr R (vectorT n)) :
  [[ e ]]_dl2e = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(dl2_ereal_translations_coincide _ _ n 0 0); right;left.
Qed.

Lemma dl2_ereal_translations_Index_coincide n (e : expr (indexT n)) :
  [[ e ]]_dl2e = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(dl2_ereal_translations_coincide _ _ n 0 0); right;right;left.
Qed.

Lemma dl2_ereal_translations_Real_coincide (e : expr realT):
  [[ e ]]_dl2e = [[ e ]]_B.
Proof.
by apply/JMeq_eq/(dl2_ereal_translations_coincide _ _ 0 0 0); left.
Qed.

Definition is_dl2 b (x : \bar R) := (if b then x == 0 else x < 0)%E.

Lemma nsume_eq0 (I : eqType) (r : seq I) (P : pred I) (F : I -> \bar R) :
    (forall i, P i -> 0 >= F i)%E ->
  (\sum_(i <- r | P i) (F i) == 0)%E = (all (fun i => (P i) ==> (F i == 0)) r)%E.
Proof.
elim: r=> [|a r ihr hr] /=; rewrite (big_nil, big_cons); first by rewrite eqxx.
by case: ifP=> pa /=; rewrite ?nadde_eq0 ?ihr ?hr // sume_le0.
Qed.

Lemma dl2_nary_inversion_andE1 n (s : 'I_n -> expr (boolT_undef impl_def m_def l_def)) :
  is_dl2 true ([[ dl_mand s ]]_dl2e) -> (forall i, is_dl2 true ([[ s i ]]_dl2e)).
Proof.
rewrite/is_dl2/= nsume_eq0/=; last by move=> i _; exact/dl2_ereal_translation_le0.
by move=> /allP/= h i; rewrite h ?mem_index_enum.
Qed.

Lemma nadde_lt0 (x y : \bar R) : (x + y < 0 -> (x < 0) || (y < 0))%E.
Proof.
move: x y => [x| |] [y| |]//; rewrite ?lee_fin ?lte_fin.
- rewrite !ltNge -negb_and; apply: contra.
  by move=> /andP[x0' y0']; rewrite addr_ge0.
- by move=> _; rewrite ltNyr orbT.
- by move=> _; rewrite ltNyr.
- by move=> _; rewrite ltNy0.
- by rewrite ltNy0.
Qed.

Lemma fsume_lt0 (I : choiceType) (s : seq I) (F : I -> \bar R) :
  (\sum_(i <- s) F i < 0 -> exists2 i, i \in s & F i < 0)%E.
Proof.
elim: s; first by rewrite big_nil ltxx.
move=> a l ih. rewrite big_cons => /nadde_lt0 /orP [fa0 | /ih[i il fi0]].
  by exists a; rewrite ?fa0 ?mem_head.
by exists i; rewrite ?fi0// mem_behead.
Qed.

Lemma dl2_nary_inversion_andE0 n (s : 'I_n -> expr (boolT_undef impl_def m_def l_def)) :
  is_dl2 false ([[ dl_mand s ]]_dl2e) -> (exists i, (is_dl2 false ([[ s i ]]_dl2e))).
Proof.
rewrite /is_dl2/=.
move=> /fsume_lt0 [/=i _ si0].
by exists i.
Qed.

End dl2_lemmas.
