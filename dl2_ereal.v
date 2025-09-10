From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra perm.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal interval_inference.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral hoelder.
Require Import mathcomp_extra analysis_extra ldl dl2.

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

Local Open Scope ereal_scope.

Lemma adde_eq_pinfty {R : numDomainType} (x y : \bar R) :
  (x + y == +oo) = ((x == +oo) && (y != -oo)) || ((y == +oo) && (x != -oo)).
Proof. by move: x y => [?| |] [?| |]. Qed.

Local Close Scope ereal_scope.

Section dl2_lemmas.
Local Open Scope ldl_scope.
Local Open Scope ring_scope.
Context {R : realType}.
Variable p : R.

Local Notation "[[ e ]]_dl2e" := (@dl2_ereal_translation R _ e).

Lemma dl2_mandC_nary n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def impl_def m_def l_def))) :
  [[ldl_mand s]]_dl2e = [[ldl_mand (s \o pi)]]_dl2e.
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

Lemma dl2_morC_nary n (pi : {perm 'I_n}) (s : 'I_n -> (expr (boolT_def impl_def m_def l_def))) :
  [[ldl_mor s]]_dl2e = [[ldl_mor (s \o pi)]]_dl2e.
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
  [[ e `** (ldl_bool _ _ _ _ true) ]]_dl2e = [[ e ]]_dl2e.
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

Lemma dl2_nary_inversion_andE1 (s : seq (expr (boolT_undef impl_def m_def l_def))) :
  is_dl2 true ([[ ldl_mand s ]]_dl2e) ->
  (forall i, (i < size s)%N -> is_dl2 true ([[ nth (ldl_bool _ _ _ _ false) s i ]]_dl2e)).
Proof.
rewrite/is_dl2//=.
case: ifPn => //; case: ifPn => //.
elim: s => //= a l IH + + + i size.
rewrite !negb_or => /andP [hap lp] /andP [han ln].
rewrite big_cons nadde_eq0//=.
- move => /andP [ha hl].
  case: i size => [_|i ih].
  + by rewrite nth0//=.
  + rewrite -nth_behead//=. apply IH => //=.
- exact: dl2_ereal_translation_le0.
- rewrite big_seq_cond; apply: sume_le0 => /= x.
    by rewrite andbT => /mapP[/= e et] ->; exact: dl2_ereal_translation_le0.
Qed.

Lemma dl2_nary_inversion_andE0 (s : seq (expr (boolT_undef impl_def m_def l_def))) :
  is_dl2 false ([[ ldl_mand s ]]_dl2e) ->
  (exists i, (is_dl2 false ([[ nth (ldl_bool _ _ _ _ false) s i ]]_dl2e)) && (i < size s)%nat) \/
  (exists i, ([[ nth (ldl_bool _ _ _ _ false) s i ]]_dl2e == +oo%E) && (i < size s)%nat).
Proof.
rewrite/is_dl2//=.
case: ifPn => //=.
- move => hs _. left.
  have /hasP [y /mapP [x xin ->] /eqP hx] := hs.
  set i := index x s.
  exists i; apply/andP; split.
  + have -> : nth (ldl_bool neg_undef impl_def m_def l_def false) s i = x;
      first by rewrite /i nth_index.
    by rewrite hx.
  + by rewrite /i index_mem.
- case: ifPn => // h1 h.
  + right. have /hasP [y /mapP [x xin ->] /eqP hx] := h1.
  set i := index x s.
  exists i; apply/andP; split.
  + have -> : nth (ldl_bool neg_undef impl_def m_def l_def false) s i = x;
      first by rewrite /i nth_index.
    by rewrite hx.
  + by rewrite /i index_mem.
  + left.
    elim: s h1 h H => [ |h t ih] //=; first by rewrite big_nil ltxx.
    rewrite !negb_or => /andP [hap lp] /andP [han ln].
    rewrite big_cons => /nadde_lt0 => /(_ (dl2_ereal_translation_le0 _)).
    have : (\sum_(j <- [seq [[i]]_dl2e | i <- t]) j <= 0)%E.
      rewrite big_seq_cond; apply: sume_le0 => /= z.
      by rewrite andbT => /mapP[/= e et ->]; exact: dl2_ereal_translation_le0.
    move=> /[swap] /[apply] /orP[H|H];
           first by exists 0%N; rewrite /= H.
    have [i /andP [H1 H2]] := ih lp ln H.
    exists i.+1; apply/andP; split.
    * case: i H1 H2 => [H1 H2|i H1 H2]; by rewrite -nth_behead//=.
    * have Hi_le : (i.+1 <= size t)%N by [].
      exact: (leq_ltn_trans Hi_le (ltnSn _)).
Qed.

End dl2_lemmas.
