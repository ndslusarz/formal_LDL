From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
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

Lemma dl2_mandC_nary (s1 s2 : seq (expr (boolT_def impl_def m_def l_def))) :
  perm_eq s1 s2 -> [[ldl_mand s1]]_dl2e = [[ldl_mand s2]]_dl2e.
Proof.
move=> s12/=.
move/(perm_map (fun e => [[e]]_dl2e)) : (s12) => /[dup].
move/(perm_has (pred1 -oo%E)) ->.
move/(perm_has (pred1 +oo%E)) ->.
case: ifPn => //=; case: ifPn => //= _ _.
rewrite !big_map.
exact: perm_big.
Qed.

Lemma dl2_mandC (e1 e2 : expr (boolT_def impl_def m_def l_def)) :
 [[ e1 `** e2 ]]_dl2e = [[ e2 `** e1 ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons !big_nil !adde0.
rewrite !(orbC ([[e2]]_dl2e == _)).
by rewrite addeC.
Qed.

Lemma dl2_mandA (e1 e2 e3 : expr (boolT_undef impl_def m_def l_def)) :
  [[ e1 `** (e2 `** e3) ]]_dl2e = [[ (e1 `** e2) `** e3 ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons !big_nil !adde0.
have [H1//=|/negbTE H1/=] := eqVneq ([[e1]]_dl2e) -oo%E.
have [H2//=|/negbTE H2/=] := eqVneq ([[e2]]_dl2e) -oo%E.
have [H3/=|/negbTE H3/=] := eqVneq ([[e3]]_dl2e) -oo%E.
  by rewrite orbT.
have [K1//=|/negbTE K1/=] := eqVneq ([[e1]]_dl2e) +oo%E.
  have [K2//=|/negbTE K2/=] := eqVneq ([[e2]]_dl2e) +oo%E.
  have [K3//=|/negbTE K3/=] := eqVneq ([[e3]]_dl2e) +oo%E.
  by case: ifPn.
have [K2//=|/negbTE K2/=] := eqVneq ([[e2]]_dl2e) +oo%E.
have [K3//=|/negbTE K3/=] := eqVneq ([[e3]]_dl2e) +oo%E.
  rewrite !orbF !orbT.
  by case: ifPn.
rewrite !adde_eq_ninfty !orbF H1 H2 H3/=.
by rewrite !adde_eq_pinfty H1 H2 H3 K1 K2 K3/= addeA.
Qed.

Lemma dl2_morC_nary (s1 s2 : seq (expr (boolT_def impl_def m_def l_def))) :
  perm_eq s1 s2 -> [[ldl_mor s1]]_dl2e = [[ldl_mor s2]]_dl2e.
Proof.
move=> s12/=.
move/(perm_map (fun e => [[e]]_dl2e)) : (s12) => /[dup].
move/(perm_has (pred1 -oo%E)) ->.
move/(perm_has (pred1 +oo%E)) ->.
case: ifPn => //=; case: ifPn => //= _ _.
by rewrite !big_map (perm_size s12) (perm_big _ s12)//=.
Qed.

Lemma dl2_morC (e1 e2 : expr (boolT_undef impl_def m_def l_undef)) :
 [[ e1 `++ e2 ]]_dl2e = [[ e2 `++ e1 ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons !big_nil !mule1.
rewrite !(orbC ([[e2]]_dl2e == _)).
by rewrite (muleC ([[e1]]_dl2e) _).
Qed.

Lemma dl2_ereal_translation_le0 e :
  ([[ e ]]_dl2e <= 0 :> ereal_type_translation (boolT_undef impl_def m_def l_def))%E.
Proof.
dependent induction e using expr_ind' => /=.
- by case: b.
- case: l H; first by rewrite big_nil.
  move => a l.
  rewrite /=; move=> /List.Forall_forall H.
  rewrite !big_seq bigmin_idl.
  + rewrite {1}/mine; case: ifPn =>  h; first by rewrite//=.
    rewrite ltNge Bool.negb_involutive in h.
    by rewrite h.
- case: l H; first by rewrite big_nil.
  move => a l.
  rewrite /=; move=> /List.Forall_forall H.
  rewrite big_seq.
  rewrite bigmax_le//=.
  + rewrite ?ler01// => i il0.
    rewrite in_cons in il0. move/orP: il0.
    move => [/eqP i0 | i0].
    * subst. by apply: H => //; rewrite -In_in mem_head//.
    * have /mapP [x Hx ->] := i0.
    by apply: H => //; rewrite -In_in in_cons Hx orbT.
- rewrite /maxe; case: ifPn => h //=.
  by rewrite leeNl oppe0 leNgt h.
- case: ifPn => //.
  case: ifPn => //.
  rewrite big_map big_seq sume_le0// => t tl.
  move/List.Forall_forall : H => /(_ t); apply => //.
  exact/In_in.
- case: ifPn => //.
  case: ifPn => // hi1 hi2.
  rewrite  big_map big_seq; have [ol|ol] := boolP (odd (length l)).
    rewrite exprS -signr_odd ol expr1 mulrN1 !EFinN oppeK mul1e.
    have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2e != 0)%E; last first.
      move/existsNP : l0 => [/= x /not_implyP[xl /negP/negPn/eqP x0]].
      rewrite le_eqVlt; apply/orP; left.
      rewrite prode_seq_eq0; apply/hasP; exists x => //.
      by rewrite xl x0 eqxx.
    apply/ltW/sgeN1_lt0; rewrite -big_seq prodeN1.
      by rewrite -signr_odd ol expr1.
    move=> e el; rewrite lt_neqAle l0//=.
    by move/List.Forall_forall : H => /(_ e); apply => //; exact/In_in.
  rewrite exprS -signr_odd (negbTE ol) expr0 mulN1r.
  rewrite EFinN mulN1e oppe_le0.
  have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2e != 0)%E; last first.
    move/existsNP : l0 => [/= x /not_implyP[xl /negP/negPn/eqP x0]].
    rewrite le_eqVlt; apply/orP; left.
    rewrite eq_sym prode_seq_eq0; apply/hasP; exists x => //.
    by rewrite xl x0 eqxx.
  apply/ltW/sge1_gt0; rewrite -big_seq prodeN1.
    by rewrite -signr_odd (negbTE ol) expr0.
  move=> e el; rewrite lt_neqAle l0//=.
  by move/List.Forall_forall : H => /(_ e); apply => //; exact/In_in.
- case: c => //=.
  by rewrite lee_fin oppr_le0 le_max lexx orbT.
Qed.

Lemma dl2_morA (e1 e2 e3 : expr (boolT_undef impl_def m_def l_def)) :
  [[ e1 `++ (e2 `++ e3) ]]_dl2e = [[ (e1 `++ e2) `++ e3 ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons !big_nil !mule1.
have [H1//=|/negbTE H1/=] := eqVneq ([[e1]]_dl2e) -oo%E.
have [H2//=|/negbTE H2/=] := eqVneq ([[e2]]_dl2e) -oo%E.
have [H3/=|/negbTE H3/=] := eqVneq ([[e3]]_dl2e) -oo%E.
  by rewrite orbT.
have [K1//=|/negbTE K1/=] := eqVneq ([[e1]]_dl2e) +oo%E.
  have [K2//=|/negbTE K2/=] := eqVneq ([[e2]]_dl2e) +oo%E.
  have [K3//=|/negbTE K3/=] := eqVneq ([[e3]]_dl2e) +oo%E.
  by case: ifPn.
have [K2//=|/negbTE K2/=] := eqVneq ([[e2]]_dl2e) +oo%E.
have [K3//=|/negbTE K3/=] := eqVneq ([[e3]]_dl2e) +oo%E.
  rewrite !orbF !orbT.
  by case: ifPn.
have T1 := dl2_ereal_translation_le0 e1.
have T2 := dl2_ereal_translation_le0 e2.
have T3 := dl2_ereal_translation_le0 e3.
rewrite !mule_eq_ninfty !orbF H1 H2 H3 K1 K2 K3 !andbF.
rewrite !mule_eq_pinfty H1 H2 H3 K1 K2 K3/=//= !andbF.
rewrite !mule_eq_ninfty !orbF H1 H2 H3 K1 K2 K3 !andbF/=.
rewrite !muleA.
by rewrite (muleC (((-1) ^+ 3)%:E * [[e1]]_dl2e) _) muleA//=.
Qed.

Theorem dl2_mand_unit (e : expr (boolT_undef impl_def m_def l_def)) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_dl2e = [[ e ]]_dl2e.
Proof.
rewrite /= !orbF !big_cons big_nil !adde0.
case: ifPn => [/eqP ->//|e2oo].
rewrite ifF//.
apply/negbTE.
by rewrite -leye_eq -ltNge (le_lt_trans (dl2_ereal_translation_le0 e)).
Qed.


Theorem dl2_residuation (e1 e2 e3 : expr (boolT_undef impl_def m_def l_def)) :
  ([[ e1 `** e2 ]]_dl2e <= [[ e3 ]]_dl2e <->
   [[ e2 ]]_dl2e <= [[ e1 `=> e3 ]]_dl2e)%E.
Proof.
rewrite /= orbF.
have [H1//=|/negbTE H1/=] := eqVneq ([[e1]]_dl2e) -oo%E.
  rewrite H1 leNye; split => // _.
  rewrite (le_trans (dl2_ereal_translation_le0 e2))//.
  by rewrite -leeNr oppe0 addNye maxNye.
case: ifPn => //= H2.
  rewrite leNye; split => // _.
  by rewrite (eqP H2) leNye.
split.
- rewrite !big_cons big_nil adde0 => H.
  rewrite /maxe; case: ifPn => h.
  + by rewrite oppe0; exact: dl2_ereal_translation_le0.
  + rewrite oppeB; last first.
      rewrite /adde_def H1/= andbT.
      apply/negP => /andP[/eqP e1oo].
      rewrite eqe_oppLR/= => /eqP e3oo.
      by rewrite e1oo e3oo/= ltNyr in h.
    move: H.
    rewrite -leeBlDl; last first.
      rewrite fin_numN fin_numE H1/=.
      by rewrite -leye_eq -ltNge (le_lt_trans (dl2_ereal_translation_le0 e1)).
    rewrite orbF.
    rewrite ifF; last first.
      apply/negbTE.
      rewrite negb_or.
      rewrite -leye_eq -ltNge (le_lt_trans (dl2_ereal_translation_le0 e1))//=.
      by rewrite -leye_eq -ltNge (le_lt_trans (dl2_ereal_translation_le0 e2))//=.
    by rewrite oppeK addeC.
- rewrite !big_cons big_nil adde0 => H.
  rewrite /maxe; case: ifPn => [h|].
  + by rewrite leNye.
  + rewrite orbF negb_or => /andP[e1oo e2oo].
    move: H.
    rewrite /maxe.
    case: ifPn.
      rewrite oppe0 => e1e3 e20.
      rewrite sube_lt0 in e1e3; last first.
        by rewrite !fin_numE H1/= e1oo.
      rewrite (le_trans _ (ltW e1e3))//.
      rewrite -[leRHS]adde0.
      by rewrite leeD2l.
    move=> e1e3.
    rewrite oppeB; last first.
      by rewrite /adde_def H1/= andbT (negbTE e1oo)/=.
    rewrite addeC.
    rewrite -leeBlDr; last first.
      by rewrite fin_numN fin_numE e1oo H1.
    by rewrite oppeK addeC.
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
