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
(* - dl2_andC_nary == n-ary commutativity of conjunction                      *)
(* - dl2_andC == commutativity of conjunction                                 *)
(* - dl2_andA == associativity of conjunction                                 *)
(* - dl2_orC_nary == n-ary commutativity of disjunction                       *)
(* - dl2_orC == commutativity of disjunction                                  *)
(* - dl2_orA == associativity of disjunction                                  *)
(*                                                                            *)
(* ## Adequacy                                                                *)
(* - dl2_translation_le0 == invariant for the translation: all values are in  *)
(*                          the range $(-\infty, 0]$                          *)
(* - dl2_nary_inversion_andE1 == inversion lemma for conjunction/true         *)
(* - dl2_nary_inversion_andE0 == inversion lemma for conjuntion/false         *)
(* - dl2_nary_inversion_orE1 == inversion lemma for disjunction/true          *)
(* - dl2_nary_inversion_orE0 == inversion lemma for disjunction/false         *)
(* - dl2_translations_Vector_coincide == shows that the Boolean translation   *)
(*   and the DL2 translation coincide on expressions of type Vector_T         *)
(* - dl2_translations_Index_coincide == shows that the Boolean translation    *)
(*   and the DL2 translation coincide on expressions of type Index_T          *)
(* - dl2_translations_Real_coincide == shows that the Boolean translation and *)
(*   the DL2 translation coincide on expressions of type Real_T               *)
(* - dl2_adeuqacy == final adequacy result for DL2                            *)
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
Proof.
by move=> pi; rewrite /=/sumR !big_map (perm_big _ pi)/=.
Qed.

Lemma dl2_mandC f1 f2 (e1 e2 : expr (Bool_T_def f1 m_def f2)) : [[ e1 `** e2 ]]_dl2 = [[ e2 `** e1 ]]_dl2.
Proof.
by rewrite /=/sumR ?big_cons ?big_nil /= addr0 addr0 addrC.
Qed.

Lemma dl2_mandA f1 f2 (e1 e2 e3 : expr (Bool_T_def f1 m_def f2)) :
  [[ e1 `** (e2 `** e3) ]]_dl2 = [[ (e1 `** e2) `** e3 ]]_dl2.
Proof.
by rewrite /=/sumR ?big_cons ?big_nil !addr0 addrA.
Qed.

Lemma dl2_morC_nary f1 f2 (s1 s2 : seq (expr (Bool_T_def f1 m_def f2))) :
  perm_eq s1 s2 -> [[ldl_mor s1]]_dl2 = [[ldl_mor s2]]_dl2.
Proof.
move => pi; rewrite //=; repeat case: ifP; move => /eqP h1 /eqP h2; rewrite big_map in h1;
rewrite big_map in h2; rewrite//=; have H := (@perm_big R maxr 0 _ _ _ _ _ pi);
try rewrite H in h2; try rewrite H in h2; rewrite//=.
rewrite /sumR !big_map (perm_big _ pi)//=.
(*by move=> pi; rewrite /=/prodR !big_map (perm_big _ pi)/= (perm_size pi).*)
Qed.

Lemma dl2_morC f1 f2 (e1 e2 : expr (Bool_T_def f1 m_def f2)) :
  [[ e1 `++ e2 ]]_dl2 = [[ e2 `++ e1 ]]_dl2.
Proof.
have h : maxr ([[e2]]_dl2) (maxr ([[e1]]_dl2) 0) = maxr ([[e1]]_dl2) (maxr ([[e2]]_dl2) 0)
by rewrite /maxr; repeat case: ifP; rewrite//=; try nra.
rewrite/=; repeat case: ifP; rewrite /sumR !big_cons !big_nil ?addr0//=; move =>  /eqP h1 /eqP h2;
rewrite ?h in h1; rewrite//=.
by rewrite /=/sumR  addrC//=.
(*rewrite /=/prodR !big_cons big_nil !mulr1; congr *%R.
by rewrite mulrC.*)
Qed.

Lemma dl2_translation_le0 f e : [[ e ]]_dl2 <= 0 :> type_translation (Bool_T_undef f m_def l_undef).
Proof.
dependent induction e using expr_ind' => /=.
- by case: b.
- rewrite /maxr; case: ifP; move => h; lra. 
(*case: ifP; move => h; try lra.
  have IH2 := IHe2 e2.
  apply IH2; rewrite //=.*)
- rewrite /sumR big_map big_seq sumr_le0// => t tl.
  move/List.Forall_forall : H => /(_ t); apply => //.
  exact/In_in.
- rewrite /sumR big_map big_seq.
  case: ifP; move => /eqP H1//=.
  have h : forall (r : R), r < 0 -> 1/r <= 0. intros. rewrite (ler_ndivrMr 0 1) ?mul0r//=. 
  admit.



(*rewrite /prodR big_map big_seq; have [ol|ol] := boolP (odd (length l)).
    rewrite exprS -signr_odd ol expr1 mulrN1 opprK mul1r.
    have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2 != 0); last first.
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
  have [l0|l0] := pselect (forall i, i \in l -> [[i]]_dl2 != 0); last first.
    move/existsNP : l0 => [/= x /not_implyP[xl /negP/negPn/eqP x0]].
    rewrite le_eqVlt; apply/orP; left.
    rewrite eq_sym prodr_seq_eq0; apply/hasP; exists x => //.
    by rewrite xl x0 eqxx.
  apply/ltW; rewrite -sgr_gt0 -big_seq prodrN1.
    by rewrite -signr_odd (negbTE ol) expr0.
  move=> e el; rewrite lt_neqAle l0//=.
  by move/List.Forall_forall : H => /(_ e); apply => //; exact/In_in.*)

- case: c => //=.
  by rewrite oppr_le0 le_max lexx orbT.
Admitted.

(*move to mathcomp_extra later*)
Lemma maxr_le0_x0 (x : R) :
  x <= 0 -> maxr x 0 = 0.
Proof. 
intros; rewrite/maxr; case: ifP; lra.
Qed.

(*Lemma div_lt (x y : R) :
  x > 0 -> y < 0 -> x / y < 0.
Proof.
intros. rewrite ltr_ndivrMr ?mul0r//=.
Qed.*)

Lemma dl2_morA f1 (e1 e2 e3 : expr (Bool_T_undef f1 m_def l_undef)) :
  [[ e1 `++ (e2 `++ e3) ]]_dl2 = [[ (e1 `++ e2) `++ e3 ]]_dl2.
Proof.
have he1 := dl2_translation_le0 _ e1.
have he2 := dl2_translation_le0 _ e2.
have he3 := dl2_translation_le0 _ e3.
rewrite /= /sumR !big_cons !big_nil !addr0; repeat case: ifP; rewrite//=;
 try nra.
- move => _;  rewrite  ?maxr_le0_x0 ?maxr_le0_x0//=; lra. 
- rewrite maxr_le0_x0//= maxr_le0_x0//=; lra. 
- move => _; rewrite maxr_le0_x0//= maxr_le0_x0//=; lra. 
- rewrite maxr_le0_x0//= maxr_le0_x0//=; lra. 
- move => _ _ _. rewrite maxr_le0_x0//= maxr_le0_x0//=; lra. 
- rewrite maxr_le0_x0//= maxr_le0_x0//=; lra.
- move => _; rewrite maxr_le0_x0//= maxr_le0_x0//=; lra.  
- rewrite maxr_le0_x0//= maxr_le0_x0//=; lra. 
- move => _ _; rewrite maxr_le0_x0//= maxr_le0_x0//=; lra. 
- rewrite maxr_le0_x0//= maxr_le0_x0//=; lra. 
- move => _; rewrite maxr_le0_x0//= maxr_le0_x0//=; lra. 
- rewrite maxr_le0_x0//= maxr_le0_x0//=; lra. 
Qed.

Theorem dl2_mand_unit f1 f2 (e :  (expr (Bool_T_def f1 m_def f2))) :
  [[ e `** (ldl_bool _ _ _ _ true) ]]_dl2 = [[ e ]]_dl2.
Proof.
rewrite //=/sumR !big_cons big_nil !addr0//=.
Qed.

(*this does not work. need to think about or again*)
Theorem dl2_mor_unit f1 f2 (e :  (expr (Bool_T_def f1 m_def f2))) :
  [[ e `++ (ldl_bool _ _ _ _ false) ]]_dl2 = [[ e ]]_dl2.
Proof.
rewrite//= !big_cons big_nil; case: ifP.
- rewrite /maxr; repeat case: ifP; try lra.
Admitted.

Theorem dl2_residuation (e1 e2 e3 :  (expr (Bool_T_undef impl_def m_def l_undef))) :
  [[ e1 `** e2 ]]_dl2 <= [[ e3 ]]_dl2 <->
    [[ e2 ]]_dl2 <= [[ e1 `=> e3 ]]_dl2.
Proof.
split; move => /= H.
- rewrite /sumR !big_cons big_nil addr0 in H. 
  rewrite/maxr; case: ifP; move => /eqP h; try lra.
  rewrite oppr0.
  exact (dl2_translation_le0 _ e2).
- rewrite /sumR !big_cons big_nil addr0.
  move: H; rewrite/maxr;  case: ifP; move => h1 h2; lra.
Qed.

Definition is_dl2 b (x : R) := if b then x == 0 else x < 0.

Lemma dl2_nary_inversion_mandE1 f (s : seq (expr (Bool_T_undef f m_def l_undef))) :
  is_dl2 true ([[ ldl_mand s ]]_dl2) ->
  (forall i, (i < size s)%N -> is_dl2 true ([[ nth (ldl_bool _ _ _ _ false) s i ]]_dl2)).
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

Lemma dl2_nary_inversion_mandE0 f (s : seq (expr (Bool_T_undef f m_def l_undef))) :
  is_dl2 false ([[ ldl_mand s ]]_dl2) ->
  (exists i, (is_dl2 false ([[ nth (ldl_bool _ _ _ _ false) s i ]]_dl2)) && (i < size s)%nat).
Proof.
rewrite/is_dl2.
elim: s => [|h t ih] //=; first by rewrite /sumR big_nil ltxx.
rewrite /sumR big_cons => /naddr_lt0 => /(_ (dl2_translation_le0 _ _)).
have : (\sum_(j <- [seq [[i]]_dl2 | i <- t]) j <= 0).
  rewrite big_seq_cond; apply: sumr_le0 => /= z.
  by rewrite andbT => /mapP[/= e et ->]; exact: dl2_translation_le0.
move=> /[swap] /[apply] /orP[H|/ih[j /andP[j0 jt]]].
  by exists 0%N; rewrite /= H.
by exists j.+1; rewrite /= j0.
Qed.

Lemma dl2_nary_inversion_morE1 f (s : seq (expr (Bool_T_undef f m_def l_undef))) :
  is_dl2 true ([[ ldl_mor s ]]_dl2) ->
  exists i, ([[ nth (ldl_bool _ _ _ _ false) s i ]]_dl2 == 0) && (i < size s)%nat.
Proof.
elim: s => [|h t ih] /=. admit.
  (*rewrite /prodR big_nil mulr1 expr1.
  by rewrite lt_eqF//.
rewrite mulf_eq0 signr_eq0/=.
rewrite /prodR big_cons mulf_eq0 => /orP[H|/eqP H].
  by exists 0%N; rewrite /= H.
have /ih[j /andP[Hj jt]] : [[ldl_mor t]]_dl2 == 0 by rewrite /= /prodR H mulr0.
by exists j.+1; rewrite /= Hj.*)
Admitted.

Lemma dl2_nary_inversion_morE0 f (Es : seq (expr (Bool_T_undef f m_def l_undef)) ) :
    is_dl2 false ([[ ldl_mor Es ]]_dl2)  -> 
    (forall i, (i < size Es)%nat -> is_dl2 false ([[ nth (ldl_bool _ _ _ _ false) Es i ]]_dl2)).
Proof.
elim: Es => //= a l IH.
(*rewrite /prodR big_cons mulrCA mulr_lt0 => /andP[aneq0]/andP[]/[swap] _.
rewrite exprS -mulrA mulN1r oppr_eq0 => lneq0.
have ale0 := dl2_translation_le0 a.
have alt0 : ([[a]]_dl2 < 0) by rewrite lt_neqAle aneq0 ale0.
elim => [_//=|i _].
rewrite ltnS => isize.
apply IH => //.
rewrite lt_neqAle lneq0/= /prodR big_map.
apply: prodr_le0 => j.
exact: dl2_translation_le0.*)
Admitted.

Lemma dl2_inversion_implE1 (E1 E2 : expr (Bool_T_undef impl_def m_def l_undef)) :
  is_dl2 true ([[  E1 `=> E2 ]]_dl2) ->
     is_dl2 false ([[ E1 ]]_dl2) || is_dl2 true ([[ E2 ]]_dl2).
Proof.
rewrite//=/maxr; case: ifP => H1 H2; 
have H2' := dl2_translation_le0 _ E2;
have H1' := dl2_translation_le0 _ E1; try lra.
Qed.

(*not provable for this semantic of implication*)
(*Lemma dl2_inversion_implE0 (E1 E2 : expr (Bool_T_undef impl_def m_def l_undef)) :
  is_dl2 false ([[  E1 `=> E2 ]]_dl2) ->
     is_dl2 true ([[ E1 ]]_dl2) && is_dl2 false([[ E2 ]]_dl2).
Proof.
rewrite//=/maxr; case: ifP =>  H1 H2.
- lra.
- have H := dl2_translation_le0 E1. 
have h : - ([[E1]]_dl2 - [[E2]]_dl2) < 0 ->
           [[E1]]_dl2 > [[E2]]_dl2 by intros; lra.
(*apply h in H2. 
have h' : [[E2]]_dl2 < [[E1]]_dl2 ->
          [[E1]]_dl2 <= 0 ->
          [[E2]]_dl2 < 0 by intros; lra.
apply (h' H2) in H; rewrite H orbT. (*false, this case doesn't go through - try and fix the definition?*)
admit.*)
(*- rewrite H1 addr0 in H2. by rewrite H2//=.
- exfalso. lra.*)
Admitted.*)

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

(*only adequate without implication for this semantics of implication *)
Lemma dl2_adequacy (e : expr (Bool_T_undef impl_undef m_def l_undef)) b :
  is_dl2 b ([[ e ]]_dl2) -> [[ e ]]_B = b.
Proof.
dependent induction e using expr_ind'.
- move: b b0 => [] [] //=; by rewrite ?lt_irreflexive ?lt_eqF ?ltrN10.
(*- move: b => [].
  + move/(dl2_inversion_implE1); move/orP => [ H1 | H2].
    * rewrite //= implybE. rewrite //= in IHe1. rewrite (IHe1 e1 erefl JMeq_refl (false) H1).
      have tf : ~~ false = true. by rewrite//=.
      rewrite tf orTb//=.
    * rewrite //= implybE. rewrite //= in IHe2. 
      by rewrite (IHe2 e2 erefl JMeq_refl (true) H2) orbT.
  + move/(dl2_inversion_implE0); rewrite//=; move/andP => [ H1  H2].
    rewrite implybE Bool.orb_false_intro//=. 
    * rewrite //= in IHe1. by rewrite (IHe1 e1 erefl JMeq_refl (true)  H1)//=.
    * rewrite //= in IHe2. by rewrite (IHe2 e2 erefl JMeq_refl (false) H2)//=.*)
- rewrite List.Forall_forall in H.
  move: b => [].
  + move /(dl2_nary_inversion_mandE1).
    rewrite [bool_translation (ldl_mand l)]/= big_map big_seq big_all_cond => h.
    apply: allT => x/=.
    apply/implyP => /nthP xnth.
    have [i il0 <-] := xnth (ldl_bool _ _ _ _ false).
    apply: H => //. rewrite ?h// -In_in mem_nth//.
    by rewrite h.
  + move/dl2_nary_inversion_mandE0.
    rewrite [bool_translation (ldl_mand l)]/= big_map big_all.
    elim=>// i /andP[/eqP i0 isize].
    apply/allPn; exists (nth (ldl_bool _ _ _ _ false) l i); first by rewrite mem_nth.
    apply/negPf; apply: H => //.
    * by rewrite -In_in mem_nth.
    * rewrite /is_dl2/=. move: i0.
      by rewrite eqb_id.
- rewrite List.Forall_forall in H.
  move: b => [].
  + move/dl2_nary_inversion_morE1.
    rewrite [bool_translation (ldl_mor l)]/= big_map big_has.
    elim=>// i /andP[/eqP i0 isize].
    apply/hasP; exists (nth (ldl_bool _ _ _ _ false) l i); first by rewrite mem_nth.
    apply: H => //.
    by rewrite -In_in mem_nth.
    rewrite /is_dl2/=. by rewrite i0.
  + move/dl2_nary_inversion_morE0.
    rewrite [bool_translation (ldl_mor l)]/= big_map big_has => h.
    apply/hasPn => x.
    move/nthP => xnth.
    have [i il0 <-] := xnth (ldl_bool _ _ _ _ false).
    apply/negPf; apply: H => //.
    * by rewrite ?h// -In_in mem_nth.
    * by rewrite h.
- case: c; rewrite //=; rewrite -!dl2_translations_Real_coincide;
  set t1 := _ e1; set t2 := _ e2; case: b => //.
  + by rewrite /is_dl2 => /eqP/maxr0_le; rewrite subr_le0.
  + rewrite/is_dl2 oppr_lt0 /maxr; case: ifPn; first by rewrite lt_irreflexive.
    by rewrite subr_gt0 => _; move/lt_geF.
  + by rewrite /is_dl2 oppr_eq0 normr_eq0 subr_eq0.
  + rewrite/is_dl2; rewrite oppr_lt0 normr_gt0.
    by rewrite subr_eq0 => /eqP h; apply/eqP.
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
  dl2_and v = sumR (map (dl2_translation \o ldl_real) (seq_of_rV v)).
Proof.
rewrite /sumR !big_map /dl2_and -enumT big_enum.
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
