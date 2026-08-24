From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.

(**md**************************************************************************)
(* # Algebraic structures for fuzzy DLs                                       *)
(*                                                                            *)
(* The hierarchy is layered so that each fuzzy DL of dl.v can be an instance  *)
(* of the weakest structure that supports it.  All four connectives are       *)
(* primitive: no DL of dl.v defines any of them from the others.              *)
(*                                                                            *)
(* ## Operations (in mtl_scope)                                               *)
(* ```                                                                        *)
(*      x `** y == monoidal conjunction (a t-norm), i.e., `mand x y`          *)
(*      x `++ y == monoidal disjunction (a t-conorm), i.e., `mor x y`         *)
(*         `~ x == negation, i.e., `mneg x`                                   *)
(*     x `--> y == implication, i.e., `mimpl x y`                             *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Structures for the individual operations                                *)
(* ```                                                                        *)
(*         tnormType d == bounded lattice with a monotone commutative monoid  *)
(*                        operation `**` whose unit is \top (integrality)     *)
(*                        The HB class is Tnorm.                              *)
(*       tconormType d == the order-dual: `++` is a monotone commutative      *)
(*                        monoid operation with unit \bot                     *)
(*                        The HB class is Tconorm.                            *)
(*      negationType d == bounded lattice with an antitone `~ swapping \top   *)
(*                        and \bot                                            *)
(*                        The HB class is Negation.                           *)
(*   implicationType d == bounded lattice with a `-->` antitone in its first  *)
(*                        and monotone in its second argument                 *)
(*                        The HB class is Implication.                        *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Structures combining operations, without linking axioms                 *)
(* ```                                                                        *)
(*     tnormImplType d == both `**` and `-->`                                 *)
(*                        The HB class is TnormImpl.                          *)
(*         fuzzyType d == all four operations                                 *)
(*                        The HB class is Fuzzy.                              *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Structures carrying a single linking axiom                              *)
(*                                                                            *)
(* These exist so that a builder producing (or requiring) that axiom has a    *)
(* class to complete; see the note above the hierarchy.  Rarely used directly.*)
(* ```                                                                        *)
(* involutiveNegType d == negationType with `~ `~ x = x                       *)
(*                        The HB class is InvolutiveNegation.                 *)
(*       negImplType d == fuzzyType with `~ x = x `--> \bot                   *)
(*                        The HB class is NegImpl.                            *)
(*         sImplType d == fuzzyType with x `--> y = `~ x `++ y                *)
(*                        The HB class is SImpl.                              *)
(* ```                                                                        *)
(*                                                                            *)
(* ## Structures with linking axioms                                          *)
(* ```                                                                        *)
(*    residuatedType d == `**` and `-->` form an adjoint pair:                *)
(*                          z `** x <= y  iff  x <= z `--> y                  *)
(*                        i.e., a bounded integral commutative residuated     *)
(*                        lattice, also known as an FL_ew-algebra             *)
(*                        The HB class is Residuated.                         *)
(*      deMorganType d == `**`, `++` and `~ satisfy the de Morgan laws        *)
(*                        The HB class is DeMorgan.                           *)
(*        dlAlgType d  == de Morgan algebra whose negation is implicative,    *)
(*                        i.e., `~ x = x `--> \bot                            *)
(*                        The HB class is DLAlgebra.                          *)
(*    involutiveType d == dlAlgType with `~ `~ x = x                          *)
(*                        The HB class is Involutive.                         *)
(*          flewType d == dlAlgType that is residuated                        *)
(*                        The HB class is FLewAlgebra.                        *)
(*          sAlgType d == involutiveType whose implication is the S-implica-  *)
(*                        tion x `--> y = `~ x `++ y (not residuated)         *)
(*                        The HB class is SAlgebra.                           *)
(*           mtlType d == flewType with prelinearity:                         *)
(*                          (x `--> y) `|` (y `--> x) = \top                  *)
(*                        The HB class is MTLAlgebra.                         *)
(*          imtlType d == involutive mtlType                                  *)
(*                        The HB class is IMTLAlgebra.                        *)
(*            blType d == divisible mtlType: x `** (x `--> y) = x `&` y       *)
(*                        The HB class is BLAlgebra.                          *)
(*         godelType d == blType with idempotent `**`.                        *)
(*.                       A BLAlgebra is also a GodelAlgebra.                 *)
(*            mvType d == involutive blType                                   *)
(*                        The HB class is MVAlgebra.                          *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope mtl_scope.
Delimit Scope mtl_scope with mtl.

Reserved Notation "x `** y" (at level 65).
Reserved Notation "x `++ y" (at level 50, left associativity).
Reserved Notation "x `--> y" (at level 69, right associativity).
Reserved Notation "`~ x" (at level 61).

Import Order.Theory.
Local Open Scope order_scope.

(******************************************************************************)
(* The four operations                                                        *)
(******************************************************************************)

HB.mixin Record TBLattice_isTnorm d T of Order.TBLattice d T := {
  mand : T -> T -> T;
  mandC : commutative mand;
  mandA : associative mand;
  mand1x : left_id (\top : T) mand;
  le_mand2l : forall x : T, {homo mand x : y z / y <= z};
}.

#[short(type="tnormType")]
HB.structure Definition Tnorm d :=
  { T of Order.TBLattice d T & TBLattice_isTnorm d T }.

Notation "x `** y" := (mand x y) : mtl_scope.

HB.mixin Record TBLattice_isTconorm d T of Order.TBLattice d T := {
  mor : T -> T -> T;
  morC : commutative mor;
  morA : associative mor;
  mor0x : left_id (\bot : T) mor;
  le_mor2l : forall x : T, {homo mor x : y z / y <= z};
}.

#[short(type="tconormType")]
HB.structure Definition Tconorm d :=
  { T of Order.TBLattice d T & TBLattice_isTconorm d T }.

Notation "x `++ y" := (mor x y) : mtl_scope.

HB.mixin Record TBLattice_isNegation d T of Order.TBLattice d T := {
  mneg : T -> T;
  le_mneg : {homo mneg : x y /~ x <= y};
  mneg1 : mneg \top = \bot;
  mneg0 : mneg \bot = \top;
}.

#[short(type="negationType")]
HB.structure Definition Negation d :=
  { T of Order.TBLattice d T & TBLattice_isNegation d T }.

Notation "`~ x" := (mneg x) : mtl_scope.

HB.mixin Record TBLattice_isImplication d T of Order.TBLattice d T := {
  mimpl : T -> T -> T;
  le_mimpl2l : forall x : T, {homo mimpl x : y z / y <= z};
  le_mimpl2r : forall x : T, {homo mimpl^~ x : y z /~ y <= z};
  mimpl1x : forall x : T, mimpl \top x = x;
  mimplx1 : forall x : T, mimpl x \top = \top;
}.

#[short(type="implicationType")]
HB.structure Definition Implication d :=
  { T of Order.TBLattice d T & TBLattice_isImplication d T }.

Notation "x `--> y" := (mimpl x y) : mtl_scope.

(******************************************************************************)
(* Combining the operations                                                   *)
(******************************************************************************)

#[short(type="tnormImplType")]
HB.structure Definition TnormImpl d :=
  { T of Tnorm d T & Implication d T }.

#[short(type="tconormImplType")]
HB.structure Definition TconormImpl d :=
  { T of Tconorm d T & Implication d T }.

#[short(type="fuzzyType")]
HB.structure Definition Fuzzy d :=
  { T of TnormImpl d T & Tconorm d T & Negation d T }.

(******************************************************************************)
(* Linking axioms                                                             *)
(******************************************************************************)
Open Scope mtl_scope.

HB.mixin Record TnormImpl_isResiduated d T of TnormImpl d T := {
  mand_residuation : forall x y z : T, (z `** x <= y) = (x <= z `--> y);
}.

HB.mixin Record Fuzzy_isDeMorgan d T of Fuzzy d T := {
  mneg_mand : forall x y : T, `~ (x `** y) = (`~ x) `++ (`~ y);
  mneg_mor : forall x y : T, `~ (x `++ y) = (`~ x) `** (`~ y);
}.

HB.mixin Record Fuzzy_isNegImpl d T of Fuzzy d T := {
  mnegE : forall x : T, `~ x = x `--> \bot;
}.

HB.mixin Record Fuzzy_isSImpl d T of Fuzzy d T := {
  mimplE : forall x y : T, x `--> y = (`~ x) `++ y;
}.

HB.mixin Record Negation_isInvolutive d T of Negation d T := {
  mnegK : involutive (mneg : T -> T);
}.

HB.mixin Record Implication_isPrelinear d T of Implication d T := {
  mimpl_prelinear : forall x y : T, (x `--> y) `|` (y `--> x) = \top;
}.

HB.mixin Record TnormImpl_isDivisible d T of TnormImpl d T := {
  mand_divisible : forall x y : T, x `** (x `--> y) = x `&` y;
}.

HB.mixin Record Tnorm_isIdempotent d T of Tnorm d T := {
  mandxx : forall x : T, x `** x = x;
}.

HB.mixin Record TnormImpl_isSoftIdem d T of TnormImpl d T := {
  mand_softidem : exists x : T, forall y : T, x >= (y `** y) `--> y;
}.

HB.mixin Record TconormImpl_isSoftIdem d T of TconormImpl d T := {
  mor_softidem : exists x : T, forall y : T, x >= (y `++ y) `--> y;
}.

(******************************************************************************)
(* The hierarchy                                                              *)
(******************************************************************************)

#[short(type="involutiveNegType")]
HB.structure Definition InvolutiveNegation d :=
  { T of Negation d T & Negation_isInvolutive d T }.

#[short(type="residuatedType")]
HB.structure Definition Residuated d :=
  { T of TnormImpl d T & TnormImpl_isResiduated d T }.

#[short(type="softIdemTnormType")]
HB.structure Definition SoftIdemTnorm d :=
  { T of TnormImpl d T & TnormImpl_isSoftIdem d T }.

#[short(type="softIdemTconormType")]
HB.structure Definition SoftIdemTconorm d :=
  { T of TconormImpl d T & TconormImpl_isSoftIdem d T }.

#[short(type="negImplType")]
HB.structure Definition NegImpl d :=
  { T of Fuzzy d T & Fuzzy_isNegImpl d T }.

#[short(type="sImplType")]
HB.structure Definition SImpl d :=
  { T of Fuzzy d T & Fuzzy_isSImpl d T }.

#[short(type="deMorganType")]
HB.structure Definition DeMorgan d :=
  { T of Fuzzy d T & Fuzzy_isDeMorgan d T }.

#[short(type="dlAlgType")]
HB.structure Definition DLAlgebra d :=
  { T of DeMorgan d T & NegImpl d T }.

#[short(type="involutiveType")]
HB.structure Definition Involutive d :=
  { T of DLAlgebra d T & InvolutiveNegation d T }.

#[short(type="flewType")]
HB.structure Definition FLewAlgebra d :=
  { T of DLAlgebra d T & TnormImpl_isResiduated d T }.

#[short(type="sAlgType")]
HB.structure Definition SAlgebra d :=
  { T of Involutive d T & SImpl d T }.

#[short(type="mtlType")]
HB.structure Definition MTLAlgebra d :=
  { T of FLewAlgebra d T & Implication_isPrelinear d T }.

#[short(type="imtlType")]
HB.structure Definition IMTLAlgebra d :=
  { T of MTLAlgebra d T & Involutive d T }.

#[short(type="blType")]
HB.structure Definition BLAlgebra d :=
  { T of MTLAlgebra d T & TnormImpl_isDivisible d T }.

#[short(type="godelType")]
HB.structure Definition GodelAlgebra d :=
  { T of BLAlgebra d T & Tnorm_isIdempotent d T }.

#[short(type="mvType")]
HB.structure Definition MVAlgebra d :=
  { T of BLAlgebra d T & IMTLAlgebra d T }.

Local Open Scope mtl_scope.

HB.instance Definition _ d (L : tnormType d) :=
  Monoid.isComLaw.Build L \top (@mand d L)
    (@mandA d L) (@mandC d L) (@mand1x d L).

HB.instance Definition _ d (L : tconormType d) :=
  Monoid.isComLaw.Build L \bot (@mor d L)
    (@morA d L) (@morC d L) (@mor0x d L).

(******************************************************************************)
(* Theory of t-norm lattices                                                  *)
(******************************************************************************)

Section TnormTheory.
Variables (d : Order.disp_t) (L : tnormType d).
Implicit Types x y z t : L.

Lemma mandx1 x : x `** \top = x.
Proof. by rewrite mandC mand1x. Qed.

Lemma le_mand2r x : {homo mand^~ x : y z / y <= z}.
Proof. by move=> y z yz; rewrite ![_ `** x]mandC le_mand2l. Qed.

Lemma le_mand2 x y z t : x <= z -> y <= t -> x `** y <= z `** t.
Proof. by move=> xz ?; rewrite (le_trans (@le_mand2r _ _ _ xz)) ?le_mand2l. Qed.

Lemma le_mandl x y : x `** y <= x.
Proof. by rewrite -[leRHS]mandx1 le_mand2l. Qed.

Lemma le_mandr x y : x `** y <= y.
Proof. by rewrite mandC le_mandl. Qed.

Lemma le_mandI x y : x `** y <= x `&` y.
Proof. by rewrite lexI le_mandl le_mandr. Qed.

Lemma mandx0 x : x `** \bot = \bot.
Proof. by apply/le_anti; rewrite le_mandr le0x. Qed.

Lemma mand0x x : \bot `** x = \bot.
Proof. by rewrite mandC mandx0. Qed.

End TnormTheory.

HB.instance Definition _ d (L : tnormType d) :=
  Monoid.isMulLaw.Build L \bot (@mand d L) (@mand0x d L) (@mandx0 d L).

(******************************************************************************)
(* Theory of t-conorm lattices                                                *)
(******************************************************************************)

Section TconormTheory.
Variables (d : Order.disp_t) (L : tconormType d).
Implicit Types x y z t : L.

Lemma morx0 x : x `++ \bot = x.
Proof. by rewrite morC mor0x. Qed.

Lemma le_mor2r x : {homo mor^~ x : y z / y <= z}.
Proof. by move=> y z yz; rewrite ![_ `++ x]morC le_mor2l. Qed.

Lemma le_mor2 x y z t : x <= z -> y <= t -> x `++ y <= z `++ t.
Proof. by move=> xz yt; rewrite (le_trans (@le_mor2r _ _ _ xz)) ?le_mor2l. Qed.

Lemma le_morl x y : x <= x `++ y.
Proof. by rewrite -[leLHS]morx0 le_mor2l. Qed.

Lemma le_morr x y : y <= x `++ y.
Proof. by rewrite morC le_morl. Qed.

Lemma le_morU x y : x `|` y <= x `++ y.
Proof. by rewrite leUx le_morl le_morr. Qed.

Lemma morx1 x : x `++ \top = \top.
Proof. by apply/le_anti; rewrite lex1 le_morr. Qed.

Lemma mor1x x : \top `++ x = \top.
Proof. by rewrite morC morx1. Qed.

End TconormTheory.

HB.instance Definition _ d (L : tconormType d) :=
  Monoid.isMulLaw.Build L \top (@mor d L) (@mor1x d L) (@morx1 d L).

(******************************************************************************)
(* Theory of involutive negation                                              *)
(******************************************************************************)

Section InvolutiveNegationTheory.
Variables (d : Order.disp_t) (L : involutiveNegType d).
Implicit Types x y : L.

Lemma mneg_inj : injective (mneg : L -> L).
Proof. exact: can_inj mnegK. Qed.

Lemma le_mneg2 x y : (`~ x <= `~ y) = (y <= x).
Proof.
apply/idP/idP => xy; last exact: le_mneg.
by rewrite -(mnegK y) -(mnegK x) le_mneg.
Qed.

Lemma le_mnegl x y : (`~ x <= y) = (`~ y <= x).
Proof. by rewrite -le_mneg2 mnegK. Qed.

Lemma le_mnegr x y : (x <= `~ y) = (y <= `~ x).
Proof. by rewrite -le_mneg2 mnegK. Qed.

Lemma mneg_meet x y : `~ (x `&` y) = (`~ x) `|` (`~ y).
Proof.
by apply/le_anti;
  rewrite le_mnegl lexI le_mnegl leUl le_mnegl leUr leUx !le_mneg2 leIl leIr.
Qed.

Lemma mneg_join x y : `~ (x `|` y) = (`~ x) `&` (`~ y).
Proof.
by apply/le_anti;
  rewrite le_mnegr lexI leUx !le_mneg2 leUl leUr le_mnegr leIl le_mnegr leIr.
Qed.

End InvolutiveNegationTheory.

(******************************************************************************)
(* Residuated t-norm lattices                                                 *)
(******************************************************************************)

HB.factory Record TBLattice_isResiduated d T of Order.TBLattice d T := {
  mand : T -> T -> T;
  mimpl : T -> T -> T;
  mandC : commutative mand;
  mandA : associative mand;
  mand1x : left_id (\top : T) mand;
  mand_residuation : forall x y z : T, (mand z x <= y) = (x <= mimpl z y);
}.

HB.builders Context d T of TBLattice_isResiduated d T.

Lemma le_mand2l (x : T) : {homo mand x : y z / y <= z}.
Proof.
by move=> y z yz; rewrite mand_residuation (le_trans yz) -?mand_residuation.
Qed.

Lemma le_mand2r (x : T) : {homo mand^~ x : y z / y <= z}.
Proof. by move=> y z yz; rewrite ![mand _ x]mandC; exact: le_mand2l. Qed.

HB.instance Definition _ :=
  TBLattice_isTnorm.Build d T mandC mandA mand1x le_mand2l.

Lemma le_mimpl2l (x : T) : {homo mimpl x : y z / y <= z}.
Proof.
by move=> y z yz; rewrite -mand_residuation (le_trans _ yz) ?mand_residuation.
Qed.

Lemma le_mimpl2r (x : T) : {homo mimpl^~ x : y z /~ y <= z}.
Proof.
move=> y z zy.
by rewrite -mand_residuation (le_trans (@le_mand2r _ _ _ zy)) ?mand_residuation.
Qed.

Lemma mimpl1x (x : T) : mimpl \top x = x.
Proof.
apply/le_anti.
by rewrite -[leLHS]mand1x mand_residuation lexx/= -mand_residuation mand1x.
Qed.

Lemma mimplx1 (x : T) : mimpl x \top = \top.
Proof. by apply/le_anti; rewrite lex1 -mand_residuation lex1. Qed.

HB.instance Definition _ := TBLattice_isImplication.Build d T
  le_mimpl2l le_mimpl2r mimpl1x mimplx1.

HB.instance Definition _ := TnormImpl_isResiduated.Build d T mand_residuation.

HB.end.

(******************************************************************************)
(* Theory of residuated t-norm lattices                                       *)
(******************************************************************************)

Section ResiduatedTheory.
Variables (d : Order.disp_t) (L : residuatedType d).
Implicit Types x y z t : L.

Lemma mandP x y z : x `** y <= z -> y <= x `--> z.
Proof. by rewrite mand_residuation. Qed.

Lemma mimplP x y z : y <= x `--> z -> x `** y <= z.
Proof. by rewrite mand_residuation. Qed.

Lemma mand_mimpl x y : x `** (x `--> y) <= y.
Proof. by rewrite mand_residuation. Qed.

Lemma le_mimpl_mand x y : x <= y `--> (y `** x).
Proof. by rewrite -mand_residuation. Qed.

Lemma mimpl_eq1 x y : (x `--> y == \top) = (x <= y).
Proof.
apply/eqP/idP => xy; first by rewrite -[x]mandx1 -xy mand_mimpl.
by apply/eqP; rewrite eq_le lex1 mandP// mandx1.
Qed.

Lemma mimplxx x : x `--> x = \top.
Proof. by apply/eqP; rewrite mimpl_eq1. Qed.

Lemma mimpl_trans x y z : (x `--> y) `** (y `--> z) <= x `--> z.
Proof.
by rewrite mandP// mandA (le_trans _ (mand_mimpl y z)) ?le_mand2// mand_mimpl.
Qed.

Lemma mand_mimplI x y : x `** (x `--> y) <= x `&` y.
Proof. by rewrite lexI le_mandl mand_mimpl. Qed.

Lemma mandUl x y z : x `** (y `|` z) = (x `** y) `|` (x `** z).
Proof.
by apply/le_anti; rewrite mimplP leUx -?mand_residuation ?le_mand2 ?leUl ?leUr.
Qed.

Lemma mandUr x y z : (x `|` y) `** z = (x `** z) `|` (y `** z).
Proof. by rewrite mandC mandUl !(mandC z). Qed.

Lemma mimplIr x y z : x `--> (y `&` z) = (x `--> y) `&` (x `--> z).
Proof.
by apply/le_anti; rewrite mandP ?lexI ?mimplP ?le_mimpl2l ?leIl ?leIr.
Qed.

Lemma mimplUl x y z : (x `|` y) `--> z = (x `--> z) `&` (y `--> z).
Proof.
apply/le_anti; rewrite mandP; first by rewrite lexI !le_mimpl2r ?leUl ?leUr.
by rewrite mandUr leUx !mand_residuation leIl leIr.
Qed.

End ResiduatedTheory.

Arguments mandP {d L x y z}.
Arguments mimplP {d L x y z}.

HB.instance Definition _ d (L : residuatedType d) :=
  Monoid.isAddLaw.Build L (@mand d L) (@Order.join d L)
    (@mandUr d L) (@mandUl d L).

(******************************************************************************)
(* Builders                                                                   *)
(******************************************************************************)

HB.factory Record TBLattice_isMeetTnorm d T of Order.TBLattice d T := {
  mand : T -> T -> T;
  mandE : forall x y : T, mand x y = x `&` y;
}.

HB.builders Context d T of TBLattice_isMeetTnorm d T.

Lemma mandC : commutative mand.
Proof. by move=> x y; rewrite !mandE meetC. Qed.

Lemma mandA : associative mand.
Proof. by move=> x y z; rewrite !mandE meetA. Qed.

Lemma mand1x : left_id (\top : T) mand.
Proof. by move=> x; rewrite mandE meet1x. Qed.

Lemma le_mand2l (x : T) : {homo mand x : y z / y <= z}.
Proof. by move=> y z yz; rewrite !mandE lexI leIl/= (le_trans _ yz) ?leIr. Qed.

HB.instance Definition _ :=
  TBLattice_isTnorm.Build d T mandC mandA mand1x le_mand2l.

Lemma mandxx (x : T) : mand x x = x.
Proof. by rewrite mandE meetxx. Qed.

HB.instance Definition _ := Tnorm_isIdempotent.Build d T mandxx.

HB.end.

HB.factory Record TBLattice_isJoinTconorm d T of Order.TBLattice d T := {
  mor : T -> T -> T;
  morE : forall x y : T, mor x y = x `|` y;
}.

HB.builders Context d T of TBLattice_isJoinTconorm d T.

Lemma morC : commutative mor.
Proof. by move=> x y; rewrite !morE joinC. Qed.

Lemma morA : associative mor.
Proof. by move=> x y z; rewrite !morE joinA. Qed.

Lemma mor0x : left_id (\bot : T) mor.
Proof. by move=> x; rewrite morE join0x. Qed.

Lemma le_mor2l (x : T) : {homo mor x : y z / y <= z}.
Proof. by move=> y z yz; rewrite !morE leUx leUl/= (le_trans yz) ?leUr. Qed.

HB.instance Definition _ :=
  TBLattice_isTconorm.Build d T morC morA mor0x le_mor2l.

HB.end.

Section Prelinear.
Variables (d : Order.disp_t) (L : residuatedType d).
Hypothesis tot : total (<=%O : rel L).

Lemma total_prelinear (x y : L) : (x `--> y) `|` (y `--> x) = \top.
Proof.
by have /orP[/[dup] xy|/[dup] xy] := tot x y; rewrite -mimpl_eq1 => /eqP ->;
  [rewrite join_l | rewrite join_r].
Qed.


End Prelinear.

Section Idempotent.
Variables (d : Order.disp_t) (L : residuatedType d).
Hypothesis mandxx : forall x : L, x `** x = x.
Implicit Types x y z : L.

Lemma idem_mandI x y : x `** y = x `&` y.
Proof.
by apply/le_anti; rewrite le_mandI/= -[leLHS]mandxx le_mand2 ?leIl ?leIr.
Qed.

Lemma idem_divisible x y : x `** (x `--> y) = x `&` y.
Proof.
apply/le_anti; rewrite idem_mandI !lexI !leIl/=.
by rewrite -idem_mandI mand_mimpl/= -mand_residuation idem_mandI meetA meetxx leIr.
Qed.

End Idempotent.

HB.factory Record MTLAlgebra_isIdempotent d T of MTLAlgebra d T := {
  mandxx : forall x : T, x `** x = x;
}.

HB.builders Context d T of MTLAlgebra_isIdempotent d T.

HB.instance Definition _ :=
  TnormImpl_isDivisible.Build d T (@idem_divisible d T mandxx).

HB.instance Definition _ := Tnorm_isIdempotent.Build d T mandxx.

HB.end.

HB.factory Record Residuated_isNegation d T of Residuated d T := {
  mneg : T -> T;
  mnegE : forall x : T, mneg x = x `--> \bot;
}.

HB.builders Context d T of Residuated_isNegation d T.

Lemma le_mneg : {homo mneg : x y /~ x <= y}.
Proof. by move=> x y yx; rewrite !mnegE le_mimpl2r. Qed.

Lemma mneg1 : mneg \top = \bot. Proof. by rewrite mnegE mimpl1x. Qed.
Lemma mneg0 : mneg \bot = \top. Proof. by rewrite mnegE mimplxx. Qed.

HB.instance Definition _ := TBLattice_isNegation.Build d T le_mneg mneg1 mneg0.

HB.end.

HB.factory Record TconormNegation_isImplication d T
    of Tnorm d T & Tconorm d T & Negation d T := {
  mimpl : T -> T -> T;
  mimplE : forall x y : T, mimpl x y = (`~ x) `++ y;
}.

HB.builders Context d T of TconormNegation_isImplication d T.

Lemma le_mimpl2l (x : T) : {homo mimpl x : y z / y <= z}.
Proof. by move=> y z yz; rewrite !mimplE le_mor2l. Qed.

Lemma le_mimpl2r (x : T) : {homo mimpl^~ x : y z /~ y <= z}.
Proof. by move=> y z zy; rewrite !mimplE le_mor2r ?le_mneg. Qed.

Lemma mimpl1x (x : T) : mimpl \top x = x.
Proof. by rewrite mimplE mneg1 mor0x. Qed.

Lemma mimplx1 (x : T) : mimpl x \top = \top.
Proof. by rewrite mimplE morx1. Qed.

HB.instance Definition _ :=
  TBLattice_isImplication.Build d T le_mimpl2l le_mimpl2r mimpl1x mimplx1.

Lemma mnegE (x : T) : `~ x = mimpl x \bot.
Proof. by rewrite mimplE morx0. Qed.

HB.instance Definition _ := Fuzzy_isSImpl.Build d T mimplE.
HB.instance Definition _ := Fuzzy_isNegImpl.Build d T mnegE.

HB.end.

HB.factory Record TnormNegation_isTconorm d T
    of TnormImpl d T & InvolutiveNegation d T := {
  mor : T -> T -> T;
  mneg_mor : forall x y : T, `~ (mor x y) = (`~ x) `** (`~ y);
}.

HB.builders Context d T of TnormNegation_isTconorm d T.

Lemma morE x y : mor x y = `~ ((`~ x) `** (`~ y)).
Proof. by rewrite -mneg_mor mnegK. Qed.

Lemma morC : commutative mor.
Proof. by move=> x y; rewrite !morE mandC. Qed.

Lemma morA : associative mor.
Proof. by move=> x y z; rewrite !morE !mnegK mandA. Qed.

Lemma mor0x : left_id \bot mor.
Proof. by move=> x; rewrite morE mneg0 mand1x mnegK. Qed.

Lemma le_mor2l (x : T) : {homo mor x : y z / y <= z}.
Proof. by move=> y z yz; rewrite !morE le_mneg// le_mand2l ?le_mneg. Qed.

HB.instance Definition _ :=
  TBLattice_isTconorm.Build d T morC morA mor0x le_mor2l.

Lemma mneg_mand x y : `~ (x `** y) = mor (`~ x) (`~ y).
Proof. by rewrite morE !mnegK. Qed.

HB.instance Definition _ := Fuzzy_isDeMorgan.Build d T mneg_mand mneg_mor.

HB.end.

HB.factory Record TconormNegation_isTnorm d T
    of TconormImpl d T & InvolutiveNegation d T := {
  mand : T -> T -> T;
  mneg_mand : forall x y : T, `~ (mand x y) = (`~ x) `++ (`~ y);
}.

HB.builders Context d T of TconormNegation_isTnorm d T.

Lemma mandE x y : mand x y = `~ ((`~ x) `++ (`~ y)).
Proof. by rewrite -mneg_mand mnegK. Qed.

Lemma mandC : commutative mand.
Proof. by move=> x y; rewrite !mandE morC. Qed.

Lemma mandA : associative mand.
Proof. by move=> x y z; rewrite !mandE !mnegK morA. Qed.

Lemma mand1x : left_id \top mand.
Proof. by move=> x; rewrite mandE mneg1 mor0x mnegK. Qed.

Lemma le_mand2l (x : T) : {homo mand x : y z / y <= z}.
Proof. by move=> y z yz; rewrite !mandE le_mneg// le_mor2l ?le_mneg. Qed.

HB.instance Definition _ :=
  TBLattice_isTnorm.Build d T mandC mandA mand1x le_mand2l.

Lemma mneg_mor x y : `~ (x `++ y) = mand (`~ x) (`~ y).
Proof. by rewrite mandE !mnegK. Qed.

HB.instance Definition _ := Fuzzy_isDeMorgan.Build d T mneg_mand mneg_mor.

HB.end.

(******************************************************************************)
(* Theory of FL_ew-algebras                                                   *)
(******************************************************************************)

Section FLewTheory.
Variables (d : Order.disp_t) (L : flewType d).
Implicit Types x y z t : L.

Lemma mandN x : x `** (`~ x) = \bot.
Proof. by apply/le_anti; rewrite le0x andbT mnegE mand_mimpl. Qed.

Lemma le_mnegneg x : x <= `~ `~ x.
Proof. by rewrite !mnegE -mand_residuation mandC -mnegE mandN. Qed.

Lemma mneg3 x : (`~ `~ `~ x) = `~ x.
Proof. by apply/le_anti; rewrite le_mneg le_mnegneg. Qed.

End FLewTheory.

(******************************************************************************)
(* Theory of MTL-algebras                                                     *)
(******************************************************************************)

Section MTLTheory.
Variables (d : Order.disp_t) (L : mtlType d).
Implicit Types x y z t : L.

Lemma mand_prelinear x y z : ((x `--> y) `|` (y `--> x)) `** z = z.
Proof. by rewrite mimpl_prelinear mand1x. Qed.

End MTLTheory.
