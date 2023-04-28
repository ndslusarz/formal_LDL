
module LossFunctions.Test where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Bool using (_∧_; T) renaming (Bool to 𝔹; true to ⊤; false to ⊥)
open import Data.Bool.Properties
open import Data.Rational
open import Data.Rational.Properties
open import Relation.Binary.PropositionalEquality
open import Data.Vec.Functional
open import Relation.Unary using (_∈_)

postulate +∞ : ℚ
postulate -∞ : ℚ
postulate -∞-min : ∀ p → -∞ ≤ p
postulate p≤q⇒p-q≤0 : ∀ {p q} → p ≤ q → p - q ≤ 0ℚ

-----------
-- Types --
-----------

data Type : Set where
  _↦_ : (τ₁ : Type) → (τ₂ : Type) → Type
  Bool : Type
  Real : Type
  Index : ℕ → Type
  Vec : Type → ℕ → Type

infixr 10 _↦_

-----------------
-- Expressions --
-----------------

data Builtin : Set where
  and  : Builtin
  true : Builtin
  false : Builtin
  real : ℚ → Builtin
  _<=_ : Builtin

variable
  n : ℕ

data Expr : ℕ → Set where
  lam : (τ : Type) → (e : Expr (suc n)) → Expr n
  app : (e1 : Expr n) (e2 : Expr n) → Expr n
  var : (v : Fin n) → Expr n
  builtin : (b : Builtin) → Expr n

---------------------
-- Typing relation --
---------------------

TypeContext : ℕ → Set
TypeContext n = Vector Type n

_++ᵗ_ : TypeContext n → Type → TypeContext (suc n)
Γ ++ᵗ τ = τ ∷ Γ

ϕ : TypeContext 0
ϕ ()

variable
  e e₁ e₂ : Expr n
  τ τ₁ τ₂ : Type
  Γ : TypeContext n

typeOfBuiltin : Builtin → Type
typeOfBuiltin and  = Bool ↦ Bool ↦ Bool
typeOfBuiltin true = Bool
typeOfBuiltin false = Bool
typeOfBuiltin (real _) = Real
typeOfBuiltin _<=_ = Real ↦ Real ↦ Bool

data _⊢_~_ : TypeContext n → Expr n → Type → Set where
  tVar : ∀ {v} → Γ ⊢ var v ~ Γ v
  tBuiltin : ∀ {b} → Γ ⊢ builtin b ~ typeOfBuiltin b
  tLam : (Γ⁺⊢e~τ : (Γ ++ᵗ τ₁) ⊢ e ~ τ₂) → Γ ⊢ lam τ₁ e ~ (τ₁ ↦ τ₂)
  tApp : (Γ⊢e₁~τ₁↦τ₂ : Γ ⊢ e₁ ~ (τ₁ ↦ τ₂)) → (Γ ⊢ e₂ ~ τ₁) → (Γ ⊢ app e₁ e₂ ~ τ₂)

--------------------------------
-- Generic semantics of types --
--------------------------------

record BoolTypeSemantics : Set₁ where
  field
    ⟪Bool⟫ : Set

module GenericTypeSemantics (boolTypeSem : BoolTypeSemantics) where 
  open BoolTypeSemantics boolTypeSem
  
  ⟪_⟫ : Type → Set
  ⟪ Bool ⟫     = ⟪Bool⟫
  ⟪ Real ⟫     = ℚ
  ⟪ Vec A n ⟫  = Vector ⟪ A ⟫ n
  ⟪ Index n ⟫  = Fin n
  ⟪ τ₁ ↦ τ₂ ⟫ = ⟪ τ₁ ⟫ → ⟪ τ₂ ⟫
  
--------------------------------------
-- Generic semantics of expressions --
--------------------------------------

module GenericExprSemantics (boolTypeSem : BoolTypeSemantics) where
  open BoolTypeSemantics boolTypeSem
  open GenericTypeSemantics boolTypeSem
  
  ⟪_⟫ᶜ : TypeContext n → Set
  ⟪_⟫ᶜ {n} Γ = (i : Fin n) → ⟪ Γ i ⟫ 

  ⟪ϕ⟫ᶜ : ⟪ ϕ ⟫ᶜ
  ⟪ϕ⟫ᶜ ()
  
  _++ˢ_ : ⟪ Γ ⟫ᶜ → ⟪ τ ⟫ → ⟪ Γ ++ᵗ τ ⟫ᶜ
  (⟪Γ⟫ ++ˢ ⟪τ⟫) zero    = ⟪τ⟫
  (⟪Γ⟫ ++ˢ ⟪τ⟫) (suc i) = ⟪Γ⟫ i
  
  record BoolExprSemantics  : Set₁ where 
    field
      ⟦and⟧ : ⟪ typeOfBuiltin and ⟫ 
      ⟦true⟧ : ⟪ typeOfBuiltin true ⟫
      ⟦false⟧ : ⟪ typeOfBuiltin false ⟫
      ⟦<=⟧ : ⟪ typeOfBuiltin _<=_ ⟫

  module Semantics (boolExprSem : BoolExprSemantics) where
    open BoolExprSemantics boolExprSem
    
    builtinSem : ∀ b → ⟪ typeOfBuiltin b ⟫
    builtinSem and  = ⟦and⟧
    builtinSem true = ⟦true⟧
    builtinSem false = ⟦false⟧
    builtinSem (real l) = l
    builtinSem _<=_ = ⟦<=⟧

    exprSem : ⟪ Γ ⟫ᶜ → ∀ e {τ} → Γ ⊢ e ~ τ → ⟪ τ ⟫
    exprSem ⟪Γ⟫ (lam τ e) (tLam Γ⁺⊢e~τ) = λ v → exprSem (⟪Γ⟫ ++ˢ v) e Γ⁺⊢e~τ
    exprSem ⟪Γ⟫ (app e₁ e₂) (tApp ⊢e₁ ⊢e₂) = exprSem ⟪Γ⟫ e₁ ⊢e₁ (exprSem ⟪Γ⟫ e₂ ⊢e₂)
    exprSem ⟪Γ⟫ (var v) tVar = ⟪Γ⟫ v
    exprSem ⟪Γ⟫ (builtin b) tBuiltin    = builtinSem b

------------------------
-- Standard semantics --
------------------------

module _ where
  open GenericTypeSemantics

  ⟪Bool⟫ₛ : BoolTypeSemantics
  ⟪Bool⟫ₛ = record { ⟪Bool⟫ = 𝔹 }

  ⟪_⟫ₛ : Type → Set
  ⟪_⟫ₛ = ⟪_⟫ ⟪Bool⟫ₛ

  open GenericExprSemantics ⟪Bool⟫ₛ

  ⟪_⟫ᶜₛ : TypeContext n → Set
  ⟪_⟫ᶜₛ  = ⟪_⟫ᶜ
  
  ⟪ϕ⟫ᶜₛ : ⟪ ϕ ⟫ᶜ
  ⟪ϕ⟫ᶜₛ ()

  ⟦BoolExpr⟧ₛ : BoolExprSemantics
  ⟦BoolExpr⟧ₛ = record
    { ⟦and⟧ = _∧_
    ; ⟦true⟧ = ⊤
    ; ⟦false⟧ = ⊥
    ; ⟦<=⟧ = _≤ᵇ_
    }

  open Semantics ⟦BoolExpr⟧ₛ public
    renaming
    ( exprSem to ⟦_⟧ₛ
    ; builtinSem to ⟦_⟧ᵇₛ
    )
    
  
-----------------------------
-- Loss function semantics --
-----------------------------

module _ where

  open GenericTypeSemantics

  ⟪Bool⟫ₗ : BoolTypeSemantics
  ⟪Bool⟫ₗ = record
    { ⟪Bool⟫ = ℚ
    }
    
  ⟪_⟫ₗ : Type → Set
  ⟪_⟫ₗ = ⟪_⟫ ⟪Bool⟫ₗ

  open GenericExprSemantics ⟪Bool⟫ₗ

  ⟪_⟫ᶜₗ : TypeContext n → Set
  ⟪_⟫ᶜₗ  = ⟪_⟫ᶜ
  
  ⟪ϕ⟫ᶜₗ : ⟪ ϕ ⟫ᶜ
  ⟪ϕ⟫ᶜₗ ()
  
  ⟦BoolExpr⟧ₗ : BoolExprSemantics
  ⟦BoolExpr⟧ₗ = record
    { ⟦and⟧ = _⊔_
    ; ⟦true⟧ = -∞
    ; ⟦false⟧ = +∞
    ; ⟦<=⟧ = _-_
    }    
  
  open Semantics ⟦BoolExpr⟧ₗ public
    renaming
    ( exprSem to ⟦_⟧ₗ
    ; builtinSem to ⟦_⟧ᵇₗ
    )

  ⟦⊤⟧ₗ : ℚ → Set
  ⟦⊤⟧ₗ q = q ≤ 0ℚ
  

---------------
-- Soundness --
---------------

mutual
  relCtx : ∀ (Γ : TypeContext n) → ⟪ Γ ⟫ᶜₛ → ⟪ Γ ⟫ᶜₗ → Set
  relCtx Γ ⟪Γ⟫ₛ ⟪Γ⟫ₗ = ∀ i → relType (Γ i) (⟪Γ⟫ₛ i) (⟪Γ⟫ₗ i)

  relType : ∀ τ → ⟪ τ ⟫ₛ → ⟪ τ ⟫ₗ → Set
  relType (τ₁ ↦ τ₂) f g = ∀ {x y} → relType τ₁ x y → relType τ₂ (f x) (g y)
  relType Bool       b q = T b → q ∈ ⟦⊤⟧ₗ
  relType Real      q₁ q₂ = q₁ ≡ q₂
  relType (Vec A n) xs₁ xs₂ = ∀ i → relType A (xs₁ i) (xs₂ i)
  relType (Index n) i₁ i₂ = i₁ ≡ i₂

soundnessBuiltin : ∀ b → relType (typeOfBuiltin b) ⟦ b ⟧ᵇₛ ⟦ b ⟧ᵇₗ
soundnessBuiltin and {⊤} {p₁} b₁⇒p₁∈⊤ {⊤} {q₂} b₂⇒p₂∈⊤ tt = ⊔-lub (b₁⇒p₁∈⊤ _) (b₂⇒p₂∈⊤ _)
soundnessBuiltin true _   = -∞-min 0ℚ
soundnessBuiltin false () 
soundnessBuiltin (real x) = refl
soundnessBuiltin _<=_ {x} refl {y} refl x≤y≡⊤ = p≤q⇒p-q≤0 (≤ᵇ⇒≤ {x} {y} x≤y≡⊤)

soundness′ : ∀ {Γ ⟪Γ⟫ₛ ⟪Γ⟫ₗ} →
            relCtx Γ ⟪Γ⟫ₛ ⟪Γ⟫ₗ →
            ∀ (e : Expr n) → (Γ⊢e:τ : Γ ⊢ e ~ τ) →
            relType τ (⟦_⟧ₛ ⟪Γ⟫ₛ e Γ⊢e:τ) (⟦_⟧ₗ ⟪Γ⟫ₗ e Γ⊢e:τ)
soundness′ ⟪Γ⟫ₛ∼⟪Γ⟫ₗ (var v) tVar           = ⟪Γ⟫ₛ∼⟪Γ⟫ₗ v
soundness′ ⟪Γ⟫ₛ∼⟪Γ⟫ₗ (lam τ e) (tLam Γ⊢e:τ) = λ x~y → soundness′ (λ { zero → x~y; (suc i) → ⟪Γ⟫ₛ∼⟪Γ⟫ₗ i}) e Γ⊢e:τ
soundness′ ⟪Γ⟫ₛ∼⟪Γ⟫ₗ (app e₁ e₂) (tApp Γ⊢e₁:τ Γ⊢e₂:τ) = f g
  where
    f = soundness′ ⟪Γ⟫ₛ∼⟪Γ⟫ₗ e₁ Γ⊢e₁:τ
    g = soundness′ ⟪Γ⟫ₛ∼⟪Γ⟫ₗ e₂ Γ⊢e₂:τ
soundness′ ⟪Γ⟫ₛ∼⟪Γ⟫ₗ (builtin b) tBuiltin = soundnessBuiltin b

soundness : ∀ e → (ϕ⊢e:Bool : ϕ ⊢ e ~ Bool) →
            T (⟦_⟧ₛ ⟪ϕ⟫ᶜₛ e ϕ⊢e:Bool) →
            ⟦_⟧ₗ ⟪ϕ⟫ᶜₗ e ϕ⊢e:Bool ∈ ⟦⊤⟧ₗ
soundness = soundness′ λ()
