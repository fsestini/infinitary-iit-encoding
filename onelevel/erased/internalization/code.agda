{-# OPTIONS --prop --rewriting #-}

module erased.internalization.code where

open import lib
open import IIT.spec using (U)

data Base₀ : Set where
  ty1₀ : Base₀
  ty2₀ : Base₀

data Ty₀ : Set where
  base₀ : Base₀ → Ty₀
  Π₀ : U → Base₀ → Ty₀
  ext₀ : U → Ty₀

data Params₀ : Set where
  ●₀ : Params₀
  _‣‣₀_ : Params₀ → Ty₀ → Params₀

Ctor₀ = Params₀ × Base₀

data Spec₀ : Set where
  ◆₀ : Spec₀
  _‣₀_ : Spec₀ → Ctor₀ → Spec₀

data CtorTm₀ : Spec₀ → Ctor₀ → Set where
  vz₀ : ∀{Γ C} → CtorTm₀ (Γ ‣₀ C) C
  vs₀ : ∀{Γ C C'} → CtorTm₀ Γ C → CtorTm₀ (Γ ‣₀ C') C

data Wk₀ : Spec₀ → Spec₀ → Set where
  Id₀ : ∀{Γ} → Wk₀ Γ Γ
  Drop₀ : ∀{Γ C} → Wk₀ (Γ ‣₀ C) Γ
  _∘w₀_ : ∀{Γ₀ Ω₀ θ₀} → Wk₀ Γ₀ Ω₀ → Wk₀ Ω₀ θ₀ → Wk₀ Γ₀ θ₀
