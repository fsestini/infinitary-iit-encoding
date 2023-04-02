{-# OPTIONS --prop --rewriting #-}

module erased.internalization.initial where

open import lib
open import IIT.spec
open import erased.internalization.code
open import erased.internalization.algebra

data Init₀-1 (Γ : Spec₀) : Set
data Init₀-2 (Γ : Spec₀) : Set

Init₀ : Spec₀ → Set × Set
Init₀ Γ = Init₀-1 Γ , Init₀-2 Γ

data Init₀-1 Γ where
  init₀-1 : ∀{Δ} → CtorTm₀ Γ (Δ , ty1₀) → Params₀-Alg₀ Δ (Init₀ Γ) → Init₀-1 Γ

data Init₀-2 Γ where
  init₀-2 : ∀{Δ} → CtorTm₀ Γ (Δ , ty2₀) → Params₀-Alg₀ Δ (Init₀ Γ) → Init₀-2 Γ

module _ (Ω : Spec₀) where

  private
    Init-Ω = Init₀ Ω

  Init-is-alg₀ : Spec₀-Alg₀ Ω Init-Ω
  Init-is-alg₀ {Δ , ty1₀} c p = init₀-1 c p
  Init-is-alg₀ {Δ , ty2₀} c p = init₀-2 c p

  module Elim₀ {Y} (δ : Spec₀-DAlg₀ Ω Init-is-alg₀ Y) where

    elim-1 : (x : _) → proj₁ Y x
    elim-2 : (x : _) → proj₂ Y x
    elims : ∀ Δ (p : Params₀-Alg₀ Δ Init-Ω) → Params₀-DAlg₀ Δ Y p
    elim-ty : ∀ A (a : Ty₀-Alg₀ A Init-Ω) → Ty₀-DAlg₀ A Y a
    elim-base : ∀ A (a : Base₀-Alg₀ A Init-Ω) → Base₀-DAlg₀ A Y a

    elim-1 (init₀-1 c p) = δ c (elims _ p)
    elim-2 (init₀-2 c p) = δ c (elims _ p)

    elims ●₀ p = tt
    elims (Δ ‣‣₀ A) (p , a) = elims Δ p , elim-ty A a
    
    elim-ty (base₀ x) a = elim-base x a
    elim-ty (Π₀ x y) a = λ n → elim-base y (a n)
    elim-ty (ext₀ x) a = a

    elim-base ty1₀ a = elim-1 a
    elim-base ty2₀ a = elim-2 a
