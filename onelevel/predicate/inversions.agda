{-# OPTIONS --prop --rewriting #-}

module predicate.inversions where

open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import erased.section
open import predicate.algebra
open import lib

record HasPredicateInversions (Ω : Spec) {F₀} (F₁ : BasePreds F₀) (ω₀ : Spec₀-Alg Ω F₀) : Set where
  field
    pred-inv : (c : CtorTm Ω (ctor Δ B)) (p₀ : _)
             → Base₁-Alg B ω₀ p₀ (CtorTm₀-Alg c ω₀ p₀) F₁
             → Params₁-Alg Δ ω₀ p₀ F₁
    pred-ix-inv : ∀{t} (c : CtorTm Ω (ctor Δ (ty2 t))) (p₀ : _) (a₀ : _)
                → proj₂ F₁ a₀ (CtorTm₀-Alg c ω₀ p₀)
                → a₀ ≡p Tm₀-Alg t ω₀ p₀
