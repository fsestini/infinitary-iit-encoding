{-# OPTIONS --prop --rewriting #-}

module relation.inversions where

open import lib
open import IIT.spec
open import erased.algebra
open import predicate.algebra
open import IIT.algebra
open import relation.algebra
open import sigma-construction

record HasRelationInversions
  (Ω : Spec) {F₀} {ω₀ : Spec₀-Alg Ω F₀}
             {F₁} (ω₁ : Spec₁-Alg Ω ω₀ F₁)
             {Y : _} {ωd : Spec-DAlg Ω (Σ-Spec Ω ω₁) Y}
             (R : _) (ωr : Spec-R-Alg _ ωd R)
  : Set where

  private
    σ-alg = Σ-Spec Ω ω₁

  field
    param-inv : (c : CtorTm Ω (ctor Δ ty1)) (p : _) (aᴰ : _)
                     → proj₁ R (CtorTm-Alg c σ-alg p) aᴰ
                     → Σ (Params-DAlg Δ σ-alg ωd p) λ pd → Params-R-Alg Δ pd R
  
    param-inv-≡
      : (c : CtorTm Ω (ctor Δ ty1)) (p : _)
        (pd : Params-DAlg Δ _ ωd p) (pr : Params-R-Alg Δ pd R)
      → param-inv c p (CtorTm-DAlg c ωd pd) (CtorTm-R-Alg c ωr pr)
      ≡ (pd , pr)
  
    ix-inv : (c : CtorTm Ω (ctor Δ ty1)) (p : _) (aᴰ : _)
                  → (r : proj₁ R (CtorTm-Alg c σ-alg p) aᴰ)
                  → aᴰ ≡ CtorTm-DAlg c ωd (proj₁ (param-inv c p aᴰ r))

