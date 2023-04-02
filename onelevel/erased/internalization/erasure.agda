{-# OPTIONS --prop --rewriting #-}

module erased.internalization.erasure where

open import lib
open import IIT.spec
open import erased.internalization.code
open import erased.internalization.algebra
open import erased.internalization.initial

erase-Base : Base Γ Δ → Base₀
erase-Base ty1 = ty1₀
erase-Base (ty2 x) = ty2₀

erase-Ty : Ty Γ Δ → Ty₀
erase-Ty (ext X) = ext₀ X
erase-Ty (base x) = base₀ (erase-Base x)
erase-Ty (Π A x) = Π₀ A (erase-Base x)
erase-Ty (A [ x ]) = erase-Ty A
erase-Ty (A [ w ]') = erase-Ty A

erase-Params : Params Γ → Params₀
erase-Params ● = ●₀
erase-Params (Δ ‣‣ x) = erase-Params Δ ‣‣₀ erase-Ty x
erase-Params (Δ [ x ]p) = erase-Params Δ

erase-Ctor : Ctor Γ → Ctor₀
erase-Ctor (ctor Δ B) = erase-Params Δ , erase-Base B

erase-Spec : Spec → Spec₀
erase-Spec init = ◆₀
erase-Spec (Γ ‣ C) = erase-Spec Γ ‣₀ erase-Ctor C

erase-Base-[]' : (B : Base Γ Δ) (w : Wk Ω Γ) → erase-Base (B [ w ]b') ≡ erase-Base B
erase-Base-[]' ty1 w = refl
erase-Base-[]' (ty2 x) w = refl
{-# REWRITE erase-Base-[]' #-}

erase-Ctor-[] : ∀ C (w : Wk Ω Γ) → erase-Ctor (C [ w ]c) ≡ erase-Ctor C
erase-Ctor-[] (ctor Δ x) w = refl
{-# REWRITE erase-Ctor-[] #-}

erase-CtorTm : CtorTm Γ C → CtorTm₀ (erase-Spec Γ) (erase-Ctor C)
erase-Wk : ∀{A} → Wk Ω Γ → CtorTm₀ (erase-Spec Γ) A → CtorTm₀ (erase-Spec Ω) A

erase-Wk Id x = x
erase-Wk Drop x = vs₀ x
erase-Wk (w ∘w w') x = erase-Wk w (erase-Wk w' x)

erase-CtorTm v0c = vz₀
erase-CtorTm (dropc c) = vs₀ (erase-CtorTm c)
erase-CtorTm (c [ w ]ctm) = erase-Wk w (erase-CtorTm c)

----------

open import erased.algebra
open import erased.section

Base₀-≡ : (A : Base Γ Δ) (w : Wk Ω Γ)
        → Base₀-Alg A s ≡ Base₀-Alg₀ (erase-Base A) s
Base₀-≡ ty1 w = refl
Base₀-≡ (ty2 x) w = refl
{-# REWRITE Base₀-≡ #-}

Ty₀-≡ : (A : Ty Γ Δ) (w : Wk Ω Γ)
      → Ty₀-Alg A s ≡ Ty₀-Alg₀ (erase-Ty A) s
Ty₀-≡ (ext x) w = refl
Ty₀-≡ (base x) w = refl
Ty₀-≡ (Π A x) w = refl
Ty₀-≡ (A [ x ]) w = Ty₀-≡ A w
Ty₀-≡ (A [ w' ]') w = Ty₀-≡ A (w ∘w w')
{-# REWRITE Ty₀-≡ #-}

Params₀-≡ : (Δ : Params Γ) (w : Wk Ω Γ)
          → Params₀-Alg Δ s ≡ Params₀-Alg₀ (erase-Params Δ) s
Params₀-≡ ● w = refl
Params₀-≡ {s = s} (Δ ‣‣ A) w rewrite Params₀-≡ {s = s} Δ w = refl
Params₀-≡ (Δ [ x ]p) w = Params₀-≡ Δ (w ∘w x)
{-# REWRITE Params₀-≡ #-}

--------------------------------------------------------------------------------

to-Spec₀-Alg₀ : ∀ Γ → Spec₀-Alg Γ s → Spec₀-Alg₀ (erase-Spec Γ) s
to-Spec₀-Alg₀ Γ γ c = {!!}

to-Spec₀-DAlg₀ : ∀ Γ (γ₀ : Spec₀-Alg Γ s) → Spec₀-DAlg Γ γ₀ ds
              → Spec₀-DAlg₀ (erase-Spec Γ) (to-Spec₀-Alg₀ Γ γ₀) ds

--------------------------------------------------------------------------------

module _ (Ω : Spec) where

  private
    Init-Ω = Init₀ (erase-Spec Ω)
  
  Init-is-alg : Spec₀-Alg Ω Init-Ω
  Init-is-alg {ctor Δ ty1} c p = init₀-1 (erase-CtorTm c) p
  Init-is-alg {ctor Δ (ty2 x)} c p = init₀-2 (erase-CtorTm c) p

  module _ {Y} (δ : Spec₀-DAlg Ω Init-is-alg Y) where

    open Elim₀ (erase-Spec Ω) {Y} {!!}


