{-# OPTIONS --prop --rewriting #-}

module erased.initial.embedded where

open import lib hiding (fst ; snd)
open import IIT.spec
open import IIT.algebra
open import erased.initial.algebra-small
open import erased.initial.section-small
open import erased.initial.internal-algebra
open import erased.initial.erasure
open import hoas-postulated as H

module Embedded (Γ₀ : Term Spec₀) where

  postulate
    Erased-A : SType
    Erased-B : SType

  Erased : Fam₀
  Erased = Erased-A , Erased-B

  postulate
    erased-A : ∀ Δ₀ → Term (CtorTm₀ Γ₀ (ctor₀ Δ₀ ty1₀))
                    → STerm (Params₀-Alg₀ Δ₀ Erased) → STerm Erased-A
    erased-B : ∀ Δ₀ → Term (CtorTm₀ Γ₀ (ctor₀ Δ₀ ty2₀))
                    → STerm (Params₀-Alg₀ Δ₀ Erased) → STerm Erased-B

    elim-A : (T : STerm Erased-A → Type)
           → (∀ Δ₀ c p → Term (T (erased-A Δ₀ c p)))
           → ∀ x → Term (T x)
    elim-B : (T : STerm Erased-B → Type)
           → (∀ Δ₀ c p → Term (T (erased-B Δ₀ c p)))
           → ∀ x → Term (T x)
    
    elim-A-≡ : (T : STerm Erased-A → Type)
             → (h : ∀ Δ₀ c p → Term (T (erased-A Δ₀ c p)))
             → ∀ {Δ₀ c p} → elim-A T h (erased-A Δ₀ c p) ≡ h Δ₀ c p
    elim-B-≡ : (T : STerm Erased-B → Type)
             → (h : ∀ Δ₀ c p → Term (T (erased-B Δ₀ c p)))
             → ∀ {Δ₀ c p} → elim-B T h (erased-B Δ₀ c p) ≡ h Δ₀ c p

  {-# REWRITE elim-A-≡ elim-B-≡ #-}

  E = Erased

  erased : ∀ Δ₀ B₀ → Term (CtorTm₀ Γ₀ (ctor₀ Δ₀ B₀))
         → STerm (Params₀-Alg₀ Δ₀ Erased)
         → STerm (Base₀-Alg₀ B₀ Erased)
  erased Δ₀ B₀ c p =
          let h = elim-Base₀ (λ B₀ → CtorTm₀ Γ₀ (ctor₀ Δ₀ B₀)
                            => (El (Params₀-Alg₀ Δ₀ Erased =>U Base₀-Alg₀ B₀ Erased)))
                    (lam λ c₀ → lam λ p₀ → erased-A Δ₀ c₀ p₀)
                    (lam λ c₀ → lam λ p₀ → erased-B Δ₀ c₀ p₀)
          in h B₀ $ c $ p

  int-alg' : Term (Spec₀-Alg₀' Γ₀ Erased)
  int-alg' = lam λ C₀ → lam λ c → lam (erased (fst C₀) (snd C₀) c)

  module RawMap (Y : _) (ωd : STerm (Spec₀-DAlg₀' Y Γ₀ $ int-alg')) where

    f1 : (e : STerm (proj₁ E)) → STerm (proj₁ Y e)
    f2 : (e : STerm (proj₂ E)) → STerm (proj₂ Y e)

    map-B : ∀ B₀ → STerm (PiU (Base₀-Alg₀ B₀ E) (app (Base₀-DAlg₀ Y B₀)))
    map-B = elim-Base₀ _ (lam f1) (lam f2)

    map-T : ∀ A₀ → STerm (PiU (Ty₀-Alg₀ A₀ E) (app (Ty₀-DAlg₀ Y A₀)))
    map-T = elim-Ty₀ _ (λ b → lam (λ a → map-B b $ a)) (λ A → lam (λ a → a))
              λ A B → lam (λ f → lam (λ a → map-B B $ app f a))

    map-P : ∀ Δ₀ → STerm (PiU (Params₀-Alg₀ Δ₀ E) (app (Params₀-DAlg₀ Y Δ₀)))
    map-P = elim-Params₀ _ (lam (λ a → star)) (λ Δ A h → lam (λ p → pair (h $ fst p) (map-T A $ snd p)))

    {-# TERMINATING #-} -- valid by mutual induction
    h : ∀ B₀ Δ₀ → (c : Term (CtorTm₀ Γ₀ (ctor₀ Δ₀ B₀)))
      → (p : STerm (Params₀-Alg₀ Δ₀ E))
      → STerm (Base₀-DAlg₀ Y B₀ $ erased Δ₀ B₀ c p)
    h B₀ Δ₀ c p = CtorTm₀-DAlg₀' {Erased} {Y} c $ int-alg' $ ωd $ p $ (map-P Δ₀ $ p)

    f1 = elim-A (λ x → El (proj₁ Y x)) (h ty1₀)
    f2 = elim-B (λ x → El (proj₂ Y x)) (h ty2₀)

    maps : Morph₀ Erased Y
    maps = lam f1 , lam f2

    map-B-≡ : ∀ (B : Base Ω Δ) (b₀ : STerm (Base₀-Alg B Erased))
            → Base₀-Sect {Erased} {Y} B b₀ maps ≡ (map-B (erase-Base B) $ b₀)
    map-B-≡ ty1 b₀ = refl
    map-B-≡ (ty2 x) b₀ = refl

    map-T-≡ : (A : Ty Γ Δ) (a₀ : STerm (Ty₀-Alg A Erased))
            → Ty₀-Sect {_} {Y} A a₀ maps ≡ (map-T (erase-Ty A) $ a₀)
    map-T-≡ (ext x) a₀ = refl
    map-T-≡ (base x) a₀ = map-B-≡ x a₀
    map-T-≡ (Π A B) f₀ = cong lam (funext (λ x → map-B-≡ B (app f₀ x)))
    map-T-≡ (A [ x ]) a₀ = map-T-≡ A a₀
    map-T-≡ (A [ w ]') a₀ = map-T-≡ A a₀

    map-P-≡ : (Δ : Params Γ) (p₀ : STerm (Params₀-Alg Δ Erased))
            → Params₀-Sect {_} {Y} Δ p₀ maps ≡ (map-P (erase-Params Δ) $ p₀)
    map-P-≡ ● p₀ = refl
    map-P-≡ (Δ ‣‣ A) p₀ =
      cong (uncurry pair)
        (×-≡ (map-P-≡ Δ (fst p₀)) (map-T-≡ A (snd p₀)))
    map-P-≡ (Δ [ x ]p) p₀ = map-P-≡ Δ p₀

module Inductive (Ω : Spec) where

  Ω₀ = erase-Spec Ω
  open Embedded Ω₀

  erased-alg : Spec₀-Alg' Ω Erased
  erased-alg = ext-Spec-Alg' Ω int-alg'

  module _ (Y : _) (ωd : Spec₀-DAlg' Ω erased-alg Y) where

    int-dalg : STerm (Spec₀-DAlg₀' Y Ω₀ $ int-alg')
    int-dalg = ext-Spec₀-DAlg {Erased} {Y} Ω int-alg' ωd

    open RawMap Y int-dalg

    is-sect : Spec₀-Sect' {Erased} {Y} Ω erased-alg ωd maps
    is-sect {ctor Δ ty1} c p = from-≡ (trans
         (cong (λ f → f $ p $ (map-P (erase-Params Δ) $ p))
          (ext-CtorTm-DAlg {D = Y} int-alg' ωd c))
         (cong (app (ωd c $ p)) (sym (map-P-≡ Δ p))))
    is-sect {ctor Δ (ty2 x)} c p = from-≡ (trans
         (cong (λ f → f $ p $ (map-P (erase-Params Δ) $ p))
          (ext-CtorTm-DAlg {D = Y} int-alg' ωd c))
         (cong (app (ωd c $ p)) (sym (map-P-≡ Δ p))))

  is-init' : is-initial₀' erased-alg
  is-init' γd₀ = _ ,p is-sect _ γd₀

  is-init : is-initial₀ (to-Spec₀-Alg erased-alg)
  is-init = to-initial₀ Ω erased-alg is-init'
