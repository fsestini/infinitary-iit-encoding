{-# OPTIONS --prop --rewriting #-}

module erased.initial.section-small where

open import lib hiding (fst ; snd)
open import IIT.spec
open import IIT.algebra
open import erased.initial.algebra-small
open import hoas-postulated

module _ (F₀ : Fam₀) (DF₀ : DFam₀ F₀) where

  Morph₀ : Set _
  Morph₀ = STerm (PiU (proj₁ F₀) (proj₁ DF₀)) × STerm (PiU (proj₂ F₀) (proj₂ DF₀))

id-Morph₀ : (F₀ : Fam₀) → Morph₀ F₀ ((λ _ → proj₁ F₀) , λ _ → proj₂ F₀)
id-Morph₀ _ = lam (λ a → a) , lam (λ a → a)

module _ {F₀ : Fam₀} {F₀ᴰ : DFam₀ F₀} where -- {m₀ : Morph₀ F₀ DF₀} where

  Ty₀-Sect : (A : Ty Γ Δ) (a : STerm (Ty₀-Alg A F₀)) → Morph₀ F₀ F₀ᴰ → STerm (Ty₀-DAlg A a F₀ᴰ)
  Base₀-Sect : (B : Base Γ Δ) (a : STerm (Base₀-Alg B F₀)) → Morph₀ F₀ F₀ᴰ → STerm (Base₀-DAlg B a F₀ᴰ)
  Params₀-Sect : (Δ : Params Γ) (p : STerm (Params₀-Alg Δ F₀)) → Morph₀ F₀ F₀ᴰ → STerm (Params₀-DAlg Δ p F₀ᴰ)
  Ctor₀-Sect : (A : Ctor Γ) (a : STerm (Ctor₀-Alg A F₀)) → STerm (Ctor₀-DAlg A a F₀ᴰ) → Morph₀ F₀ F₀ᴰ → Prop

  Ty₀-Sect (ext A) a _ = a
  Ty₀-Sect (base B) = Base₀-Sect B
  Ty₀-Sect (Π A B) f x = lam (λ n → Base₀-Sect B (app f n) x)
  Ty₀-Sect (A [ _ ]) = Ty₀-Sect A
  Ty₀-Sect (A [ _ ]') = Ty₀-Sect A

  Base₀-Sect ty1 a m₀ = app (proj₁ m₀) a
  Base₀-Sect (ty2 _) a m₀ = app (proj₂ m₀) a
  
  Base₀-Sect[]b'
    : (A : Base Γ Δ) (w : Wk Ω Γ) (a : STerm (Base₀-Alg A F₀))
    → Base₀-Sect (A [ w ]b') a ≡ Base₀-Sect A a
  Base₀-Sect[]b' ty1 w a = refl
  Base₀-Sect[]b' (ty2 x) w a = refl
  {-# REWRITE Base₀-Sect[]b' #-}

  Params₀-Sect ● p _ = star
  Params₀-Sect (Δ ‣‣ A) p m = pair (Params₀-Sect Δ (fst p) m) (Ty₀-Sect A (snd p) m)
  Params₀-Sect (Δ [ x ]p) = Params₀-Sect Δ
   
  Ctor₀-Sect (ctor Δ A) c c' m =
    (p : _) → Base₀-Sect A (app c p) m ≡p (c' $ _ $ Params₀-Sect Δ p m)
  
  Spec₀-Sect : (Γ : Spec) (γ : Spec₀-Alg Γ F₀) → Spec₀-DAlg Γ γ F₀ᴰ → Morph₀ F₀ F₀ᴰ → Prop
  Spec₀-Sect Γ γ δ m =
    ∀{C} (c : CtorTm Γ C) → Ctor₀-Sect C (CtorTm₀-Alg c γ)
      (CtorTm₀-DAlg c {γ} δ) m

  Spec₀-Sect' : (Γ : Spec) (γ : Spec₀-Alg' Γ F₀)
              → Spec₀-DAlg' Γ γ F₀ᴰ → Morph₀ F₀ F₀ᴰ → Prop
  Spec₀-Sect' Γ γ γd m =
    ∀{C} (c : CtorTm Γ C) → Ctor₀-Sect C (γ c) (γd c) m

  to-Spec₀-Sect'
    : ∀{f} (Γ : Spec)
      (γ₀ : Spec₀-Alg' Γ F₀) (γd₀  : Spec₀-DAlg Γ (to-Spec₀-Alg γ₀) F₀ᴰ)
    → Spec₀-Sect' Γ γ₀ (to-Spec₀-DAlg' Γ γ₀ γd₀) f
    → Spec₀-Sect Γ (to-Spec₀-Alg γ₀) γd₀ f
  to-Spec₀-Sect' _ γ₀ γd₀ s {ctor Δ B} c p = s c p

  Spec₀-Sect-ind : (Γ : Spec) (γ : Spec₀-Alg Γ F₀)
              → Spec₀-DAlg-ind Γ γ F₀ᴰ → Morph₀ F₀ F₀ᴰ → Prop
  Spec₀-Sect-ind init γ γd m = ⊤p
  Spec₀-Sect-ind (Γ ‣ C) (γ , c) (γd , cd) m =
    Spec₀-Sect-ind Γ γ γd m ×p Ctor₀-Sect C c cd m

module _ {F₀ : Fam₀} where

  is-initial₀ : ∀ {Γ} → Spec₀-Alg Γ F₀ → Set _
  is-initial₀ {Γ} γ₀ = {Y : DFam₀ F₀} (γd₀ : Spec₀-DAlg Γ γ₀ Y)
                     → Σp (Morph₀ F₀ Y) λ m → Spec₀-Sect Γ γ₀ γd₀ m

  is-initial₀' : ∀ {Γ} → Spec₀-Alg' Γ F₀ → Set _
  is-initial₀' {Γ} γ₀ = {Y : DFam₀ F₀} (γd₀ : Spec₀-DAlg' Γ γ₀ Y)
                     → Σp (Morph₀ F₀ Y) λ m → Spec₀-Sect' Γ γ₀ γd₀ m

  to-initial₀ : ∀ Γ (γ₀ : Spec₀-Alg' Γ F₀)
              → is-initial₀' γ₀ → is-initial₀ (to-Spec₀-Alg γ₀)
  to-initial₀ Γ γ₀ intl γd₀ = lib.fst aux ,p to-Spec₀-Sect' Γ γ₀ γd₀ (lib.snd aux)
    where aux = intl (to-Spec₀-DAlg' Γ γ₀ γd₀)
