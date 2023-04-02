{-# OPTIONS --prop --rewriting #-}

module erased.section where

open import lib hiding (fst ; snd)
open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import hoas-postulated

module _ (F₀ : Fam₀) (DF₀ : DFam₀ F₀) where

  Morph₀ : Set _
  Morph₀ = Term (Pi (El (proj₁ F₀)) (proj₁ DF₀)) × Term (Pi (El (proj₂ F₀)) (proj₂ DF₀))

id-Morph₀ : (F₀ : Fam₀) → Morph₀ F₀ ((λ _ → El (proj₁ F₀)) , λ _ → El (proj₂ F₀))
id-Morph₀ _ = lam (λ a → a) , lam (λ a → a)

module _ {F₀ : Fam₀} {F₀ᴰ : DFam₀ F₀} where -- {m₀ : Morph₀ F₀ DF₀} where

  Ty₀-Sect : (A : Ty Γ Δ) (a : STerm (Ty₀-Alg A F₀)) → Morph₀ F₀ F₀ᴰ → Term (Ty₀-DAlg A a F₀ᴰ)
  Base₀-Sect : (B : Base Γ Δ) (a : STerm (Base₀-Alg B F₀)) → Morph₀ F₀ F₀ᴰ → Term (Base₀-DAlg B a F₀ᴰ)
  Params₀-Sect : (Δ : Params Γ) (p : STerm (Params₀-Alg Δ F₀)) → Morph₀ F₀ F₀ᴰ → Term (Params₀-DAlg Δ p F₀ᴰ)
  Ctor₀-Sect : (A : Ctor Γ) (a : STerm (Ctor₀-Alg A F₀)) → Term (Ctor₀-DAlg A a F₀ᴰ) → Morph₀ F₀ F₀ᴰ → Prop

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
  
  -- Ctor₀-Sect[] : ∀ C (w : Wk Ω Γ) → Ctor₀-Sect (C [ w ]c) ≡ Ctor₀-Sect C
  -- Ctor₀-Sect[] (ctor _ _) w = refl
  -- {-# REWRITE Ctor₀-Sect[] #-}

  Spec₀-Sect : (Γ : Spec) (γ : Spec₀-Alg Γ F₀) → Spec₀-DAlg Γ γ F₀ᴰ → Morph₀ F₀ F₀ᴰ → Prop
  Spec₀-Sect Γ γ δ m =
    ∀{C} (c : CtorTm Γ C) → Ctor₀-Sect C (CtorTm₀-Alg c γ) (CtorTm₀-DAlg c δ) m

module _ {F₀ : Fam₀} {F₀ᴰ : DFam₀ F₀} {m₀ : Morph₀ F₀ F₀ᴰ} where

  Wk₀-Sect : (w : Wk Ω Γ) {γ₀ : Spec₀-Alg Ω F₀} {γ₀ᴰ : Spec₀-DAlg Ω γ₀ F₀ᴰ}
           → Spec₀-Sect Ω γ₀ γ₀ᴰ m₀ → Spec₀-Sect Γ _ (Wk₀-DAlg w γ₀ᴰ) m₀
  Wk₀-Sect w s₀ c = s₀ (c [ w ]ctm)

  Sub₀-Sect : (σ : Sub {Γ} Δ ∇) {γ₀ : Spec₀-Alg Γ F₀} {γ₀ᴰ : Spec₀-DAlg Γ γ₀ F₀ᴰ}
              (s₀ : Spec₀-Sect Γ γ₀ γ₀ᴰ m₀) (p₀ : _)
            → Params₀-Sect ∇ (Sub₀-Alg σ γ₀ p₀) m₀ ≡ Sub₀-DAlg σ γ₀ᴰ (Params₀-Sect Δ p₀ m₀)

  Tm₀-Sect : (t : Tm Γ Δ A) {γ₀ : Spec₀-Alg Γ F₀} {γ₀ᴰ : Spec₀-DAlg Γ γ₀ F₀ᴰ}
             (s₀ : Spec₀-Sect Γ γ₀ γ₀ᴰ m₀) (p₀ : _)
           → Ty₀-Sect A (Tm₀-Alg t γ₀ p₀) m₀ ≡ Tm₀-DAlg t γ₀ᴰ (Params₀-Sect Δ p₀ m₀)

  Tm₀-Sect vz γ₀ᴰ p₀ = refl
  Tm₀-Sect vz1 γ₀ᴰ p₀ = refl
  Tm₀-Sect (vs t) γ₀ᴰ p₀ = Tm₀-Sect t γ₀ᴰ (fst p₀)
  Tm₀-Sect (ext A x) γ₀ᴰ p₀ = refl
  Tm₀-Sect (ctor c σ) {γ₀} {γ₀ᴰ} s₀ p₀ =
    trans (to-≡ (s₀ c (Sub₀-Alg σ _ p₀)))
          (cong (CtorTm₀-DAlg c γ₀ᴰ $ _ $_) (Sub₀-Sect σ s₀ p₀))
  Tm₀-Sect (ctor-1 c σ) {γ₀} {γ₀ᴰ} s₀ p₀ =
    trans (to-≡ (s₀ c (Sub₀-Alg σ _ p₀)))
          (cong (CtorTm₀-DAlg c γ₀ᴰ $ _ $_) (Sub₀-Sect σ s₀ p₀))
  Tm₀-Sect (App t) s₀ p₀ =
           cong (λ f → app f (snd p₀)) (Tm₀-Sect t s₀ (fst p₀))
  Tm₀-Sect (App-U t f) s₀ p₀ = cong (app f) (Tm₀-Sect t s₀ p₀)
  Tm₀-Sect (Lam t) s₀ p₀ = Pi-funext (λ a → Tm₀-Sect t s₀ (pair p₀ a))
  Tm₀-Sect (t [ σ ]tm) {γ₀} {γ₀ᴰ} s₀ p₀ =
    trans (Tm₀-Sect t s₀ (Sub₀-Alg σ _ p₀))
          (cong (Tm₀-DAlg t γ₀ᴰ) (Sub₀-Sect σ s₀ p₀))
  Tm₀-Sect (t [ w ]tm') {γ₀ᴰ = γ₀ᴰ} s₀ p₀ = Tm₀-Sect t (Wk₀-Sect w {γ₀ᴰ = γ₀ᴰ} s₀) p₀
  Tm₀-Sect (t [ w ]tm'-1) {γ₀ᴰ = γ₀ᴰ} s₀ p₀ = Tm₀-Sect t (Wk₀-Sect w {γ₀ᴰ = γ₀ᴰ} s₀) p₀

  Sub₀-Sect Sub.Id γ₀ᴰ p₀ = refl
  Sub₀-Sect (Ext σ x) s₀ p₀ = pair-≡ (Sub₀-Sect σ s₀ p₀) (Tm₀-Sect x s₀ p₀)
  Sub₀-Sect Drop γ₀ᴰ p₀ = refl
  Sub₀-Sect (σ ∘ τ) γ₀ᴰ p₀ =
    trans (Sub₀-Sect τ γ₀ᴰ (Sub₀-Alg σ _ p₀))
          (cong (Sub₀-DAlg τ _) (Sub₀-Sect σ γ₀ᴰ p₀))
  Sub₀-Sect (σ [ w ]ws) {γ₀ᴰ = γ₀ᴰ} s₀ p₀ = Sub₀-Sect σ (Wk₀-Sect w {γ₀ᴰ = γ₀ᴰ} s₀) p₀

module _ {F₀ : Fam₀} where

  is-initial₀ : ∀ {Γ} → Spec₀-Alg Γ F₀ → Set _
  is-initial₀ {Γ} γ₀ = {Y : DFam₀ F₀} (γd₀ : Spec₀-DAlg Γ γ₀ Y)
                     → Σp (Morph₀ F₀ Y) λ m → Spec₀-Sect Γ γ₀ γd₀ m
