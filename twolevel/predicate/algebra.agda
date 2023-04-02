{-# OPTIONS --prop --rewriting #-}

module predicate.algebra where

open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import lib hiding (fst ; snd) renaming (fstP to lib-fstP ; sndP to lib-sndP)
open import hoas-postulated

Fam₁ : Fam₀ → Set
Fam₁ (A₀ , B₀) = (STerm A₀ → Term P) × (STerm A₀ → STerm B₀ → Term P)

module _ {F₀ : Fam₀} where -- {F₁ : Fam₁ F₀} where

  Spec₁-Alg : (Γ : Spec) → Spec₀-Alg Γ F₀ → Fam₁ F₀ → Prop
  Ctor₁-Alg : (A : Ctor Γ) → Spec₀-Alg Γ F₀ → STerm (Ctor₀-Alg A F₀) → Fam₁ F₀ → Term P
  Ty₁-Alg : (A : Ty Γ Δ) → Spec₀-Alg Γ F₀ → STerm (Params₀-Alg Δ F₀) → STerm (Ty₀-Alg A F₀) → Fam₁ F₀ → Term P
  Base₁-Alg : (A : Base Γ Δ) → Spec₀-Alg Γ F₀ → STerm (Params₀-Alg Δ F₀) → STerm (Base₀-Alg A F₀) → Fam₁ F₀ → Term P
  Params₁-Alg : (Δ : Params Γ) → Spec₀-Alg Γ F₀ → STerm (Params₀-Alg Δ F₀) → Fam₁ F₀ → Term P

  Spec₁-Alg init x _ = ⊤p
  Spec₁-Alg (Γ ‣ A) (γ , a) x = ΣP (Spec₁-Alg Γ γ x) λ _ → PTerm (Ctor₁-Alg A γ a x)

  Ctor₁-Alg (ctor Δ B) γ₀ c₀ x =
    Pip (Params₀-Alg Δ F₀) (λ p₀ → Params₁-Alg Δ γ₀ p₀ x =>P Base₁-Alg B γ₀ p₀ (app c₀ p₀) x)
  
  Params₁-Alg ● γ ps _ = Top
  Params₁-Alg (Δ ‣‣ A) γ ps x =
    SigmaP (Params₁-Alg Δ γ (fst ps) x) λ _ → Ty₁-Alg A γ (fst ps) (snd ps) x
  Params₁-Alg (Δ [ x ]p) γ = Params₁-Alg Δ (Wk₀-Alg x γ)
  
  Ty₁-Alg (ext A) _ _ _ _ = Top
  Ty₁-Alg (base b)= Base₁-Alg b
  Ty₁-Alg (Π A B) γ p f F₁ = Pip A (λ x → Base₁-Alg B γ (pair p x) (app f x) F₁)
  Ty₁-Alg (A [ σ ]) γ p = Ty₁-Alg A γ (Sub₀-Alg σ γ p)
  Ty₁-Alg (A [ w ]') γ = Ty₁-Alg A (Wk₀-Alg w γ)
  
  Base₁-Alg ty1 γ p a F₁ = proj₁ F₁ a
  Base₁-Alg (ty2 t) γ p a F₁ = proj₂ F₁ (Tm₀-Alg t γ p) a
  
  Base₁-Alg[]b'
    : (A : Base Γ Δ) (w : Wk Ω Γ) {γ : Spec₀-Alg Ω F₀}
    → Base₁-Alg (A [ w ]b') γ ≡ Base₁-Alg A (Wk₀-Alg w γ)
  Base₁-Alg[]b' ty1 w = refl
  Base₁-Alg[]b' (ty2 x) w = refl
  {-# REWRITE Base₁-Alg[]b' #-}
  
module _ {F₀ : Fam₀} {F₁ : Fam₁ F₀} where

  Sub₁-Alg : (σ : Sub {Γ} Δ ∇) {γ₀ : Spec₀-Alg Γ F₀} (δ : Spec₁-Alg Γ γ₀ F₁) {ps : _}
           → PTerm (Params₁-Alg Δ γ₀ ps F₁)
           → PTerm (Params₁-Alg ∇ γ₀ (Sub₀-Alg σ γ₀ ps) F₁)
  Wk₁-Alg : (w : Wk Ω Γ) {γ₀ : Spec₀-Alg Ω F₀} → Spec₁-Alg Ω γ₀ F₁ → Spec₁-Alg Γ (Wk₀-Alg w γ₀) F₁
  Tm₁-Alg : (t : Tm Γ Δ A) {γ₀ : Spec₀-Alg Γ F₀} (δ : Spec₁-Alg Γ γ₀ F₁)
            {ps : _} (ps' : PTerm (Params₁-Alg Δ γ₀ ps F₁))
          → PTerm (Ty₁-Alg A γ₀ ps (Tm₀-Alg t γ₀ ps) F₁)
  CtorTm₁-Alg : (c : CtorTm Γ C) {γ₀ : Spec₀-Alg Γ F₀} (δ : Spec₁-Alg Γ γ₀ F₁)
              → PTerm (Ctor₁-Alg C γ₀ (CtorTm₀-Alg c γ₀) F₁)
  
  Sub₁-Alg Id δ x = x
  Sub₁-Alg (Ext σ t) δ x = pairP (Sub₁-Alg σ δ x) (Tm₁-Alg t δ x)
  Sub₁-Alg Drop δ x = fstP x
  Sub₁-Alg (σ ∘ τ) δ x = Sub₁-Alg τ δ (Sub₁-Alg σ δ x)
  Sub₁-Alg (σ [ w ]ws) δ x = Sub₁-Alg σ (Wk₁-Alg w δ) x
  
  Wk₁-Alg Id x = x
  Wk₁-Alg Drop x = lib-fstP x
  Wk₁-Alg (w ∘w w') x = Wk₁-Alg w' (Wk₁-Alg w x)
  
  Tm₁-Alg vz δ p = sndP p
  Tm₁-Alg vz1 δ p = sndP p
  Tm₁-Alg (vs t) δ p = Tm₁-Alg t δ (fstP p)
  Tm₁-Alg (ext A x) δ p = truth
  Tm₁-Alg (ctor x σ) δ p = CtorTm₁-Alg x δ $p _ $P Sub₁-Alg σ δ p
  Tm₁-Alg (ctor-1 x σ) δ p = CtorTm₁-Alg x δ $p _ $P Sub₁-Alg σ δ p
  Tm₁-Alg (App t) γ₁ {ps} p = Tm₁-Alg t γ₁ (fstP p) $p snd ps
  Tm₁-Alg (Lam t) δ p = lamp λ x → Tm₁-Alg t δ (pairP p truth)
  Tm₁-Alg (t [ σ ]tm) δ p = Tm₁-Alg t δ (Sub₁-Alg σ δ p)
  Tm₁-Alg (t [ w ]tm') δ p = Tm₁-Alg t (Wk₁-Alg w δ) p
  Tm₁-Alg (t [ w ]tm'-1) δ p = Tm₁-Alg t (Wk₁-Alg w δ) p
  Tm₁-Alg (App-U t x) δ p = truth
  
  -- Ctor₁-Alg[]c
  --   : (C : Ctor Γ) (w : Wk Ω Γ) (γ₀ : Spec₀-Alg Ω F₀)
  --   → Ctor₁-Alg (C [ w ]c) γ₀ ≡ Ctor₁-Alg C (Wk₀-Alg w γ₀)
  -- Ctor₁-Alg[]c (ctor Δ x) w _ = refl
  -- {-# REWRITE Ctor₁-Alg[]c #-}
  
  CtorTm₁-Alg v0c δ = lib-sndP δ
  CtorTm₁-Alg (dropc c) δ = CtorTm₁-Alg c (lib-fstP δ)
  CtorTm₁-Alg (_[_]ctm c w) δ = CtorTm₁-Alg c (Wk₁-Alg w δ)

  CtorTm₁-Alg'
    : ∀{Δ X} (c : CtorTm Γ (ctor Δ X))
      {γ₀ : Spec₀-Alg Γ F₀} (δ : Spec₁-Alg Γ γ₀ F₁)
    → {p₀ : _} → PTerm (Params₁-Alg Δ γ₀ p₀ F₁) → _
  CtorTm₁-Alg' c γ₁ p₁ = CtorTm₁-Alg c γ₁ $p _ $P p₁

module _ {F₀ : _} where

  Spec₁-Alg' : (Γ : Spec) → Spec₀-Alg Γ F₀ → Fam₁ F₀ → Prop
  Spec₁-Alg' Γ γ₀ F₁ = ∀{C} (c : CtorTm Γ C) → PTerm (Ctor₁-Alg C γ₀ (CtorTm₀-Alg c γ₀) F₁)

  to-Spec₁-Alg : ∀{F₁} (Γ : Spec) {γ₀ : _} → Spec₁-Alg' Γ γ₀ F₁ → Spec₁-Alg Γ γ₀ F₁
  to-Spec₁-Alg init γ₁ = ttp
  to-Spec₁-Alg (Γ ‣ C) γ₁ =
    to-Spec₁-Alg Γ (λ c → γ₁ (c [ Drop ]ctm)) ,P γ₁ v0c
