{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

module erased.algebra where

open import lib hiding (fst ; snd)
open import IIT.spec
open import IIT.algebra
open import hoas-postulated

Fam₀ : Set
Fam₀ = SType × SType

DFam₀ : Fam₀ → Set
DFam₀ (A , B) = (STerm A -> Type) × (STerm B -> Type)

Spec₀-Alg : Spec → Fam₀ → Set
Ctor₀-Alg : Ctor Γ → Fam₀ → SType
Params₀-Alg : Params Γ → Fam₀ → SType
Ty₀-Alg : Ty Γ Δ → Fam₀ → SType
Base₀-Alg : Base Γ Δ → Fam₀ → SType

Spec₀-Alg init _ = ⊤
Spec₀-Alg (Γ ‣ A) F₀ = Spec₀-Alg Γ F₀ × STerm (Ctor₀-Alg A F₀)
  
Ctor₀-Alg (ctor Δ A) F₀ = Params₀-Alg Δ F₀ =>U Base₀-Alg A F₀

Params₀-Alg ● _ = 𝟙U
Params₀-Alg (Δ ‣‣ A) F₀ = PairU (Params₀-Alg Δ F₀) (Ty₀-Alg A F₀)
Params₀-Alg (Δ [ x ]p) F₀ = Params₀-Alg Δ F₀

Ty₀-Alg (ext A) _ = A
Ty₀-Alg (base b) = Base₀-Alg b
Ty₀-Alg (Π A B) F₀ = A =>U Base₀-Alg B F₀
Ty₀-Alg (A [ _ ]) = Ty₀-Alg A
Ty₀-Alg (A [ _ ]') = Ty₀-Alg A

Base₀-Alg ty1 F₀ = proj₁ F₀
Base₀-Alg (ty2 _) F₀ = proj₂ F₀

Base₀-Alg[]b' : (A : Base Γ Δ) (w : Wk Ω Γ) → Base₀-Alg (A [ w ]b') ≡ Base₀-Alg A
Base₀-Alg[]b' ty1 w = refl
Base₀-Alg[]b' (ty2 x) w = refl
{-# REWRITE Base₀-Alg[]b' #-}

module _ {F₀} where

  Tm₀-Alg : Tm Γ Δ A → Spec₀-Alg Γ F₀ → STerm (Params₀-Alg Δ F₀) → STerm (Ty₀-Alg A F₀)
  CtorTm₀-Alg : CtorTm Γ C → Spec₀-Alg Γ F₀ → STerm (Ctor₀-Alg C F₀)
  Wk₀-Alg : Wk Γ Ω → Spec₀-Alg Γ F₀ → Spec₀-Alg Ω F₀
  Sub₀-Alg : Sub {Γ} Δ ∇ → Spec₀-Alg Γ F₀ → STerm (Params₀-Alg Δ F₀) → STerm (Params₀-Alg ∇ F₀)
  
  Sub₀-Alg Id _ ps = ps
  Sub₀-Alg (Ext σ t) x ps = pair (Sub₀-Alg σ x ps) (Tm₀-Alg t x ps)
  Sub₀-Alg Drop x ps = fst ps
  Sub₀-Alg (σ ∘ τ) x ps = Sub₀-Alg τ x (Sub₀-Alg σ x ps)
  Sub₀-Alg (σ [ w ]ws) x ps = Sub₀-Alg σ (Wk₀-Alg w x) ps
  
  Wk₀-Alg Id x = x
  Wk₀-Alg Drop x = proj₁ x
  Wk₀-Alg (w ∘w w₁) x = Wk₀-Alg w₁ (Wk₀-Alg w x)
  
  Tm₀-Alg vz γ p = snd p
  Tm₀-Alg vz1 γ p = snd p
  Tm₀-Alg (vs t) γ p = Tm₀-Alg t γ (fst p)
  Tm₀-Alg (ext A x) γ p = x
  Tm₀-Alg (ctor x σ) γ p = app (CtorTm₀-Alg x γ) (Sub₀-Alg σ γ p)
  Tm₀-Alg (ctor-1 x σ) γ p = app (CtorTm₀-Alg x γ) (Sub₀-Alg σ γ p)
  Tm₀-Alg (App t) γ p = app (Tm₀-Alg t γ (fst p)) (snd p)
  Tm₀-Alg (Lam t) γ p = lam λ n → Tm₀-Alg t γ (pair p n)
  Tm₀-Alg (t [ σ ]tm) γ p = Tm₀-Alg t γ (Sub₀-Alg σ γ p)
  Tm₀-Alg (t [ w ]tm') γ p = Tm₀-Alg t (Wk₀-Alg w γ) p
  Tm₀-Alg (t [ w ]tm'-1) γ p = Tm₀-Alg t (Wk₀-Alg w γ) p
  Tm₀-Alg (App-U t f) γ p = app f (Tm₀-Alg t γ p)
  
  -- Ctor₀-Alg[]c : (C : Ctor Γ) (w : Wk Ω Γ) → Ctor₀-Alg (C [ w ]c) ≡ Ctor₀-Alg C
  -- Ctor₀-Alg[]c (ctor Δ x) w = refl
--  {-# REWRITE Ctor₀-Alg[]c #-}
  
  CtorTm₀-Alg v0c x = proj₂ x
  CtorTm₀-Alg (dropc c) x = CtorTm₀-Alg c (proj₁ x)
  CtorTm₀-Alg (_[_]ctm c w) x = CtorTm₀-Alg c (Wk₀-Alg w x)
  
Spec₀-Alg' : Spec → Fam₀ → Set
Spec₀-Alg' Γ F = ∀{C} → CtorTm Γ C → STerm (Ctor₀-Alg C F)

to-Spec₀-Alg : ∀ {Γ F} → Spec₀-Alg' Γ F → Spec₀-Alg Γ F
to-Spec₀-Alg {init} γ = tt
to-Spec₀-Alg {Γ ‣ x} γ = (to-Spec₀-Alg {Γ} (λ c → γ (c [ Drop ]ctm))) , γ v0c



module _ {F₀} where

  Spec₀-DAlg : ∀ Γ (γ : Spec₀-Alg Γ F₀) → DFam₀ F₀ → Set
  Ctor₀-DAlg : (A : Ctor Γ) -> STerm (Ctor₀-Alg A F₀) -> DFam₀ F₀ → Type
  Ty₀-DAlg : (A : Ty Γ Δ) → STerm (Ty₀-Alg A F₀) -> DFam₀ F₀ → Type
  Base₀-DAlg : (A : Base Γ Δ) → STerm (Base₀-Alg A F₀) -> DFam₀ F₀ → Type
  Params₀-DAlg : (Δ : Params Γ) → STerm (Params₀-Alg Δ F₀) -> DFam₀ F₀ → Type

  Spec₀-DAlg Γ γ F₀ᴰ =
    (∀{A} (c : CtorTm Γ A) → Term (Ctor₀-DAlg A (CtorTm₀-Alg c γ) F₀ᴰ))
  
  Ctor₀-DAlg (ctor Δ A) f F₀ᴰ =
    Pi _ λ p → Params₀-DAlg Δ p F₀ᴰ => Base₀-DAlg A (app f p) F₀ᴰ
  
  Ty₀-DAlg (ext X) x _ = El X
  Ty₀-DAlg (base b) = Base₀-DAlg b
  Ty₀-DAlg (Π A B) y F₀ᴰ = Pi (El A) λ n → Base₀-DAlg B (app y n) F₀ᴰ
  Ty₀-DAlg (A [ _ ]) = Ty₀-DAlg A
  Ty₀-DAlg (A [ _ ]') = Ty₀-DAlg A
  
  Params₀-DAlg ● h _ = Unit
  Params₀-DAlg (Δ ‣‣ A) p F₀ᴰ = Pair (Params₀-DAlg Δ (fst p) F₀ᴰ) (Ty₀-DAlg A (snd p) F₀ᴰ)
  Params₀-DAlg (Δ [ _ ]p) = Params₀-DAlg Δ
  
  Base₀-DAlg ty1 a F₀ᴰ = proj₁ F₀ᴰ a
  Base₀-DAlg (ty2 _) a F₀ᴰ = proj₂ F₀ᴰ a
  
module _ {F₀} {F₀ᴰ : DFam₀ F₀} where

  CtorTm₀-DAlg : (c : CtorTm Γ C) {γ₀ : Spec₀-Alg Γ F₀} (γd₀ : Spec₀-DAlg Γ γ₀ F₀ᴰ)
               → Term (Ctor₀-DAlg C (CtorTm₀-Alg c γ₀) F₀ᴰ)
  Tm₀-DAlg : ∀{γ₀} (t : Tm Γ Δ A) (γd₀ : Spec₀-DAlg Γ γ₀ F₀ᴰ)
             {p : _} (pd : Term (Params₀-DAlg Δ p F₀ᴰ))
           → Term (Ty₀-DAlg A (Tm₀-Alg t γ₀ p) F₀ᴰ)
  Wk₀-DAlg : ∀{γ₀} (w : Wk Ω Γ) → Spec₀-DAlg Ω γ₀ F₀ᴰ
           → Spec₀-DAlg Γ (Wk₀-Alg w γ₀) F₀ᴰ
  Sub₀-DAlg : ∀{γ₀} (σ : Sub {Γ} Δ ∇) → Spec₀-DAlg Γ γ₀ F₀ᴰ
            → {p₀ : STerm (Params₀-Alg Δ F₀)} → Term (Params₀-DAlg Δ p₀ F₀ᴰ)
            → Term (Params₀-DAlg ∇ (Sub₀-Alg σ γ₀ p₀) F₀ᴰ)

  CtorTm₀-DAlg c γd₀ = γd₀ c

  Sub₀-DAlg Id x p = p
  Sub₀-DAlg (Ext σ t) x p = pair (Sub₀-DAlg σ x p) (Tm₀-DAlg t x p)
  Sub₀-DAlg Drop x p = fst p
  Sub₀-DAlg (σ ∘ τ) x p = Sub₀-DAlg τ x (Sub₀-DAlg σ x p)
  Sub₀-DAlg (σ [ w ]ws) x p = Sub₀-DAlg σ (Wk₀-DAlg w x) p
  
  Tm₀-DAlg vz δ p = snd p
  Tm₀-DAlg vz1 δ p = snd p
  Tm₀-DAlg (vs t) δ p = Tm₀-DAlg t δ (fst p)
  Tm₀-DAlg (ext A x) δ p = x
  Tm₀-DAlg (ctor x σ) δ p = CtorTm₀-DAlg x δ $ _ $ Sub₀-DAlg σ δ p
  Tm₀-DAlg (ctor-1 x σ) δ p = CtorTm₀-DAlg x δ $ _ $ Sub₀-DAlg σ δ p
  Tm₀-DAlg (App t) δ {p₀} p = app (Tm₀-DAlg t δ (fst p)) (snd p₀)
  Tm₀-DAlg (Lam t) δ p = lam λ n → Tm₀-DAlg t δ (pair p n)
  Tm₀-DAlg (t [ σ ]tm) δ p = Tm₀-DAlg t δ (Sub₀-DAlg σ δ p)
  Tm₀-DAlg (t [ w ]tm') δ p = Tm₀-DAlg t (Wk₀-DAlg w δ) p
  Tm₀-DAlg (t [ w ]tm'-1) δ p = Tm₀-DAlg t (Wk₀-DAlg w δ) p
  Tm₀-DAlg (App-U t f) γd₀ pd₀ = app f (Tm₀-DAlg t γd₀ pd₀)

  Base₀-DAlg[]b'
    : (A : Base Γ Δ) (w : Wk Ω Γ) (a : STerm (Base₀-Alg A F₀))
    → Base₀-DAlg (A [ w ]b') a F₀ᴰ ≡ Base₀-DAlg A a F₀ᴰ
  Base₀-DAlg[]b' ty1 w a = refl
  Base₀-DAlg[]b' (ty2 x) w a = refl
  {-# REWRITE Base₀-DAlg[]b' #-}

  -- Ctor₀-DAlg[]c
  --   : (C : Ctor Γ) (w : Wk Ω Γ) (c : STerm (Ctor₀-Alg C F₀))
  --   → Ctor₀-DAlg (C [ w ]c) c F₀ᴰ ≡ Ctor₀-DAlg C c F₀ᴰ
  -- Ctor₀-DAlg[]c (ctor Δ x) w c = refl
  -- {-# REWRITE Ctor₀-DAlg[]c #-}
  
  Wk₀-DAlg w f c = f (c [ w ]ctm)
