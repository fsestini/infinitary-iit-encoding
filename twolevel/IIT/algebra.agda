{-# OPTIONS --prop --rewriting #-}

module IIT.algebra where

open import lib hiding (Σp ; fst ; snd ; Fam)
open import IIT.spec
open import hoas-postulated

Fam : Set
Fam = Σ SType λ A → STerm A → SType

DFam : Fam -> Set
DFam (A , B) = Σ (STerm A -> SType) (λ A' → (a : STerm A) -> STerm (A' a) -> STerm (B a) -> SType)

variable
  F : Fam

Spec-Alg : Spec → Fam → Set
Ctor-Alg : Ctor Γ -> Spec-Alg Γ F -> SType
Params-Alg : Params Γ → Spec-Alg Γ F → SType
Base-Alg : Base Γ Δ → (γ : Spec-Alg Γ F) → STerm (Params-Alg Δ γ) → SType
Ty-Alg : Ty Γ Δ → (γ : Spec-Alg Γ F) → STerm (Params-Alg Δ γ) → SType
Tm-Alg : Tm Γ Δ A → (γ : Spec-Alg Γ F) (δ : STerm (Params-Alg Δ γ)) → STerm (Ty-Alg A γ δ)
Sub-Alg : Sub Δ ∇ → {γ : Spec-Alg Γ F} → STerm (Params-Alg Δ γ) → STerm (Params-Alg ∇ γ)
Wk-Alg : Wk Γ Ω → Spec-Alg Γ F → Spec-Alg Ω F
CtorTm-Alg : CtorTm Γ C → (γ : Spec-Alg Γ F) → STerm (Ctor-Alg C γ)
  
Spec-Alg init _ = ⊤
Spec-Alg (Γ ‣ A) F = Σ (Spec-Alg Γ F) (λ γ → STerm (Ctor-Alg A γ))

Ctor-Alg (ctor Δ A) γ = PiU (Params-Alg Δ γ) (Base-Alg A γ)

Params-Alg ● γ = 𝟙U
Params-Alg (Δ ‣‣ A) γ = SigmaU (Params-Alg Δ γ) (Ty-Alg A γ)
Params-Alg (Δ [ x ]p) γ = Params-Alg Δ (Wk-Alg x γ)

Ty-Alg (ext A) γ p = A
Ty-Alg (base x) γ p = Base-Alg x γ p
Ty-Alg (Π A B) γ p = PiU A (λ n → Base-Alg B γ (pair p n))
Ty-Alg (A [ x ]) γ p = Ty-Alg A γ (Sub-Alg x p)
Ty-Alg (A [ w ]') γ p = Ty-Alg A (Wk-Alg w γ) p

Sub-Alg Id y = y
Sub-Alg (Ext x t) y = pair (Sub-Alg x y) (Tm-Alg t _ y)
Sub-Alg Drop y = fst y
Sub-Alg (σ ∘ τ) p = Sub-Alg τ (Sub-Alg σ p)
Sub-Alg (σ [ w ]ws) p = Sub-Alg σ p

Base-Alg {F = F} ty1 γ p = proj₁ F
Base-Alg {F = F} (ty2 x) γ p = proj₂ F (Tm-Alg x γ p)  

Base-Alg-[]b'
  : ∀{Ω Γ Δ} (A : Base Γ Δ) (w : Wk Ω Γ) (γ : Spec-Alg Ω F) (p : STerm (Params-Alg Δ _))
  → Base-Alg (A [ w ]b') γ p ≡ Base-Alg A (Wk-Alg w γ) p

{-# TERMINATING #-}
Tm-Alg vz γ δ = snd δ
Tm-Alg vz1 γ δ = snd δ
Tm-Alg (vs t) γ δ = Tm-Alg t γ (fst δ)
Tm-Alg (ext A x) γ δ = x
Tm-Alg (ctor x σ) γ δ = app (CtorTm-Alg x γ) (Sub-Alg σ δ)
Tm-Alg (App t) γ p = app (Tm-Alg t γ (fst p)) (snd p)
Tm-Alg (Lam t) γ δ = lam (λ n → Tm-Alg t γ (pair δ n))
Tm-Alg (t [ σ ]tm) γ δ = Tm-Alg t γ (Sub-Alg σ δ)
Tm-Alg (t [ w ]tm') γ δ = Tm-Alg t _ δ
Tm-Alg (ctor-1 x σ) γ δ = app (CtorTm-Alg x γ) (Sub-Alg σ δ)
Tm-Alg (t [ w ]tm'-1) γ δ = Tm-Alg t _ δ
Tm-Alg (App-U t f) γ δ = app f (Tm-Alg t γ δ)

Wk-Alg Id y = y
Wk-Alg Drop y = proj₁ y -- proj₁ y
Wk-Alg (w ∘w w') γ = Wk-Alg w' (Wk-Alg w γ)

Base-Alg-[]b' ty1 w γ p = refl
Base-Alg-[]b' (ty2 x) w γ p = refl
{-# REWRITE Base-Alg-[]b' #-}

-- Ctor-Alg[]c
--   : ∀ C (w : Wk Ω Γ) (γ : Spec-Alg _ F)
--   → Ctor-Alg (C [ w ]c) γ ≡ Ctor-Alg C (Wk-Alg w γ)
-- Ctor-Alg[]c (ctor Δ x) w γ = refl
-- {-# REWRITE Ctor-Alg[]c #-}

CtorTm-Alg v0c γ = proj₂ γ
CtorTm-Alg (dropc x) γ = CtorTm-Alg x (proj₁ γ)
CtorTm-Alg (_[_]ctm c w) γ = CtorTm-Alg c _

-- variable
--   γ : Spec-Alg Γ F


--------------------------------------------------------------------------------
-- Displayed algebras
  
Spec-DAlg : (Γ : Spec) → Spec-Alg Γ F → DFam F → Set
Ctor-DAlg : ∀{Fᴰ}(C : Ctor Γ) {γ : Spec-Alg Γ F} → Spec-DAlg Γ γ Fᴰ → STerm (Ctor-Alg C γ) → SType
Params-DAlg : ∀{Fᴰ} (Δ : Params Γ) {γ : Spec-Alg Γ F} → Spec-DAlg Γ γ Fᴰ → STerm (Params-Alg Δ γ) → SType
Base-DAlg : ∀{Fᴰ} (B : Base Γ Δ) {γ : Spec-Alg Γ F} (γd : Spec-DAlg Γ γ Fᴰ) {δ : _}
          → STerm (Params-DAlg Δ γd δ) → STerm (Base-Alg B γ δ) → SType
Ty-DAlg : ∀{Fᴰ} (A : Ty Γ Δ) {γ : Spec-Alg Γ F} (δ : Spec-DAlg Γ γ Fᴰ) {ps : _}
        → STerm (Params-DAlg Δ δ ps) → STerm (Ty-Alg A γ ps) → SType

Tm-DAlg : ∀{Fᴰ} (t : Tm Γ Δ A) {γ : Spec-Alg Γ F} (γd : Spec-DAlg Γ γ Fᴰ) {p : _} (ps : STerm (Params-DAlg Δ γd p))
        → STerm (Ty-DAlg A γd ps (Tm-Alg t γ p))
CtorTm-DAlg : ∀{Fᴰ} (t : CtorTm Γ C) {γ : Spec-Alg Γ F} (x : Spec-DAlg Γ γ Fᴰ) → STerm (Ctor-DAlg C x (CtorTm-Alg t γ))
Wk-DAlg : ∀{Fᴰ} {γ : Spec-Alg Ω F} (w : Wk Ω Γ) → Spec-DAlg Ω γ Fᴰ → Spec-DAlg Γ (Wk-Alg w γ) Fᴰ
Sub-DAlg : ∀{Fᴰ} (σ : Sub Δ ∇) {γ : Spec-Alg Γ F} {δ : Spec-DAlg Γ γ Fᴰ} {ps : _} 
         → STerm (Params-DAlg Δ δ ps) → STerm (Params-DAlg ∇ δ (Sub-Alg σ ps))

Spec-DAlg init _ _ = ⊤
Spec-DAlg (Γ ‣ A) (γ , a) Fᴰ = Σ (Spec-DAlg Γ γ Fᴰ) λ x → STerm (Ctor-DAlg A x a)

Ctor-DAlg (ctor Δ A) γd c =
  PiU (Params-Alg Δ _) (λ δ → PiU (Params-DAlg Δ γd δ) λ x → Base-DAlg A γd x (app c δ))

Params-DAlg ● γd _ = 𝟙U
Params-DAlg (Δ ‣‣ A) γd y =
  SigmaU (Params-DAlg Δ γd (fst y)) λ z → Ty-DAlg A γd z (snd y)
Params-DAlg (Δ [ w ]p) γd y = Params-DAlg Δ (Wk-DAlg w γd) y

Ty-DAlg (ext A) δ p a = 𝟙U
Ty-DAlg (base x) δ p a = Base-DAlg x δ p a
Ty-DAlg (Π A B) δ p f = PiU A λ n → Base-DAlg B δ (pair p star) (app f n)
Ty-DAlg (A [ x ]) δ p a = Ty-DAlg A δ (Sub-DAlg x p) a
Ty-DAlg (A [ w ]') δ p a = Ty-DAlg A (Wk-DAlg w δ) p a

Base-DAlg {Fᴰ = Fᴰ} ty1 δ x y = proj₁ Fᴰ y
Base-DAlg {Fᴰ = Fᴰ} (ty2 t) δ {ps} x y = proj₂ Fᴰ (Tm-Alg t _ ps) (Tm-DAlg t δ x) y

Base-DAlg[]b'
  : ∀{Fᴰ}(B : Base Γ Δ) (w : Wk Ω Γ) {γ : Spec-Alg Ω F} (δ : Spec-DAlg Ω γ Fᴰ)
    {ps : STerm (Params-Alg Δ _)} (pd : STerm (Params-DAlg Δ _ ps))
    (a : STerm (Base-Alg B _ ps))
  → Base-DAlg (B [ w ]b') δ pd a ≡ Base-DAlg B (Wk-DAlg w δ) pd a

Sub-DAlg Id x = x
Sub-DAlg (Ext σ x) p = pair (Sub-DAlg σ p) (Tm-DAlg x _ p)
Sub-DAlg Drop p = fst p
Sub-DAlg (σ ∘ τ) x = Sub-DAlg τ (Sub-DAlg σ x)
Sub-DAlg (σ [ w ]ws) x = Sub-DAlg σ x

Wk-DAlg Id x = x
Wk-DAlg Drop x = proj₁ x
Wk-DAlg (w ∘w w') x = Wk-DAlg w' (Wk-DAlg w x)

{-# TERMINATING #-}
Tm-DAlg vz x ps = snd ps
Tm-DAlg vz1 x ps = snd ps
Tm-DAlg (vs t) x ps = Tm-DAlg t x (fst ps)
Tm-DAlg (ext A x) γ ps = star
Tm-DAlg (ctor c σ) x ps = CtorTm-DAlg c x $ _ $ Sub-DAlg σ ps
Tm-DAlg (ctor-1 c σ) x ps = CtorTm-DAlg c x $ _ $ Sub-DAlg σ ps
Tm-DAlg (App t) x ps = app (Tm-DAlg t x (fst ps)) _
Tm-DAlg (Lam t) x ps = lam (λ n → Tm-DAlg t x (pair ps star))
Tm-DAlg (t [ σ ]tm) x p = Tm-DAlg t x (Sub-DAlg σ p)
Tm-DAlg (t [ w ]tm') x p = Tm-DAlg t (Wk-DAlg w x) p
Tm-DAlg (t [ w ]tm'-1) x p = Tm-DAlg t (Wk-DAlg w x) p
Tm-DAlg (App-U t f) x p = star

Base-DAlg[]b' ty1 w δ pd a = refl
Base-DAlg[]b' (ty2 x) w δ pd a = refl
{-# REWRITE Base-DAlg[]b' #-}

-- Ctor-DAlg[]c
--   : ∀ {Fᴰ} C (w : Wk Ω Γ) {γ : Spec-Alg Ω F} (γ' : Spec-DAlg Ω γ Fᴰ) (c : _)
--   → Ctor-DAlg (C [ w ]c) γ' c ≡ Ctor-DAlg C (Wk-DAlg w γ') c
-- Ctor-DAlg[]c (ctor Δ x) w γ' c = refl
-- {-# REWRITE Ctor-DAlg[]c #-}

CtorTm-DAlg v0c x = proj₂ x
CtorTm-DAlg (dropc t) x = CtorTm-DAlg t (proj₁ x)
CtorTm-DAlg (_[_]ctm c w) x = CtorTm-DAlg c (Wk-DAlg w x)

-- variable
--   γᴰ : Spec-DAlg Γ γ

