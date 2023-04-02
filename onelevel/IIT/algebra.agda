{-# OPTIONS --prop --rewriting #-}

module IIT.algebra where

open import lib
open import IIT.spec

Ca = Fam {lzero}

Spec-Alg : Spec → Ca → Set
Ctor-Alg : {Γ : Spec} {f : _} -> Ctor Γ -> Spec-Alg Γ f -> Set
Params-Alg : {Γ : Spec} {f : _} → Params Γ → Spec-Alg Γ f → Set
Base-Alg : ∀{Γ Δ f} → Base Γ Δ → (γ : Spec-Alg Γ f) → Params-Alg Δ γ → Set
Ty-Alg : ∀{Γ Δ f} → Ty Γ Δ → (γ : Spec-Alg Γ f) → Params-Alg Δ γ → Set
Tm-Alg : ∀{Γ Δ A f} → Tm Γ Δ A → (γ : Spec-Alg Γ f) (δ : Params-Alg Δ γ) → Ty-Alg A γ δ
Sub-Alg : ∀{Γ} {Δ ∇ : Params Γ} {f : _} → Sub Δ ∇ → {γ : Spec-Alg Γ f}
        → Params-Alg Δ γ → Params-Alg ∇ γ
Wk-Alg : {Γ Δ : Spec} {f : _} → Wk Γ Δ → Spec-Alg Γ f → Spec-Alg Δ f
CtorTm-Alg : ∀{Γ A f} → CtorTm Γ A → (γ : Spec-Alg Γ f) → Ctor-Alg A γ

Spec-Alg init F = ⊤
Spec-Alg (Γ ‣ A) F = Σ (Spec-Alg Γ F) (Ctor-Alg A)

Ctor-Alg (ctor Δ A) γ = (p : Params-Alg Δ γ) → Base-Alg A γ p

Params-Alg ● γ = ⊤
Params-Alg (Δ ‣‣ A) γ = Σ (Params-Alg Δ γ) (Ty-Alg A γ)
Params-Alg (Δ [ x ]p) γ = Params-Alg Δ (Wk-Alg x γ)

Ty-Alg (ext A) γ p = El A
Ty-Alg (base x) γ p = Base-Alg x γ p
Ty-Alg (Π A B) γ p = (x : El A) → Base-Alg B γ (p , x)
Ty-Alg (A [ x ]) γ p = Ty-Alg A γ (Sub-Alg x p)
Ty-Alg (A [ w ]') γ p = Ty-Alg A (Wk-Alg w γ) p

Sub-Alg Id y = y
Sub-Alg (Ext x t) y = Sub-Alg x y , Tm-Alg t _ y
Sub-Alg Drop y = proj₁ y
Sub-Alg (σ ∘ τ) p = Sub-Alg τ (Sub-Alg σ p)
Sub-Alg (σ [ w ]ws) p = Sub-Alg σ p

Base-Alg {f = f} ty1 γ p = proj₁ f
Base-Alg {f = f} (ty2 x) γ p = proj₂ f (Tm-Alg x γ p)

Base-Alg-[]b'
  : ∀{Ω Γ Δ f} (A : Base Γ Δ) (w : Wk Ω Γ) (γ : Spec-Alg Ω f) (p : Params-Alg Δ _)
  → Base-Alg (A [ w ]b') γ p ≡ Base-Alg A (Wk-Alg w γ) p

Tm-Alg vz γ δ = proj₂ δ
Tm-Alg vz1 γ δ = proj₂ δ
Tm-Alg (vs t) γ δ = Tm-Alg t γ (proj₁ δ)
Tm-Alg (ext A x) γ δ = x
Tm-Alg (ctor x σ) γ δ = CtorTm-Alg x γ (Sub-Alg σ δ)
Tm-Alg (app t) γ (δ , n) = Tm-Alg t γ δ n
Tm-Alg (lam t) γ δ n = Tm-Alg t γ (δ , n)
Tm-Alg (t [ σ ]tm) γ δ = Tm-Alg t γ (Sub-Alg σ δ)
Tm-Alg (t [ w ]tm') γ δ = Tm-Alg t _ δ
Tm-Alg (ctor-1 x σ) γ δ = CtorTm-Alg x γ (Sub-Alg σ δ)
Tm-Alg (t [ w ]tm'-1) γ δ = Tm-Alg t _ δ
Tm-Alg (app-U x f) γ δ = f (Tm-Alg x γ δ)

Wk-Alg Id y = y
Wk-Alg Drop y = proj₁ y
Wk-Alg (w ∘w w') γ = Wk-Alg w' (Wk-Alg w γ)

Base-Alg-[]b' ty1 w γ p = refl
Base-Alg-[]b' (ty2 x) w γ p = refl
{-# REWRITE Base-Alg-[]b' #-}

Ctor-Alg[]c
  : ∀{f} C (w : Wk Ω Γ) (γ : Spec-Alg _ f)
  → Ctor-Alg (C [ w ]c) γ ≡ Ctor-Alg C (Wk-Alg w γ)
Ctor-Alg[]c (ctor Δ x) w γ = refl
{-# REWRITE Ctor-Alg[]c #-}

CtorTm-Alg v0c γ = proj₂ γ
CtorTm-Alg (dropc x) γ = CtorTm-Alg x (proj₁ γ)
CtorTm-Alg (_[_]ctm c w) γ = CtorTm-Alg c _

--------------------------------------------------------------------------------
-- Displayed algebras

DFam : Ca -> Set₁
DFam (A , B) = Σ (A -> Set) (λ A' → (a : A) -> A' a -> B a -> Set)

Spec-DAlg : ∀{s} (Γ : Spec) → Spec-Alg Γ s → DFam s → Set₁
Ctor-DAlg : ∀{s df}{Γ : Spec} (c : Ctor Γ) (γ : Spec-Alg Γ s)
    -> Spec-DAlg Γ γ df -> Ctor-Alg c γ -> Set
Params-DAlg : ∀{Γ s df}
            → (Δ : Params Γ) (γ : Spec-Alg Γ s) → Spec-DAlg Γ γ df
            → Params-Alg Δ γ
            → Set
Base-DAlg : ∀{Γ Δ s df} (b : Base Γ Δ) {γ : Spec-Alg Γ s} (δ : Spec-DAlg Γ γ df)
          → {ps : Params-Alg Δ γ} → Params-DAlg Δ γ δ ps → Base-Alg b γ ps → Set
Ty-DAlg : ∀{Γ Δ s df} (b : Ty Γ Δ) {γ : Spec-Alg Γ s} (δ : Spec-DAlg Γ γ df)
          → {ps : Params-Alg Δ γ} → Params-DAlg Δ γ δ ps → Ty-Alg b γ ps → Set

Tm-DAlg : ∀{Γ Δ A s df} (t : Tm Γ Δ A)
        → {γ : Spec-Alg Γ s} (x : Spec-DAlg Γ γ df)
        → {p : _} (ps : Params-DAlg Δ γ x p)
        → Ty-DAlg A x ps (Tm-Alg t γ p)
CtorTm-DAlg : ∀{Γ A s df} (t : CtorTm Γ A)
              {γ : Spec-Alg Γ s} (x : Spec-DAlg Γ γ df)
            → Ctor-DAlg A γ x (CtorTm-Alg t γ)
Wk-DAlg : ∀{Γ Ω s df} {γ : Spec-Alg Ω s}
        → (w : Wk Ω Γ)
        → Spec-DAlg Ω γ df
        → Spec-DAlg Γ (Wk-Alg w γ) df
Sub-DAlg : ∀{Γ Δ ∇ s df} {γ : Spec-Alg Γ s} {δ : Spec-DAlg Γ γ df} {ps : _}
         → (σ : Sub Δ ∇)
         → Params-DAlg Δ γ δ ps
         → Params-DAlg ∇ γ δ (Sub-Alg σ ps)

Spec-DAlg init γ df = ⊤
Spec-DAlg (Γ ‣ A) (γ , a) df = Σ (Spec-DAlg Γ γ df) λ x → Ctor-DAlg A γ x a

Ctor-DAlg (ctor Δ A) γ δ a =
  {ps : Params-Alg Δ γ} (x : Params-DAlg Δ γ δ ps) → Base-DAlg A δ x (a ps)

Params-DAlg ● γ x x₁ = ⊤
Params-DAlg (Δ ‣‣ A) γ x y =
  Σ (Params-DAlg Δ γ x (proj₁ y)) λ z → Ty-DAlg A x z (proj₂ y)
Params-DAlg (Δ [ w ]p) γ x y = Params-DAlg Δ _ (Wk-DAlg w x) y

Ty-DAlg (ext A) δ p a = ⊤
Ty-DAlg (base x) δ p a = Base-DAlg x δ p a
Ty-DAlg (Π A x) δ p f = (n : El A) → Base-DAlg x δ (p , tt) (f n)
Ty-DAlg (A [ x ]) δ p a = Ty-DAlg A δ (Sub-DAlg x p) a
Ty-DAlg (A [ w ]') δ p a = Ty-DAlg A (Wk-DAlg w δ) p a

Base-DAlg {df = df} ty1 δ x y = proj₁ df y
Base-DAlg {df = df} (ty2 t) δ {ps} x y = proj₂ df (Tm-Alg t _ ps) (Tm-DAlg t δ x) y

Base-DAlg[]b'
  : ∀{Γ Ω Δ s df} (A : Base Γ Δ) (w : Wk Ω Γ) {γ : Spec-Alg Ω s} (δ : Spec-DAlg Ω γ df)
    {ps : Params-Alg Δ _} (pd : Params-DAlg Δ _ _ ps) (a : Base-Alg A _ ps)
  → Base-DAlg (A [ w ]b') δ pd a ≡ Base-DAlg A (Wk-DAlg w δ) pd a

Sub-DAlg Id x = x
Sub-DAlg (Ext σ x) p = Sub-DAlg σ p , Tm-DAlg x _ p
Sub-DAlg Drop = proj₁
Sub-DAlg (σ ∘ τ) x = Sub-DAlg τ (Sub-DAlg σ x)
Sub-DAlg (σ [ w ]ws) x = Sub-DAlg σ x

Wk-DAlg Id x = x
Wk-DAlg Drop x = proj₁ x
Wk-DAlg (w ∘w w') x = Wk-DAlg w' (Wk-DAlg w x)

Tm-DAlg vz x ps = proj₂ ps
Tm-DAlg vz1 x ps = proj₂ ps
Tm-DAlg (vs t) x ps = Tm-DAlg t x (proj₁ ps)
Tm-DAlg (ext A x) γ ps = tt
Tm-DAlg (ctor c σ) x ps = CtorTm-DAlg c x (Sub-DAlg σ ps)
Tm-DAlg (ctor-1 c σ) x ps = CtorTm-DAlg c x (Sub-DAlg σ ps)
Tm-DAlg (app t) x (ps , _) = Tm-DAlg t x ps _
Tm-DAlg (lam t) x ps = λ n → Tm-DAlg t x (ps , tt)
Tm-DAlg (t [ σ ]tm) x p = Tm-DAlg t x (Sub-DAlg σ p)
Tm-DAlg (t [ w ]tm') x p = Tm-DAlg t (Wk-DAlg w x) p
Tm-DAlg (t [ w ]tm'-1) x p = Tm-DAlg t (Wk-DAlg w x) p
Tm-DAlg (app-U x f) y z = tt

Base-DAlg[]b' ty1 w δ pd a = refl
Base-DAlg[]b' (ty2 x) w δ pd a = refl
{-# REWRITE Base-DAlg[]b' #-}

Ctor-DAlg[]c
  : ∀{f df} C (w : Wk Ω Γ) (γ : Spec-Alg _ f) (γ' : Spec-DAlg _ _ df) (c : _)
  → Ctor-DAlg (C [ w ]c) γ γ' c ≡ Ctor-DAlg C _ (Wk-DAlg w γ') c
Ctor-DAlg[]c (ctor Δ x) w γ γ' c = refl
{-# REWRITE Ctor-DAlg[]c #-}

CtorTm-DAlg v0c x = proj₂ x
CtorTm-DAlg (dropc t) x = CtorTm-DAlg t (proj₁ x)
CtorTm-DAlg (_[_]ctm c w) x = CtorTm-DAlg c (Wk-DAlg w x)
