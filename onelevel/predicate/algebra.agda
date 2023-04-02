{-# OPTIONS --prop --rewriting #-}

module predicate.algebra where

open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import lib

BasePreds : Fam₀ → Set₁
BasePreds (C , T) = (C -> Prop) × (C -> T -> Prop)

variable
  F₁ : BasePreds F₀

Spec₁-Alg : (Γ : Spec) → Spec₀-Alg Γ F₀ → BasePreds F₀ → Prop
Ctor₁-Alg : (A : Ctor Γ) → Spec₀-Alg Γ F₀ → Ctor₀-Alg A F₀ → BasePreds F₀ -> Prop
Ty₁-Alg : (A : Ty Γ Δ) → Spec₀-Alg Γ F₀ → Params₀-Alg Δ F₀
          → Ty₀-Alg A F₀ → BasePreds F₀ -> Prop
Base₁-Alg : (A : Base Γ Δ) → Spec₀-Alg Γ F₀ → Params₀-Alg Δ F₀
          → Base₀-Alg A F₀ → BasePreds F₀ -> Prop
Params₁-Alg : (Δ : Params Γ) → Spec₀-Alg Γ F₀ → Params₀-Alg Δ F₀ → BasePreds F₀ -> Prop

Spec₁-Alg init x y = ⊤p
Spec₁-Alg (Γ ‣ A) (γ , a) y = ΣP (Spec₁-Alg Γ γ y) λ _ → Ctor₁-Alg A γ a y

Ctor₁-Alg (ctor Δ A) γ f x = {p : _} → Params₁-Alg Δ γ p x → Base₁-Alg A γ p (f p) x

Params₁-Alg ● γ ps bp = ⊤p
Params₁-Alg (Δ ‣‣ A) γ (ps , a) bp =
  ΣP (Params₁-Alg Δ γ ps bp) λ _ → Ty₁-Alg A γ ps a bp
Params₁-Alg (Δ [ x ]p) γ p bp = Params₁-Alg Δ (Wk₀-Alg x γ) p bp

Ty₁-Alg (ext A) γ p a x = ⊤p
Ty₁-Alg (base b) γ p a x = Base₁-Alg b γ p a x
Ty₁-Alg (Π A B) γ p a x = (n : El A) → Base₁-Alg B γ (p , n) (a n) x
Ty₁-Alg (A [ σ ]) γ p a x = Ty₁-Alg A γ (Sub₀-Alg σ γ p) a x
Ty₁-Alg (A [ w ]') γ p a x = Ty₁-Alg A (Wk₀-Alg w γ) p a x

Base₁-Alg ty1 γ p a x = proj₁ x a
Base₁-Alg (ty2 t) γ p a x = proj₂ x (Tm₀-Alg t γ p) a

Base₁-Alg[]b'
  : (A : Base Γ Δ) (w : Wk Ω Γ) {γ : Spec₀-Alg Ω F₀} {p : _} {a : _}
  → Base₁-Alg (A [ w ]b') γ p a F₁ ≡ Base₁-Alg A (Wk₀-Alg w γ) p a F₁

Sub₁-Alg : (σ : Sub {Γ} Δ ∇) {γ₀ : Spec₀-Alg Γ F₀}
           (δ : Spec₁-Alg Γ γ₀ F₁) {ps : _}
         → Params₁-Alg Δ γ₀ ps F₁
         → Params₁-Alg ∇ γ₀ (Sub₀-Alg σ γ₀ ps) F₁
Wk₁-Alg : (w : Wk Ω Γ) {γ : Spec₀-Alg Ω F₀}
        → Spec₁-Alg Ω γ F₁ → Spec₁-Alg Γ (Wk₀-Alg w γ) F₁
Tm₁-Alg : (t : Tm Γ Δ A) {γ : Spec₀-Alg Γ F₀} (δ : Spec₁-Alg Γ γ F₁)
          {ps : _} (ps' : Params₁-Alg Δ γ ps F₁)
        → Ty₁-Alg A γ ps (Tm₀-Alg t γ ps) F₁
CtorTm₁-Alg : (c : CtorTm Γ C) {γ : Spec₀-Alg Γ F₀} (δ : Spec₁-Alg Γ γ F₁)
            → Ctor₁-Alg C γ (CtorTm₀-Alg c γ) F₁

Sub₁-Alg Id δ x = x
Sub₁-Alg (Ext σ t) δ x = Sub₁-Alg σ δ x ,P Tm₁-Alg t δ x
Sub₁-Alg Drop δ x = fstP x
Sub₁-Alg (σ ∘ τ) δ x = Sub₁-Alg τ δ (Sub₁-Alg σ δ x)
Sub₁-Alg (σ [ w ]ws) δ x = Sub₁-Alg σ (Wk₁-Alg w δ) x

Tm₁-Alg vz δ p = sndP p
Tm₁-Alg vz1 δ p = sndP p
Tm₁-Alg (vs t) δ p = Tm₁-Alg t δ (fstP p)
Tm₁-Alg (ext A x) δ p = ttp -- ∣ liftSet x ∣
Tm₁-Alg (ctor x σ) δ p = CtorTm₁-Alg x δ (Sub₁-Alg σ δ p)
Tm₁-Alg (ctor-1 x σ) δ p = CtorTm₁-Alg x δ (Sub₁-Alg σ δ p)
Tm₁-Alg (app t) {γ} δ {_ , n} (p ,P _) = Tm₁-Alg t δ p n
Tm₁-Alg (lam t) δ p = λ n → Tm₁-Alg t δ (p ,P ttp)
Tm₁-Alg (t [ σ ]tm) δ p = Tm₁-Alg t δ (Sub₁-Alg σ δ p)
Tm₁-Alg (t [ w ]tm') δ p = Tm₁-Alg t (Wk₁-Alg w δ) p
Tm₁-Alg (t [ w ]tm'-1) δ p = Tm₁-Alg t (Wk₁-Alg w δ) p
Tm₁-Alg (app-U t x) δ p = ttp

Base₁-Alg[]b' ty1 w = refl
Base₁-Alg[]b' (ty2 x) w = refl
{-# REWRITE Base₁-Alg[]b' #-}

Ctor₁-Alg[]c
  : (C : Ctor Γ) (w : Wk Ω Γ) (γ₀ : Spec₀-Alg _ F₀) (c₀ : _)
  → Ctor₁-Alg (C [ w ]c) γ₀ c₀ F₁ ≡ Ctor₁-Alg C (Wk₀-Alg w γ₀) c₀ F₁
Ctor₁-Alg[]c (ctor Δ x) w γ₀ c₀ = refl
{-# REWRITE Ctor₁-Alg[]c #-}

Wk₁-Alg Id γ' = γ'
Wk₁-Alg Drop γ' = fstP γ'
Wk₁-Alg (w ∘w w') γ' = Wk₁-Alg w' (Wk₁-Alg w γ')

CtorTm₁-Alg v0c δ = sndP δ
CtorTm₁-Alg (dropc c) δ = CtorTm₁-Alg c (fstP δ)
CtorTm₁-Alg (c [ w ]ctm) δ = CtorTm₁-Alg c (Wk₁-Alg w δ)

Spec₁-Alg' : (Γ : Spec) → Spec₀-Alg Γ F₀ → BasePreds F₀ → Prop
Spec₁-Alg' Γ γ₀ P = ∀{C} (c : CtorTm Γ C) → Ctor₁-Alg C γ₀ (CtorTm₀-Alg c γ₀) P

to-Spec₁-Alg : (Γ : Spec) (γ₀ : Spec₀-Alg Γ F₀) → Spec₁-Alg' Γ γ₀ F₁ → Spec₁-Alg Γ γ₀ F₁
to-Spec₁-Alg init γ₀ γ₁ = ttp
to-Spec₁-Alg (Γ ‣ x) (γ₀ , c₀) γ₁ =
  to-Spec₁-Alg Γ γ₀ (λ c → γ₁ (c [ Drop ]ctm)) ,P γ₁ v0c
