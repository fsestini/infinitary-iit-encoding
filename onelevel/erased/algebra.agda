{-# OPTIONS --prop --rewriting #-}

module erased.algebra where

open import lib
open import IIT.spec
open import IIT.algebra

Fam₀ : Set₁
Fam₀ = Set × Set

variable
  F₀ : Fam₀

Spec₀-Alg : Spec -> Fam₀ -> Set
Ctor₀-Alg : ∀{Γ} → Ctor Γ -> Fam₀ -> Set
Params₀-Alg : ∀{Γ} → Params Γ -> Fam₀ -> Set
Ty₀-Alg : ∀{Γ Δ} → Ty Γ Δ -> Fam₀ -> Set
Base₀-Alg : ∀{Γ Δ} → Base Γ Δ -> Fam₀ -> Set

Spec₀-Alg init X = ⊤
Spec₀-Alg (Γ ‣ C) X = Spec₀-Alg Γ X × Ctor₀-Alg C X

Ctor₀-Alg (ctor Δ A) x = Params₀-Alg Δ x → Base₀-Alg A x

Params₀-Alg ● x = ⊤
Params₀-Alg (Δ ‣‣ A) x = Params₀-Alg Δ x × Ty₀-Alg A x
Params₀-Alg (Δ [ x ]p) p = Params₀-Alg Δ p

Ty₀-Alg (ext A) x = El A
Ty₀-Alg (base b) x = Base₀-Alg b x
Ty₀-Alg (Π A B) x = El A → Base₀-Alg B x
Ty₀-Alg (A [ x₁ ]) x = Ty₀-Alg A x
Ty₀-Alg (A [ w ]') x = Ty₀-Alg A x

Base₀-Alg ty1 x = proj₁ x
Base₀-Alg (ty2 _) x = proj₂ x

Base₀-Alg[]b'
  : ∀{s} (A : Base Γ Δ) (w : Wk Ω Γ) → Base₀-Alg (A [ w ]b') s ≡ Base₀-Alg A s

Tm₀-Alg : Tm Γ Δ A → Spec₀-Alg Γ F₀ → Params₀-Alg Δ F₀ → Ty₀-Alg A F₀
CtorTm₀-Alg : CtorTm Γ C → Spec₀-Alg Γ F₀ → Ctor₀-Alg C F₀
Wk₀-Alg : Wk Γ Ω → Spec₀-Alg Γ F₀ → Spec₀-Alg Ω F₀
Sub₀-Alg : Sub {Γ} Δ ∇ → Spec₀-Alg Γ F₀ → Params₀-Alg Δ F₀ → Params₀-Alg ∇ F₀

Sub₀-Alg Id _ ps = ps
Sub₀-Alg (Ext σ t) x ps = Sub₀-Alg σ x ps , Tm₀-Alg t x ps
Sub₀-Alg Drop x ps = proj₁ ps
Sub₀-Alg (σ ∘ τ) x ps = Sub₀-Alg τ x (Sub₀-Alg σ x ps)
Sub₀-Alg (σ [ w ]ws) x ps = Sub₀-Alg σ (Wk₀-Alg w x) ps

Wk₀-Alg Id x = x
Wk₀-Alg Drop x = proj₁ x
Wk₀-Alg (w ∘w w₁) x = Wk₀-Alg w₁ (Wk₀-Alg w x)

Tm₀-Alg vz γ p = proj₂ p
Tm₀-Alg vz1 γ p = proj₂ p
Tm₀-Alg (vs t) γ p = Tm₀-Alg t γ (proj₁ p)
Tm₀-Alg (ext A x) γ p = x
Tm₀-Alg (ctor x σ) γ p = CtorTm₀-Alg x γ (Sub₀-Alg σ γ p)
Tm₀-Alg (ctor-1 x σ) γ p = CtorTm₀-Alg x γ (Sub₀-Alg σ γ p)
Tm₀-Alg (app t) γ (p , n) = Tm₀-Alg t γ p n
Tm₀-Alg (lam t) γ p n = Tm₀-Alg t γ (p , n)
Tm₀-Alg (t [ σ ]tm) γ p = Tm₀-Alg t γ (Sub₀-Alg σ γ p)
Tm₀-Alg (t [ w ]tm') γ p = Tm₀-Alg t (Wk₀-Alg w γ) p
Tm₀-Alg (t [ w ]tm'-1) γ p = Tm₀-Alg t (Wk₀-Alg w γ) p
Tm₀-Alg (app-U x f) γ p = f (Tm₀-Alg x γ p)

Base₀-Alg[]b' ty1 w = refl
Base₀-Alg[]b' (ty2 x) w = refl
{-# REWRITE Base₀-Alg[]b' #-}

Ctor₀-Alg[]c : ∀{s} (C : Ctor Γ) (w : Wk Ω Γ) → Ctor₀-Alg (C [ w ]c) s ≡ Ctor₀-Alg C s
Ctor₀-Alg[]c (ctor Δ x) w = refl
{-# REWRITE Ctor₀-Alg[]c #-}

CtorTm₀-Alg v0c x = proj₂ x
CtorTm₀-Alg (dropc c) x = CtorTm₀-Alg c (proj₁ x)
CtorTm₀-Alg (_[_]ctm c w) x = CtorTm₀-Alg c (Wk₀-Alg w x)

----------

DFam₀ : Fam₀ -> Set (lsuc i)
DFam₀ {i} (A , B) = (A -> Set i) × (B -> Set i)

variable
  F₀ᴰ : DFam₀ F₀

Spec₀-DAlg : ∀ Γ (γ : Spec₀-Alg Γ F₀) -> DFam₀ {i} F₀ -> Set i
Ctor₀-DAlg : (A : Ctor Γ) -> DFam₀ {i} F₀ -> Ctor₀-Alg A F₀ -> Set i
Ty₀-DAlg : (A : Ty Γ Δ) -> DFam₀ {i} F₀ -> Ty₀-Alg A F₀ -> Set i
Base₀-DAlg : (A : Base Γ Δ) -> DFam₀ {i} F₀ -> Base₀-Alg A F₀ -> Set i
Params₀-DAlg : (Δ : Params Γ) -> DFam₀ {i} F₀ -> Params₀-Alg Δ F₀ -> Set i

Ctor₀-DAlg (ctor Δ A) x f = {p : _} → Params₀-DAlg Δ x p -> Base₀-DAlg A x (f p)

Spec₀-DAlg Γ γ Y = ∀ {C} (c : CtorTm Γ C) → Ctor₀-DAlg C Y (CtorTm₀-Alg c γ)

Ty₀-DAlg (ext A) x y = ⊤ -- LiftSet (El A)
Ty₀-DAlg (base b) x y = Base₀-DAlg b x y
Ty₀-DAlg (Π A B) x y = (n : El A) → Base₀-DAlg B x (y n) 
Ty₀-DAlg (A [ _ ]) x y = Ty₀-DAlg A x y
Ty₀-DAlg (A [ _ ]') x y = Ty₀-DAlg A x y

Params₀-DAlg ● x h = ⊤
Params₀-DAlg (Δ ‣‣ A) x (h , a) = Params₀-DAlg Δ x h × Ty₀-DAlg A x a
Params₀-DAlg (Δ [ _ ]p) x y = Params₀-DAlg Δ x y

Base₀-DAlg ty1 x a = proj₁ x a
Base₀-DAlg (ty2 _) x a = proj₂ x a

CtorTm₀-DAlg : (c : CtorTm Γ C) {γ₀ : Spec₀-Alg Γ F₀} (γ₀ᴰ : Spec₀-DAlg Γ γ₀ F₀ᴰ)
             → Ctor₀-DAlg C F₀ᴰ (CtorTm₀-Alg c γ₀)
Tm₀-DAlg : (t : Tm Γ Δ A) {γ₀ : Spec₀-Alg Γ F₀} (γ₀ᴰ : Spec₀-DAlg Γ γ₀ F₀ᴰ)
           {p : _} (pd : Params₀-DAlg Δ F₀ᴰ p)
         → Ty₀-DAlg A F₀ᴰ (Tm₀-Alg t γ₀ p)
Wk₀-DAlg : (w : Wk Ω Γ) {γ₀ : Spec₀-Alg Ω F₀} → Spec₀-DAlg Ω γ₀ F₀ᴰ
         → Spec₀-DAlg Γ (Wk₀-Alg w γ₀) F₀ᴰ
Sub₀-DAlg : (σ : Sub {Γ} Δ ∇) {γ₀ : Spec₀-Alg Γ F₀} → Spec₀-DAlg Γ γ₀ F₀ᴰ
          → {p₀ : Params₀-Alg Δ F₀} → Params₀-DAlg Δ F₀ᴰ p₀
          → Params₀-DAlg ∇ F₀ᴰ (Sub₀-Alg σ γ₀ p₀)

Sub₀-DAlg Id x p = p
Sub₀-DAlg (Ext σ t) x p = Sub₀-DAlg σ x p , Tm₀-DAlg t x p
Sub₀-DAlg Drop x p = proj₁ p
Sub₀-DAlg (σ ∘ τ) x p = Sub₀-DAlg τ x (Sub₀-DAlg σ x p)
Sub₀-DAlg (σ [ w ]ws) x p = Sub₀-DAlg σ (Wk₀-DAlg w x) p

Tm₀-DAlg vz δ p = proj₂ p
Tm₀-DAlg vz1 δ p = proj₂ p
Tm₀-DAlg (vs t) δ p = Tm₀-DAlg t δ (proj₁ p)
Tm₀-DAlg (ext A x) δ p = tt -- liftSet x
Tm₀-DAlg (ctor x σ) δ p = CtorTm₀-DAlg x δ (Sub₀-DAlg σ δ p)
Tm₀-DAlg (ctor-1 x σ) δ p = CtorTm₀-DAlg x δ (Sub₀-DAlg σ δ p)
Tm₀-DAlg (app t) {γ} δ {p₀ , n} (p , _) = Tm₀-DAlg t δ p n
Tm₀-DAlg (lam t) δ p = λ n → Tm₀-DAlg t δ (p , tt) -- liftSet n)
Tm₀-DAlg (t [ σ ]tm) δ p = Tm₀-DAlg t δ (Sub₀-DAlg σ δ p)
Tm₀-DAlg (t [ w ]tm') δ p = Tm₀-DAlg t (Wk₀-DAlg w δ) p
Tm₀-DAlg (t [ w ]tm'-1) δ p = Tm₀-DAlg t (Wk₀-DAlg w δ) p
Tm₀-DAlg (app-U x f) {γ} δ {p} p' = tt -- liftSet (Tm₀-Alg (app-U x f) γ p)

Base₀-DAlg[]b'
  : (A : Base Γ Δ) (w : Wk Ω Γ) (a : Base₀-Alg A F₀)
  → Base₀-DAlg (A [ w ]b') F₀ᴰ a ≡ Base₀-DAlg A F₀ᴰ a
Base₀-DAlg[]b' ty1 w a = refl
Base₀-DAlg[]b' (ty2 x) w a = refl
{-# REWRITE Base₀-DAlg[]b' #-}

Ctor₀-DAlg[]c
  : (C : Ctor Γ) (w : Wk Ω Γ) (c : Ctor₀-Alg C F₀)
  → Ctor₀-DAlg (C [ w ]c) F₀ᴰ c ≡ Ctor₀-DAlg C F₀ᴰ c
Ctor₀-DAlg[]c (ctor Δ x) w c = refl
{-# REWRITE Ctor₀-DAlg[]c #-}

Wk₀-DAlg w γ' c = γ' (c [ w ]ctm)

CtorTm₀-DAlg c δ = δ c
