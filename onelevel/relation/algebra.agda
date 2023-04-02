{-# OPTIONS --prop --rewriting #-}

module relation.algebra where

open import lib
open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import predicate.algebra

RelTys : (f : Fam) → DFam f → Set _
RelTys (C , T) (Cᴰ , Tᴰ) =
  ((c : C) → Cᴰ c → Set) × ((c : C) (cᴰ : Cᴰ c) (t : T c) → Tᴰ c cᴰ t → Set)

Spec-R-Alg : ∀{f df} (Γ : Spec) {γ : Spec-Alg Γ f} (δ : Spec-DAlg Γ γ df) → RelTys f df → Set
Ctor-R-Alg : ∀{Γ f df} (A : Ctor Γ) {γ : Spec-Alg Γ f} {a : Ctor-Alg A γ} {δ : Spec-DAlg Γ γ df}
             (a' : Ctor-DAlg A γ δ a) → RelTys f df → Set
Params-R-Alg : ∀{Γ f df} (Δ : Params Γ) {γ : Spec-Alg Γ f} {δ : Spec-DAlg Γ γ df} {ps : _}
             → Params-DAlg Δ γ δ ps → RelTys f df → Set

Ty-R-Alg : ∀{Γ f df Δ} (A : Ty Γ Δ) {γ : Spec-Alg Γ f} {δ : Spec-DAlg Γ γ df}
             {ps' : _} {ps : Params-DAlg Δ γ δ ps'}
             {a : _} (a' : Ty-DAlg A δ ps a) → RelTys f df → Set
Base-R-Alg : ∀{Γ f df Δ} (A : Base Γ Δ) {γ : Spec-Alg Γ f} {δ : Spec-DAlg Γ γ df}
             {ps' : _} {ps : Params-DAlg Δ γ δ ps'}
             {a : _} (a' : Base-DAlg A δ ps a) → RelTys f df → Set

-- Spec-R-Alg init δ x = ⊤
-- Spec-R-Alg (Γ ‣ A) (δ , a') x = Spec-R-Alg Γ δ x × Ctor-R-Alg A a' x

Spec-R-Alg Γ δ x = ∀{C} (c : CtorTm Γ C) → Ctor-R-Alg C (CtorTm-DAlg c δ) x

Ctor-R-Alg (ctor Δ A) a x =
  {ps : _} {ps-d : Params-DAlg Δ _ _ ps}
  → Params-R-Alg Δ ps-d x → Base-R-Alg A (a ps-d) x

Params-R-Alg ● x y = ⊤
Params-R-Alg (Δ ‣‣ A) (x , y) z = Params-R-Alg Δ x z × Ty-R-Alg A y z
Params-R-Alg (Δ [ w ]p) x y = Params-R-Alg Δ x y

Ty-R-Alg (ext A) a x = ⊤
Ty-R-Alg (base b) a x = Base-R-Alg b a x
Ty-R-Alg (Π A B) a x = (n : El A) → Base-R-Alg B (a n) x
Ty-R-Alg (A [ σ ]) a x = Ty-R-Alg A a x
Ty-R-Alg (A [ w ]') a x = Ty-R-Alg A a x

Base-R-Alg ty1 a x = proj₁ x _ a
Base-R-Alg (ty2 t) {_} {δ} {_} {ps} a x = proj₂ x _ (Tm-DAlg t δ ps) _ a

Base-R-Alg[]b'
  : ∀{f df r} (A : Base Γ Δ) (w : Wk Ω Γ)
    {γ : Spec-Alg Ω f} {δ : Spec-DAlg Ω γ df}
    {ps' : _} {ps : Params-DAlg Δ _ (Wk-DAlg w δ) ps'} {a : _} (a' : Base-DAlg A _ ps a)
  → Base-R-Alg (A [ w ]b') a' r ≡ Base-R-Alg A a' r

Wk-R-Alg : ∀{Γ Ω f df} (w : Wk Γ Ω) {γ : Spec-Alg Γ f} {δ : Spec-DAlg Γ γ df} {x : _}
         → Spec-R-Alg Γ δ x → Spec-R-Alg Ω (Wk-DAlg w δ) x
Sub-R-Alg : ∀{Γ Δ ∇ f df x} (σ : Sub Δ ∇) {γ : Spec-Alg Γ f} {δ : Spec-DAlg Γ γ df} (r : Spec-R-Alg Γ δ x)
          → {ps' : _} {ps : Params-DAlg Δ γ δ ps'}
          → Params-R-Alg Δ ps x → Params-R-Alg ∇ (Sub-DAlg σ ps) x
Tm-R-Alg
  : ∀{Γ Δ A f df x} (t : Tm Γ Δ A)
    {γ : Spec-Alg Γ f} {δ : Spec-DAlg Γ γ df} (r : Spec-R-Alg Γ δ x)
    {ps : _} {ps-d : Params-DAlg Δ γ δ ps} (ps-r : Params-R-Alg Δ ps-d x)
  → Ty-R-Alg A (Tm-DAlg t δ ps-d) x
CtorTm-R-Alg
  : ∀{Γ A f df x} (t : CtorTm Γ A) {γ : Spec-Alg Γ f} {δ : Spec-DAlg Γ γ df} (r : Spec-R-Alg Γ δ x)
  → Ctor-R-Alg A (CtorTm-DAlg t δ) x

Sub-R-Alg Id r p = p
Sub-R-Alg (Ext σ x) r p = Sub-R-Alg σ r p , Tm-R-Alg x r p
Sub-R-Alg Drop r p = proj₁ p
Sub-R-Alg (σ ∘ τ) r p = Sub-R-Alg τ r (Sub-R-Alg σ r p)
Sub-R-Alg (σ [ w ]ws) r p = Sub-R-Alg σ (Wk-R-Alg w r) p

Tm-R-Alg vz r ps-r = proj₂ ps-r
Tm-R-Alg vz1 r ps-r = proj₂ ps-r
Tm-R-Alg (vs t) r ps-r = Tm-R-Alg t r (proj₁ ps-r)
Tm-R-Alg (ext A x) r ps-r = tt
Tm-R-Alg (ctor x σ) r ps-r = CtorTm-R-Alg x r (Sub-R-Alg σ r ps-r)
Tm-R-Alg (app t) r {ps = _ , n} (ps-r , _) = Tm-R-Alg t r ps-r n
Tm-R-Alg (lam t) r ps-r = λ n → Tm-R-Alg t r (ps-r , _)
Tm-R-Alg (t [ σ ]tm) r ps-r = Tm-R-Alg t r (Sub-R-Alg σ r ps-r)
Tm-R-Alg (t [ w ]tm') r ps-r = Tm-R-Alg t (Wk-R-Alg w r) ps-r
Tm-R-Alg (t [ w ]tm'-1) r ps-r = Tm-R-Alg t (Wk-R-Alg w r) ps-r
Tm-R-Alg (ctor-1 x σ) r ps-r = CtorTm-R-Alg x r (Sub-R-Alg σ r ps-r)
Tm-R-Alg (app-U t x) r p = tt

Base-R-Alg[]b' ty1 w a' = refl
Base-R-Alg[]b' (ty2 x) w a' = refl
{-# REWRITE Base-R-Alg[]b' #-}

CtorTm-R-Alg c r = r c

Ctor-R-Alg[]
  : ∀{Γ f df r} (C : Ctor Γ) (w : Wk Ω Γ)
     {γ : Spec-Alg Ω f} {δ : Spec-DAlg Ω γ df}
     {a : Ctor-Alg C (Wk-Alg w γ)} (a' : Ctor-DAlg C (Wk-Alg w γ) (Wk-DAlg w δ) a)
  → Ctor-R-Alg (C [ w ]c) a' r ≡ Ctor-R-Alg C a' r
Ctor-R-Alg[] (ctor Δ x) w a' = refl
{-# REWRITE Ctor-R-Alg[] #-}

Wk-R-Alg w x c = x (c [ w ]ctm)

