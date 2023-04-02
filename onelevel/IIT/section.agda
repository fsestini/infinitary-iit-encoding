{-# OPTIONS --prop --rewriting #-}

module IIT.section where

open import lib
open import IIT.spec
open import IIT.algebra

Morphᴰ : (f : Fam) → DFam f → Set
Morphᴰ (C , T) (Cᴰ , Tᴰ) = Σ ((c : C) → Cᴰ c) λ m → ∀{c} (t : T c) → Tᴰ c (m c) t

Spec-Sect : ∀{f df} (Γ : Spec) (γ : Spec-Alg Γ f) → Spec-DAlg Γ γ df → Morphᴰ f df → Prop
Ctor-Sect : ∀{f df Γ} (A : Ctor Γ) {γ : _} {δ : Spec-DAlg Γ γ df}
                (a : _) → Ctor-DAlg A γ δ a → (m : Morphᴰ f df) → Spec-Sect Γ γ δ m → Prop
Params-Sect : ∀{f df Γ} (Δ : Params Γ) {γ : _} {δ : Spec-DAlg Γ γ df}
            → (p : Params-Alg Δ γ) → (m : Morphᴰ f df) (c : Spec-Sect Γ γ δ m)
            → Params-DAlg Δ γ δ p
Ty-Sect : ∀{f df Γ Δ} (A : Ty Γ Δ) {γ : _} {δ : Spec-DAlg Γ γ df}
            {p : _} (a : Ty-Alg A γ p) → (m : Morphᴰ f df) (c : Spec-Sect Γ γ δ m)
            → Ty-DAlg A δ (Params-Sect Δ p m c) a
Base-Sect : ∀{f df Γ Δ} (A : Base Γ Δ) {γ : _} {δ : Spec-DAlg Γ γ df} {p : _}
            (a : Base-Alg A γ p) (m : Morphᴰ f df) (c : Spec-Sect Γ γ δ m)
            → Base-DAlg A δ (Params-Sect Δ p m c) a
Tm-Sect : ∀{f df Γ Δ A} (t : Tm Γ Δ A) {γ : _} {δ : Spec-DAlg Γ γ df} {p : _}
            (m : Morphᴰ f df) (c : Spec-Sect Γ γ δ m)
        → Ty-Sect A (Tm-Alg t γ p) m c ≡ Tm-DAlg t δ (Params-Sect Δ p m c)
Wk-Sect : ∀{f df Ω Γ} (w : Wk Ω Γ) {γ : _} {δ : Spec-DAlg _ γ df} (m : Morphᴰ f df)
        → Spec-Sect Ω γ δ m → Spec-Sect Γ _ (Wk-DAlg w δ) m

CtorTm-Sect : ∀{f df Γ C} (t : CtorTm Γ C)
               {γ : _} {δ : Spec-DAlg Γ γ df} (m : Morphᴰ f df) (c : Spec-Sect Γ γ δ m)
            → Ctor-Sect C _ (CtorTm-DAlg t δ) m c
Sub-Sect : ∀{f df Γ Δ ∇} (σ : Sub Δ ∇) {γ : _} {δ : Spec-DAlg Γ γ df} (p : Params-Alg Δ γ)
           (m : Morphᴰ f df) (c : Spec-Sect Γ γ δ m)
         → Params-Sect ∇ (Sub-Alg σ p) m c ≡ Sub-DAlg σ (Params-Sect Δ p m c)
-- Sub-Sect' : ∀{f df Γ Δ ∇} (σ : Sub Δ ∇) {γ : _} {δ : Spec-DAlg Γ γ df} (p : Params-Alg Δ γ)
--            (m : Morphᴰ f df) (c : Spec-Sect Γ γ δ m)
--          → Params-Sect ∇ (Sub-Alg σ p) m c ≡ Sub-DAlg σ (Params-Sect Δ p m c)

Spec-Sect init γ δ m = ⊤p
Spec-Sect (Γ ‣ A) (γ , a) (δ , a') m = ΣP (Spec-Sect Γ γ δ m) (Ctor-Sect A a a' m)

Wk-Sect Id m x = x
Wk-Sect Drop m x = fstP x
Wk-Sect (w ∘w w') m x = Wk-Sect w' m (Wk-Sect w m x)

Ctor-Sect (ctor Δ A) a a' m c =
  (p : _) → Base-Sect A (a p) m c ≡p a' (Params-Sect Δ p m c)

Params-Sect ● p x _ = tt
Params-Sect (Δ ‣‣ A) (p , a) m c = Params-Sect Δ p m c , Ty-Sect A a m c
Params-Sect (Δ [ x ]p) p m c = Params-Sect Δ p m (Wk-Sect x m c)

Ty-Sect (ext A) a x c = tt
Ty-Sect (base b) a x c = Base-Sect b a x c
Ty-Sect (Π A B) f x c = λ n → Base-Sect B (f n) x c
Ty-Sect (A [ σ ]) {p = p} a x c =
  subst' (λ z → Ty-DAlg A _ z a) (Sub-Sect σ p x c) (Ty-Sect A a x c)
Ty-Sect (A [ w ]') {δ = δ} {p = p} a x c = Ty-Sect A a x (Wk-Sect w x c)

Sub-Sect Id _ _ _ = refl
Sub-Sect (Ext σ x) p m c = to-≡ (Σ-≡p (from-≡ (Sub-Sect σ p m c)) (from-≡ (Tm-Sect x m c)))
Sub-Sect Drop p m c = refl
Sub-Sect (σ ∘ τ) p m c = trans (Sub-Sect τ _ m c) (cong (Sub-DAlg τ) (Sub-Sect σ p m c))
Sub-Sect (σ [ w ]ws) p m c = Sub-Sect σ p m (Wk-Sect w m c)

-- Sub-Sect' σ p m c = to-≡ (Sub-Sect σ p m c)
-- {-# REWRITE Sub-Sect' #-}
{-# REWRITE Sub-Sect #-}

Base-Sect[]b'
  : ∀{Ω Γ Δ f df} (A : Base Γ Δ) (w : Wk Ω Γ)
    {γ : _} {δ : Spec-DAlg Ω γ df} {p : _}
    (a : Base-Alg A _ p) → (m : Morphᴰ f df) (c : Spec-Sect Ω _ δ m)
  → Base-Sect (A [ w ]b') a m c ≡ Base-Sect A a m (Wk-Sect w _ c)

{-# TERMINATING #-}
Base-Sect ty1 a x _ = proj₁ x a
Base-Sect {df = df} (ty2 t) a x c =
  subst' (λ z → proj₂ df _ z a) (Tm-Sect t x c) (proj₂ x a)

Tm-Sect vz m γ = refl
Tm-Sect vz1 m γ = refl
Tm-Sect (vs t) m = λ x → Tm-Sect t m x
Tm-Sect (ext A x) m _ = refl
Tm-Sect (ctor x σ) {p = p} m c = to-≡ (CtorTm-Sect x m c (Sub-Alg σ p))
Tm-Sect (lam t) m c = funext (λ n → Tm-Sect t m c)
Tm-Sect (app t) {p = p , n} m c = cong (λ f → f n) (Tm-Sect t m c)
Tm-Sect (t [ σ ]tm) {p = p} m c = Tm-Sect t {p = Sub-Alg σ p} m c
Tm-Sect (t [ w ]tm') m c = Tm-Sect t m (Wk-Sect w m c)
Tm-Sect (ctor-1 x σ) m c = to-≡ (CtorTm-Sect x m c (Sub-Alg σ _))
Tm-Sect (t [ w ]tm'-1) m c = Tm-Sect t m (Wk-Sect w m c)
Tm-Sect (app-U x f) m c = refl

Base-Sect[]b' ty1 w a m c = refl
Base-Sect[]b' (ty2 x) w a m c = refl
{-# REWRITE Base-Sect[]b' #-}

CtorTm-Sect (v0c {A = ctor Δ x}) m c = sndP c
CtorTm-Sect (dropc {A = ctor Δ x} t) m c = CtorTm-Sect t m (fstP c)
CtorTm-Sect (_[_]ctm {A = ctor Δ x} t w) m c = CtorTm-Sect t m (Wk-Sect w m c)

Ctor-Sect[]
  : ∀{f df} (w : Wk Ω Γ) (A : Ctor Γ) {γ : _} {δ : Spec-DAlg _ γ df}
    (a : _) (ad : Ctor-DAlg A _ (Wk-DAlg w δ) a) → (m : Morphᴰ f df) (cs : Spec-Sect Ω γ δ m)
  → Ctor-Sect (A [ w ]c) a ad m cs ≡ Ctor-Sect A _ ad m (Wk-Sect w m cs)
Ctor-Sect[] w (ctor Δ x) a ad m cs = refl
{-# REWRITE Ctor-Sect[] #-}

