{-# OPTIONS --prop --rewriting #-}

module erased.section where

open import Agda.Primitive using (Setω)
open import lib
open import IIT.spec
open import IIT.algebra
open import erased.algebra

Morph₀ : (F₀ : Fam₀) → DFam₀ {i} F₀ → Set i
Morph₀ (A , A') (B , B') = ((a : A) → B a) × ((a : A') → B' a)

Ty₀-Sect : (A : Ty Γ Δ) (a : Ty₀-Alg A F₀) → Morph₀ F₀ F₀ᴰ → Ty₀-DAlg A F₀ᴰ a
Base₀-Sect : (A : Base Γ Δ) (a : Base₀-Alg A F₀) → Morph₀ F₀ F₀ᴰ → Base₀-DAlg A F₀ᴰ a
Params₀-Sect : (Δ : Params Γ) → (p : Params₀-Alg Δ F₀) → Morph₀ F₀ F₀ᴰ → Params₀-DAlg Δ F₀ᴰ p
Ctor₀-Sect : (A : Ctor Γ) (a : Ctor₀-Alg A F₀) → Ctor₀-DAlg A F₀ᴰ a → Morph₀ {i} F₀ F₀ᴰ → Prop i

Ty₀-Sect (ext A) a x = _ -- liftSet a
Ty₀-Sect (base B) a x = Base₀-Sect B a x
Ty₀-Sect (Π A B) f m n = Base₀-Sect B (f n) m
Ty₀-Sect (A [ _ ]) a x = Ty₀-Sect A a x
Ty₀-Sect (A [ _ ]') a x = Ty₀-Sect A a x

Base₀-Sect ty1 a m = proj₁ m a
Base₀-Sect (ty2 _) a m = proj₂ m a

Base₀-Sect[]b'
  : (A : Base Γ Δ) (w : Wk Ω Γ) (a : Base₀-Alg A F₀) (m : Morph₀ F₀ F₀ᴰ)
  → Base₀-Sect (A [ w ]b') a m ≡ Base₀-Sect A a m
Base₀-Sect[]b' ty1 w a m = refl
Base₀-Sect[]b' (ty2 x) w a m = refl
{-# REWRITE Base₀-Sect[]b' #-}

Params₀-Sect ● p m = tt
Params₀-Sect (Δ ‣‣ A) (p , a) m = Params₀-Sect Δ p m , Ty₀-Sect A a m
Params₀-Sect (Δ [ x ]p) p m = Params₀-Sect Δ p m

Ctor₀-Sect (ctor Δ A) c c' m = (p : _) → Base₀-Sect A (c p) m ≡p c' (Params₀-Sect Δ p m)

Ctor₀-Sect-[] : (w : Wk Ω Γ) (c : Ctor₀-Alg C F₀) (c' : Ctor₀-DAlg C F₀ᴰ c) (m : Morph₀ {i} F₀ F₀ᴰ)
              → Ctor₀-Sect (C [ w ]c) c c' m ≡ Ctor₀-Sect C c c' m
Ctor₀-Sect-[] {C = ctor Δ x} w c c' m = refl
{-# REWRITE Ctor₀-Sect-[] #-}

Spec₀-Sect : (Γ : Spec) (γ₀ : Spec₀-Alg Γ F₀) → Spec₀-DAlg Γ γ₀ F₀ᴰ → Morph₀ {i} F₀ F₀ᴰ → Prop i
Spec₀-Sect Γ γ δ m =
  ∀{C} (c : CtorTm Γ C) → Ctor₀-Sect C (CtorTm₀-Alg c γ) (CtorTm₀-DAlg c δ) m

Wk₀-Sect : ∀{X Y} (w : Wk Ω Γ) {γ : Spec₀-Alg _ X} {γ' : Spec₀-DAlg _ γ Y} {m : Morph₀ {i} X Y}
         → Spec₀-Sect Ω γ γ' m → Spec₀-Sect Γ (Wk₀-Alg w γ) (Wk₀-DAlg w γ') m
Wk₀-Sect w s c = s (c [ w ]ctm)

Sub₀-Sect : ∀{X Y} (σ : Sub ∇ Δ) {γ : Spec₀-Alg Γ X} {δ : Spec₀-DAlg Γ γ Y} {m : Morph₀ {i} X Y} (cs : Spec₀-Sect Γ γ δ m) (p : _)
          → Params₀-Sect Δ (Sub₀-Alg σ γ p) m ≡p Sub₀-DAlg σ δ (Params₀-Sect ∇ p m)

Tm₀-Sect : ∀{X Y} (t : Tm Γ Δ A) {γ : Spec₀-Alg Γ X} {δ : Spec₀-DAlg Γ γ Y} {m : Morph₀ {i} X Y} (cs : Spec₀-Sect Γ γ δ m) (p : _)
         → Ty₀-Sect A (Tm₀-Alg t γ p) m ≡p Tm₀-DAlg t δ (Params₀-Sect Δ p m)

Sub₀-Sect Id cs p = reflp
Sub₀-Sect (Ext σ x) cs p rewrite to-≡ (Sub₀-Sect σ cs p) = cong' (_ ,_) (Tm₀-Sect x cs p)
Sub₀-Sect Drop cs p = reflp
Sub₀-Sect (σ ∘ τ) cs p = trans' (Sub₀-Sect τ cs _) (cong' (Sub₀-DAlg τ _) (Sub₀-Sect σ cs _))
Sub₀-Sect (σ [ w ]ws) cs p = Sub₀-Sect σ (Wk₀-Sect w cs) p

Tm₀-Sect vz m p = reflp
Tm₀-Sect vz1 m p = reflp
Tm₀-Sect (vs t) m p = Tm₀-Sect t m _
Tm₀-Sect (ext A x) m p = reflp
Tm₀-Sect (ctor x σ) {δ = δ} cs p = trans' (cs x _) (cong' (CtorTm₀-DAlg x δ) (Sub₀-Sect σ cs p))
Tm₀-Sect (ctor-1 x σ) {δ = δ} cs p = trans' (cs x _) (cong' (CtorTm₀-DAlg x δ) (Sub₀-Sect σ cs p))
Tm₀-Sect (app t) m (p , n) = cong' (λ f → f n) (Tm₀-Sect t m p)
Tm₀-Sect (lam t) m p = funextp (λ n → Tm₀-Sect t m (p , n))
Tm₀-Sect (t [ σ ]tm) {δ = δ} m p = trans' (Tm₀-Sect t m _) (cong' (Tm₀-DAlg t δ) (Sub₀-Sect σ m p))
Tm₀-Sect (t [ w ]tm') m p = Tm₀-Sect t (Wk₀-Sect w m) p
Tm₀-Sect (t [ w ]tm'-1) m p = Tm₀-Sect t (Wk₀-Sect w m) p
Tm₀-Sect (app-U t x) m p = reflp

----------

is-initial₀ : ∀{Γ X} → Spec₀-Alg Γ X → Setω
is-initial₀ {X = X} γ = ∀{i} {Y : DFam₀ {i} X} (δ : Spec₀-DAlg _ γ Y) → Σp (Morph₀ _ Y) (Spec₀-Sect _ γ δ)
