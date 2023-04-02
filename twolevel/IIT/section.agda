{-# OPTIONS --prop --rewriting #-}

module IIT.section where

open import lib hiding (Fam ; fst ; snd)
open import hoas-postulated
open import IIT.spec
open import IIT.algebra

Morphᴰ : (f : Fam) → DFam f → Set
Morphᴰ (C , T) (Cᴰ , Tᴰ) =
  Σ (STerm (PiU C Cᴰ)) λ m → STerm (PiU C (λ c → PiU (T c) (Tᴰ c (app m c))))

module _ {F : Fam} {Fᴰ : DFam F} where

  Spec-Sect : (Γ : Spec) (γ : Spec-Alg Γ F) → Spec-DAlg Γ γ Fᴰ → Morphᴰ F Fᴰ → Prop
  Ctor-Sect : ∀{m γ γᴰ} (C : Ctor Γ)
              (a : STerm (Ctor-Alg C γ)) → STerm (Ctor-DAlg C γᴰ a)
            → Spec-Sect Γ γ γᴰ m → Prop
  Params-Sect : ∀{m γ γᴰ} (Δ : Params Γ) → Spec-Sect Γ γ γᴰ m
              → (p : STerm (Params-Alg Δ γ)) → STerm (Params-DAlg Δ γᴰ p)
  Ty-Sect : ∀{m γ γᴰ} (A : Ty Γ Δ) (c : Spec-Sect Γ γ γᴰ m) {p : _}
            (a : STerm (Ty-Alg A γ p)) → STerm (Ty-DAlg A γᴰ (Params-Sect Δ c p) a)
  Base-Sect : ∀{m γ γᴰ} (B : Base Γ Δ) (c : Spec-Sect Γ γ γᴰ m) {p : _}
              (a : STerm (Base-Alg B γ p)) → STerm (Base-DAlg B γᴰ (Params-Sect Δ c p) a)
  Tm-Sect : ∀{m γ γᴰ} (t : Tm Γ Δ A) (c : Spec-Sect Γ γ γᴰ m) (p : _)
          → Ty-Sect A c (Tm-Alg t γ p) ≡ Tm-DAlg t γᴰ (Params-Sect Δ c p)
  Wk-Sect : ∀{m γ γᴰ} (w : Wk Ω Γ) → Spec-Sect Ω γ γᴰ m → Spec-Sect Γ _ (Wk-DAlg w γᴰ) m
  
  CtorTm-Sect : ∀{m γ γᴰ} (t : CtorTm Γ C) (c : Spec-Sect Γ γ γᴰ m)
              → Ctor-Sect C (CtorTm-Alg t γ) (CtorTm-DAlg t γᴰ) c
  Sub-Sect : ∀{m γ γᴰ} (σ : Sub Δ ∇) (c : Spec-Sect Γ γ γᴰ m) (p : STerm (Params-Alg Δ γ))
           → Params-Sect ∇ c (Sub-Alg σ p) ≡ Sub-DAlg σ (Params-Sect Δ c p)
    
  Spec-Sect init γ δ _ = ⊤p
  Spec-Sect (Γ ‣ A) (γ , a) (δ , a') m = ΣP (Spec-Sect Γ γ δ m) (Ctor-Sect A a a')
  
  Wk-Sect Id x = x
  Wk-Sect Drop x = lib.fstP x
  Wk-Sect (w ∘w w') x = Wk-Sect w' (Wk-Sect w x)
  
  Ctor-Sect (ctor Δ A) a a' c =
    (p : _) → Base-Sect A c (app a p) ≡p app (app a' _) (Params-Sect Δ c p)
  
  Params-Sect ● p x = star
  Params-Sect (Δ ‣‣ A) c p = pair (Params-Sect Δ c (fst p)) (Ty-Sect A c (snd p))
  Params-Sect (Δ [ x ]p) c p = Params-Sect Δ (Wk-Sect x c) p

  -- {-# TERMINATING #-}
  Ty-Sect (ext x) c a = star
  Ty-Sect (base x) = Base-Sect x
  Ty-Sect (Π A B) c f = lam (λ a → Base-Sect B c (app f a))
  Ty-Sect (A [ σ ]) c {p = p} a =
    subst' (λ z → STerm (Ty-DAlg A _ z a)) (Sub-Sect σ c p) (Ty-Sect A c a)
  Ty-Sect (A [ w ]') c a = Ty-Sect A (Wk-Sect w c) a
  
  Sub-Sect Id _ _ = refl
  Sub-Sect (Ext σ x) c p = pair-≡ (Sub-Sect σ c p) (Tm-Sect x c p)
  Sub-Sect Drop p c = refl
  Sub-Sect (σ ∘ τ) c p = trans (Sub-Sect τ c _) (cong (Sub-DAlg τ) (Sub-Sect σ c p))
  Sub-Sect (σ [ w ]ws) c p = Sub-Sect σ (Wk-Sect w c) p
  {-# REWRITE Sub-Sect #-}
  
  {-# TERMINATING #-}
  Base-Sect {m = m} ty1 c a = app (proj₁ m) a
  Base-Sect {m = m} (ty2 t) c {p = p} a =
    subst' (λ z → STerm (proj₂ Fᴰ _ z a)) (Tm-Sect t c p) (proj₂ m $ _ $ a)
  
  Base-Sect[]b'
    : ∀{m γ γᴰ} (A : Base Γ Δ) (w : Wk Ω Γ) (c : Spec-Sect Ω γ γᴰ m)
      {p : _} (a : STerm (Base-Alg A _ p)) 
    → Base-Sect (A [ w ]b') c a ≡ Base-Sect A (Wk-Sect w c) a
  
  Base-Sect[]b' ty1 w c a = refl
  Base-Sect[]b' (ty2 x) w c a = refl
  {-# REWRITE Base-Sect[]b' #-}

  Tm-Sect vz γ p = refl
  Tm-Sect vz1 γ p = refl
  Tm-Sect (vs t) γ p = Tm-Sect t γ (fst p)
  Tm-Sect (ext A x) _ p = refl
  Tm-Sect (ctor x σ) c p = to-≡ (CtorTm-Sect x c (Sub-Alg σ p))
  Tm-Sect (Lam t) c p = cong lam (funext (λ x → Tm-Sect t c (pair p x)))
  Tm-Sect (App t) c p = cong (λ f → app f (snd p)) (Tm-Sect t c (fst p))
  Tm-Sect (t [ σ ]tm) c p = Tm-Sect t c (Sub-Alg σ p)
  Tm-Sect (t [ w ]tm') c p = Tm-Sect t (Wk-Sect w c) p
  Tm-Sect (ctor-1 x σ) c p = to-≡ (CtorTm-Sect x c (Sub-Alg σ p))
  Tm-Sect (t [ w ]tm'-1) c p = Tm-Sect t (Wk-Sect w c) p
  Tm-Sect (App-U t x) c p = refl
  
  CtorTm-Sect v0c c = lib.sndP c
  CtorTm-Sect (dropc t) c = CtorTm-Sect t (lib.fstP c)
  CtorTm-Sect (_[_]ctm t w) c = CtorTm-Sect t (Wk-Sect w c)
  
