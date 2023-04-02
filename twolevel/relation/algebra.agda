{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

module relation.algebra where

open import lib hiding (Fam ; fst ; snd)
open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import predicate.algebra
open import hoas-postulated

RelTys : (f : Fam) → DFam f → Set
RelTys (A , B) (Aᴰ , Bᴰ) =
  ((a : STerm A) → STerm (Aᴰ a) → SType) ×
  ((a : STerm A) (aᴰ : STerm (Aᴰ a)) (b : STerm (B a)) → STerm (Bᴰ a aᴰ b) → SType)

module _ {F : Fam} {Fᴰ : DFam F} where

  Spec-R-Alg : (Γ : Spec) (γ : Spec-Alg Γ F) (δ : Spec-DAlg Γ γ Fᴰ) → RelTys F Fᴰ → Set
  Ctor-R-Alg : (A : Ctor Γ) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ}
               (a : STerm (Ctor-Alg A γ)) (aᴰ : STerm (Ctor-DAlg A γᴰ a)) → RelTys F Fᴰ → SType
  Params-R-Alg : (Δ : Params Γ) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ}
                 (p : _) → STerm (Params-DAlg Δ γᴰ p) → RelTys F Fᴰ → SType

  Ty-R-Alg : (A : Ty Γ Δ) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ}
             {p : _} {pᴰ : STerm (Params-DAlg Δ γᴰ p)}
             (a : _) (aᴰ : STerm (Ty-DAlg A γᴰ pᴰ a)) → RelTys F Fᴰ → SType
  
  Base-R-Alg : (A : Base Γ Δ) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ}
               {p : _} {pᴰ : STerm (Params-DAlg Δ γᴰ p)}
               (a : _) (aᴰ : STerm (Base-DAlg A γᴰ pᴰ a)) → RelTys F Fᴰ → SType

  -- Spec-R-Alg init γ δ r = ⊤
  -- Spec-R-Alg (Γ ‣ C) (γ , c) (γᴰ , cᴰ) r = Spec-R-Alg Γ γ γᴰ r × STerm (Ctor-R-Alg C c cᴰ r)

  Ctor-R-Alg (ctor Δ B) {γᴰ = γᴰ} c cᴰ R =
    PiU (Params-Alg Δ _) λ p → PiU (Params-DAlg Δ γᴰ p) λ pᴰ
      → Params-R-Alg Δ p pᴰ R =>U Base-R-Alg B (app c p) (cᴰ $ p $ pᴰ) R

  Params-R-Alg ● p pᴰ _ = 𝟙U
  Params-R-Alg (Δ ‣‣ A) p pᴰ R =
    PairU (Params-R-Alg Δ (fst p) (fst pᴰ) R) (Ty-R-Alg A (snd p) (snd pᴰ) R)
  Params-R-Alg (Δ [ w ]p) = Params-R-Alg Δ

  Ty-R-Alg (ext A) a aᴰ _ = 𝟙U
  Ty-R-Alg (base b) = Base-R-Alg b
  Ty-R-Alg (Π A B) f fᴰ R = PiU A (λ x → Base-R-Alg B (app f x) (app fᴰ x) R)
  Ty-R-Alg (A [ σ ]) = Ty-R-Alg A
  Ty-R-Alg (A [ w ]') = Ty-R-Alg A

  Base-R-Alg ty1 a aᴰ R = proj₁ R a aᴰ
  Base-R-Alg (ty2 t) {γᴰ = γᴰ} {pᴰ = pᴰ} b bᴰ R = proj₂ R _ (Tm-DAlg t γᴰ pᴰ) b bᴰ

  Base-R-Alg[]b'
    : (A : Base Γ Δ) (w : Wk Ω Γ) {γ : Spec-Alg Ω F} {γᴰ : Spec-DAlg _ γ Fᴰ}
      (p : _) (pᴰ : STerm (Params-DAlg Δ (Wk-DAlg w γᴰ) p))
      (a : _) (aᴰ : STerm (Base-DAlg A _ pᴰ a))
    → Base-R-Alg (A [ w ]b') a aᴰ ≡ Base-R-Alg A a aᴰ
  Base-R-Alg[]b' ty1 w p pᴰ a aᴰ = refl
  Base-R-Alg[]b' (ty2 x) w p pᴰ a aᴰ = refl
  {-# REWRITE Base-R-Alg[]b' #-}

  Wk-R-Alg : ∀{R}(w : Wk Γ Ω) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ}
           → Spec-R-Alg Γ γ γᴰ R → Spec-R-Alg Ω _ (Wk-DAlg w γᴰ) R
  Sub-R-Alg : ∀{R}(σ : Sub {Γ} Δ ∇) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ} (r : Spec-R-Alg Γ γ γᴰ R)
            → {p : _} {pᴰ : STerm (Params-DAlg Δ γᴰ p)}
            → STerm (Params-R-Alg Δ p pᴰ R) → STerm (Params-R-Alg ∇ (Sub-Alg σ p) (Sub-DAlg σ pᴰ) R)
  Tm-R-Alg
    : ∀{R}(t : Tm Γ Δ A) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ} (r : Spec-R-Alg Γ γ γᴰ R)
      {p : _} {pᴰ : STerm (Params-DAlg Δ γᴰ p)} (p-r : STerm (Params-R-Alg Δ p pᴰ R))
    → STerm (Ty-R-Alg A _ (Tm-DAlg t γᴰ pᴰ) R)
  CtorTm-R-Alg
    : ∀{R}(c : CtorTm Γ C) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ} (r : Spec-R-Alg Γ γ γᴰ R)
    → STerm (Ctor-R-Alg C (CtorTm-Alg c γ) (CtorTm-DAlg c γᴰ) R)

  -- Wk-R-Alg Id p = p
  -- Wk-R-Alg Drop p = proj₁ p
  -- Wk-R-Alg (w ∘w w') p = Wk-R-Alg w' (Wk-R-Alg w p)
  
  Sub-R-Alg Id r p = p
  Sub-R-Alg (Ext σ x) r p = pair (Sub-R-Alg σ r p) (Tm-R-Alg x r p)
  Sub-R-Alg Drop r p = fst p
  Sub-R-Alg (σ ∘ τ) r p = Sub-R-Alg τ r (Sub-R-Alg σ r p)
  Sub-R-Alg (σ [ w ]ws) r p = Sub-R-Alg σ (Wk-R-Alg w r) p

  Tm-R-Alg vz r ps-r = snd ps-r
  Tm-R-Alg vz1 r ps-r = snd ps-r
  Tm-R-Alg (vs t) r ps-r = Tm-R-Alg t r (fst ps-r)
  Tm-R-Alg (ext A x) r ps-r = star
  Tm-R-Alg (ctor x σ) r ps-r = CtorTm-R-Alg x r $ _ $ _ $ Sub-R-Alg σ r ps-r
  Tm-R-Alg (App t) r {p} p-r = Tm-R-Alg t r (fst p-r) $ snd p
  Tm-R-Alg (Lam t) r p-r = lam (λ x → Tm-R-Alg t r (pair p-r star))
  Tm-R-Alg (t [ σ ]tm) r ps-r = Tm-R-Alg t r (Sub-R-Alg σ r ps-r)
  Tm-R-Alg (t [ w ]tm') r ps-r = Tm-R-Alg t (Wk-R-Alg w r) ps-r
  Tm-R-Alg (t [ w ]tm'-1) r ps-r = Tm-R-Alg t (Wk-R-Alg w r) ps-r
  Tm-R-Alg (ctor-1 x σ) r ps-r = CtorTm-R-Alg x r $ _ $ _ $ Sub-R-Alg σ r ps-r
  Tm-R-Alg (App-U t x) r p-r = star

  -- CtorTm-R-Alg (v0c {A = ctor _ _}) r = proj₂ r
  -- CtorTm-R-Alg (dropc {Γ = Γ} {A = ctor _ _} t) r = CtorTm-R-Alg t (proj₁ r)
  -- CtorTm-R-Alg (_[_]ctm {A = ctor _ _} c w) r = CtorTm-R-Alg c (Wk-R-Alg w r)

  Spec-R-Alg Γ γ γᴰ R = ∀{C} (c : CtorTm Γ C) → STerm (Ctor-R-Alg C (CtorTm-Alg c γ) (CtorTm-DAlg c γᴰ) R)

  Wk-R-Alg = λ w x c → x (c [ w ]ctm)

  CtorTm-R-Alg = λ c r → r c

  
  -- Spec-R-Alg' : (Γ : Spec) (γ : Spec-Alg Γ F) (δ : Spec-DAlg Γ γ Fᴰ) → RelTys F Fᴰ → Set
  -- Spec-R-Alg' Γ γ γᴰ R = ∀{C} (c : CtorTm Γ C) → STerm (Ctor-R-Alg C (CtorTm-Alg c γ) (CtorTm-DAlg c γᴰ) R)

  -- Ctor-R-Alg-[] : {C : Ctor Γ} (w : Wk Ω Γ) {γ : Spec-Alg _ F} {γᴰ : Spec-DAlg Ω γ Fᴰ}
  --               → Ctor-R-Alg (C [ w ]c) {γᴰ = γᴰ} ≡ Ctor-R-Alg C
  -- Ctor-R-Alg-[] {C = ctor Δ x} w = refl
  -- {-# REWRITE Ctor-R-Alg-[] #-}

  -- to-Spec-R-Alg : ∀ Γ {m} {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ}
  --               → Spec-R-Alg' Γ γ γᴰ m → Spec-R-Alg Γ γ γᴰ m
  -- to-Spec-R-Alg init r = tt
  -- to-Spec-R-Alg (Γ ‣ C) r = (to-Spec-R-Alg Γ (λ c → r (c [ Drop ]ctm))) , r v0c

  -- CtorTm-R-Alg
  --   : ∀{R}(c : CtorTm Γ C) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ} (r : Spec-R-Alg Γ γ γᴰ R)
  --   → STerm (Ctor-R-Alg C (CtorTm-Alg c γ) (CtorTm-DAlg c γᴰ) R)

  -- CtorTm-R-Alg'-≡
  --   : ∀{R}(c : CtorTm Γ C) {γ : Spec-Alg Γ F} {γᴰ : Spec-DAlg Γ γ Fᴰ} (r : Spec-R-Alg' Γ γ γᴰ R)
  --   → CtorTm-R-Alg c (to-Spec-R-Alg _ r) ≡ r c
  -- CtorTm-R-Alg'-≡ v0c r = refl
  -- CtorTm-R-Alg'-≡ (dropc c) r = trans (CtorTm-R-Alg'-≡ c (λ c₁ → r (c₁ [ Drop ]ctm))) {!!}
  -- CtorTm-R-Alg'-≡ (c [ w ]ctm) r = {!trans (CtorTm-R-Alg'-≡ c ?) ?!}
