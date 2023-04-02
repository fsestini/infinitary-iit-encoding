{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

module erased.initial.algebra-small where

open import lib hiding (fst ; snd)
open import IIT.spec
open import IIT.algebra
open import hoas-postulated

Fam₀ : Set
Fam₀ = SType × SType

DFam₀ : Fam₀ → Set
DFam₀ (A , B) = (STerm A -> SType) × (STerm B -> SType)

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

to-Spec₀-Alg' : ∀ {Γ F} → Spec₀-Alg Γ F → Spec₀-Alg' Γ F
to-Spec₀-Alg' γ c = CtorTm₀-Alg c γ

-- postulate
--   to-Spec₀-Alg-lemma :
--     ∀ {F} Γ C (c : CtorTm Γ C) (γ : Spec₀-Alg' Γ F)
--     → CtorTm₀-Alg c (to-Spec₀-Alg γ) ≡ γ c
-- {-# REWRITE to-Spec₀-Alg-lemma #-}

-- to-Spec₀-Alg-lemma _ _ v0c γ = refl
-- to-Spec₀-Alg-lemma _ _ (dropc c) γ = {!ih!}
--   where ih = to-Spec₀-Alg-lemma _ _ c λ x → γ (x [ Drop ]ctm)
-- to-Spec₀-Alg-lemma _ _ (c [ w ]ctm) γ = {!!}

module _ {F₀} where

  Spec₀-DAlg : ∀ Γ (γ : Spec₀-Alg Γ F₀) → DFam₀ F₀ → Set
  Spec₀-DAlg' : ∀ Γ (γ : Spec₀-Alg' Γ F₀) → DFam₀ F₀ → Set
  Ctor₀-DAlg : (A : Ctor Γ) -> STerm (Ctor₀-Alg A F₀) -> DFam₀ F₀ → SType
  Ty₀-DAlg : (A : Ty Γ Δ) → STerm (Ty₀-Alg A F₀) -> DFam₀ F₀ → SType
  Base₀-DAlg : (A : Base Γ Δ) → STerm (Base₀-Alg A F₀) -> DFam₀ F₀ → SType
  Params₀-DAlg : (Δ : Params Γ) → STerm (Params₀-Alg Δ F₀) -> DFam₀ F₀ → SType

  Spec₀-DAlg Γ γ F₀ᴰ =
    (∀{A} (c : CtorTm Γ A) → STerm (Ctor₀-DAlg A (CtorTm₀-Alg c γ) F₀ᴰ))
  
  Spec₀-DAlg' Γ γ x = ∀{C} (c : CtorTm Γ C) → STerm (Ctor₀-DAlg C (γ c) x)

  -- Spec₀-DAlg' init γ x = ⊤
  -- Spec₀-DAlg' (Γ ‣ C) γ x =
  --     Spec₀-DAlg' Γ (λ c → γ (dropc c)) x
  --   × STerm (Ctor₀-DAlg C (γ v0c) x)

  Ctor₀-DAlg (ctor Δ A) f F₀ᴰ =
    PiU (Params₀-Alg Δ F₀) λ p → Params₀-DAlg Δ p F₀ᴰ =>U Base₀-DAlg A (app f p) F₀ᴰ
  
  Ty₀-DAlg (ext X) x _ = X
  Ty₀-DAlg (base b) = Base₀-DAlg b
  Ty₀-DAlg (Π A B) y F₀ᴰ = PiU A λ n → Base₀-DAlg B (app y n) F₀ᴰ
  Ty₀-DAlg (A [ _ ]) = Ty₀-DAlg A
  Ty₀-DAlg (A [ _ ]') = Ty₀-DAlg A
  
  Params₀-DAlg ● h _ = 𝟙U
  Params₀-DAlg (Δ ‣‣ A) p F₀ᴰ = PairU (Params₀-DAlg Δ (fst p) F₀ᴰ) (Ty₀-DAlg A (snd p) F₀ᴰ)
  Params₀-DAlg (Δ [ _ ]p) = Params₀-DAlg Δ
  
  Base₀-DAlg ty1 a F₀ᴰ = proj₁ F₀ᴰ a
  Base₀-DAlg (ty2 _) a F₀ᴰ = proj₂ F₀ᴰ a
  
  -- Spec₀-DAlg' Γ γ D = ∀ {C} (c : CtorTm Γ C) → STerm (Ctor₀-DAlg C (γ c) D)

  -- to-Spec₀-DAlg : ∀ D Γ (γ : Spec₀-Alg' Γ F₀) → Spec₀-DAlg' Γ γ D
  --               → Spec₀-DAlg Γ (to-Spec₀-Alg γ) D
  -- to-Spec₀-DAlg D Γ γ γd c = γd c

  Spec₀-DAlg-ind : ∀ Γ (γ : Spec₀-Alg Γ F₀) → DFam₀ F₀ → Set
  Spec₀-DAlg-ind init γ D = ⊤
  Spec₀-DAlg-ind (Γ ‣ C) (γ , c) D = Spec₀-DAlg-ind Γ γ D × STerm (Ctor₀-DAlg C c D)

module _ {F₀} {F₀ᴰ : DFam₀ F₀} where

  CtorTm₀-DAlg : (c : CtorTm Γ C) {γ₀ : Spec₀-Alg Γ F₀} (γd₀ : Spec₀-DAlg Γ γ₀ F₀ᴰ)
               → STerm (Ctor₀-DAlg C (CtorTm₀-Alg c γ₀) F₀ᴰ)
  -- CtorTm₀-DAlg' : (c : CtorTm Γ C) {γ₀ : Spec₀-Alg' Γ F₀} (γd₀ : Spec₀-DAlg' Γ γ₀ F₀ᴰ)
  --              → STerm (Ctor₀-DAlg C (γ₀ c) F₀ᴰ)
  -- Wk₀-DAlg : ∀{γ₀} (w : Wk Ω Γ) → Spec₀-DAlg Ω γ₀ F₀ᴰ
  --          → Spec₀-DAlg Γ (Wk₀-Alg w γ₀) F₀ᴰ
  -- Wk₀-DAlg' : {γ₀ : Spec₀-Alg' Ω F₀} (w : Wk Ω Γ) → Spec₀-DAlg' Ω γ₀ F₀ᴰ
  --          → Spec₀-DAlg' Γ (λ x → γ₀ (x [ w ]ctm)) F₀ᴰ
  -- Wk₀-DAlg-ind : ∀{γ₀ : Spec₀-Alg Ω F₀} (w : Wk Ω Γ) → Spec₀-DAlg-ind Ω γ₀ F₀ᴰ
  --          → Spec₀-DAlg-ind Γ (Wk₀-Alg w γ₀) F₀ᴰ
  -- Sub₀-DAlg : ∀{γ₀} (σ : Sub {Γ} Δ ∇) → Spec₀-DAlg Γ γ₀ F₀ᴰ
  --           → {p₀ : STerm (Params₀-Alg Δ F₀)} → STerm (Params₀-DAlg Δ p₀ F₀ᴰ)
  --           → STerm (Params₀-DAlg ∇ (Sub₀-Alg σ γ₀ p₀) F₀ᴰ)

  CtorTm₀-DAlg c γd₀ = γd₀ c

   -- CtorTm₀-DAlg-ind c {!!}

  -- Sub₀-DAlg Id x p = p
  -- Sub₀-DAlg (Ext σ t) x p = pair (Sub₀-DAlg σ x p) (Tm₀-DAlg t x p)
  -- Sub₀-DAlg Drop x p = fst p
  -- Sub₀-DAlg (σ ∘ τ) x p = Sub₀-DAlg τ x (Sub₀-DAlg σ x p)
  -- Sub₀-DAlg (σ [ w ]ws) x p = Sub₀-DAlg σ (Wk₀-DAlg w x) p
  
  -- Tm₀-DAlg vz δ p = snd p
  -- Tm₀-DAlg vz1 δ p = snd p
  -- Tm₀-DAlg (vs t) δ p = Tm₀-DAlg t δ (fst p)
  -- Tm₀-DAlg (ext A x) δ p = x
  -- Tm₀-DAlg (ctor x σ) δ p = CtorTm₀-DAlg x δ $ _ $ Sub₀-DAlg σ δ p
  -- Tm₀-DAlg (ctor-1 x σ) δ p = CtorTm₀-DAlg x δ $ _ $ Sub₀-DAlg σ δ p
  -- Tm₀-DAlg (App t) δ {p₀} p = app (Tm₀-DAlg t δ (fst p)) (snd p₀)
  -- Tm₀-DAlg (Lam t) δ p = lam λ n → Tm₀-DAlg t δ (pair p n)
  -- Tm₀-DAlg (t [ σ ]tm) δ p = Tm₀-DAlg t δ (Sub₀-DAlg σ δ p)
  -- Tm₀-DAlg (t [ w ]tm') δ p = Tm₀-DAlg t (Wk₀-DAlg w δ) p
  -- Tm₀-DAlg (t [ w ]tm'-1) δ p = Tm₀-DAlg t (Wk₀-DAlg w δ) p
  -- Tm₀-DAlg (App-U t f) γd₀ pd₀ = app f (Tm₀-DAlg t γd₀ pd₀)

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
  
  -- Wk₀-DAlg w f c = f (c [ w ]ctm)

  -- CtorTm₀-DAlg-ind
  --   : (c : CtorTm Γ C) {γ₀ : Spec₀-Alg Γ F₀} (γd₀ : Spec₀-DAlg-ind Γ γ₀ F₀ᴰ)
  --   → STerm (Ctor₀-DAlg C (CtorTm₀-Alg c γ₀) F₀ᴰ)
  -- CtorTm₀-DAlg-ind v0c γd₀ = proj₂ γd₀
  -- CtorTm₀-DAlg-ind (dropc c) γd₀ = CtorTm₀-DAlg-ind c (proj₁ γd₀)
  -- CtorTm₀-DAlg-ind (c [ w ]ctm) γd₀ = CtorTm₀-DAlg-ind c (Wk₀-DAlg-ind w γd₀)


  -- Wk₀-DAlg' Wk.Id x = x
  -- Wk₀-DAlg' Drop x = proj₁ x
  -- Wk₀-DAlg' (w ∘w w') x = Wk₀-DAlg' w' (Wk₀-DAlg' w x)

  -- CtorTm₀-DAlg' v0c γd₀ = proj₂ γd₀
  -- CtorTm₀-DAlg' (dropc c) γd₀ = CtorTm₀-DAlg' c (proj₁ γd₀)
  -- CtorTm₀-DAlg' (c [ w ]ctm) γd₀ = CtorTm₀-DAlg' c (Wk₀-DAlg' w γd₀)

  -- Wk₀-DAlg-ind Wk.Id x = x
  -- Wk₀-DAlg-ind Drop x = proj₁ x
  -- Wk₀-DAlg-ind (w ∘w w') x = Wk₀-DAlg-ind w' (Wk₀-DAlg-ind w x)

{-# REWRITE [Id]p [Id]b' [∘]p-≡ [∘]b'-≡ #-}

-- postulate
--   [Id]ctm-≡ : ∀{Γ C} {c : CtorTm Γ C} → c [ Wk.Id ]ctm ≡ c
--   [∘]ctm-≡ : ∀{Γ Ω ∇} (w : Wk Γ Ω) (w' : Wk Ω ∇) (C : Ctor ∇) (c : CtorTm ∇ C)
--            → c [ w' ]ctm [ w ]ctm ≡ c [ w ∘w w' ]ctm
--   [Drop]ctm-≡ : ∀{C'} (c : CtorTm Γ C) → c [ Drop {Γ} {C'} ]ctm ≡ dropc c

{-# REWRITE [Id]ctm-≡ [∘]ctm-≡ [Drop]ctm-≡ #-}

to-Spec₀-Alg-wk
  : ∀{F} (w : Wk Γ Ω) (γ : Spec₀-Alg' Γ F)
  → Wk₀-Alg w (to-Spec₀-Alg γ) ≡ to-Spec₀-Alg λ c → γ (c [ w ]ctm)
to-Spec₀-Alg-wk Wk.Id γ = refl
to-Spec₀-Alg-wk Drop γ = refl
to-Spec₀-Alg-wk (w ∘w w') γ =
  trans (cong (Wk₀-Alg w') (to-Spec₀-Alg-wk w γ)) (to-Spec₀-Alg-wk w' _)
{-# REWRITE to-Spec₀-Alg-wk #-}

module _ {F₀} {F₀ᴰ : DFam₀ F₀} where

  CtorTm₀-Alg-≡
    : (c : CtorTm Γ C) (γ₀ : Spec₀-Alg' Γ F₀)
    → CtorTm₀-Alg c (to-Spec₀-Alg γ₀) ≡ γ₀ c
  CtorTm₀-Alg-≡ v0c γ₀ = refl
  CtorTm₀-Alg-≡ (dropc c) γ₀ = CtorTm₀-Alg-≡ c λ x → γ₀ (dropc x)
  CtorTm₀-Alg-≡ (c [ w ]ctm) γ₀ = CtorTm₀-Alg-≡ c _
  {-# REWRITE CtorTm₀-Alg-≡ #-}

  to-Spec₀-DAlg' : ∀ Γ (γ : Spec₀-Alg' Γ F₀)
                 → Spec₀-DAlg Γ (to-Spec₀-Alg γ) F₀ᴰ
                 → Spec₀-DAlg' Γ γ F₀ᴰ
  to-Spec₀-DAlg' Γ γ γd c = γd c
  -- to-Spec₀-DAlg' init γ γd = tt
  -- to-Spec₀-DAlg' (Γ ‣ C) γ γd =
  --   to-Spec₀-DAlg' Γ _ (λ c → γd (dropc c)) , γd v0c

-- CtorTm₀-DAlg'-≡
--   : ∀{F₀ F₀ᴰ} (c : CtorTm Γ C) (γ₀ : Spec₀-Alg' Γ F₀)
--   → (γd₀ : Spec₀-DAlg Γ (to-Spec₀-Alg γ₀) F₀ᴰ)
--   → CtorTm₀-DAlg' c (to-Spec₀-DAlg' Γ γ₀ γd₀)
--   ≡  CtorTm₀-DAlg {F₀} {F₀ᴰ} c {to-Spec₀-Alg γ₀} γd₀
-- CtorTm₀-DAlg'-≡ v0c γ₀ γd₀ = refl
-- CtorTm₀-DAlg'-≡ (dropc c) γ₀ γd₀ = CtorTm₀-DAlg'-≡ c _ (λ c' → γd₀ (dropc c'))
-- CtorTm₀-DAlg'-≡ (c [ w ]ctm) γ₀ γd₀ = {!CtorTm₀-DAlg'-≡ c ? ?!}
-- {-# REWRITE CtorTm₀-DAlg'-≡ #-}

