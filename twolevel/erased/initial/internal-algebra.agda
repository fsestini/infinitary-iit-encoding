{-# OPTIONS --prop --rewriting #-}

module erased.initial.internal-algebra where

open import lib hiding (fst ; snd)
open import IIT.spec
open import IIT.algebra
open import erased.initial.algebra-small using (Fam₀ ; DFam₀)
open import hoas-postulated as H

postulate
  Base₀ : Type
  Ty₀ : Type
  Params₀ : Type

  ty1₀ : Term Base₀
  ty2₀ : Term Base₀

  base₀ : Term Base₀ → Term Ty₀
  ext₀ : SType → Term Ty₀
  Π₀ : (A : SType) → Term Base₀ → Term Ty₀

  ●₀ : Term Params₀
  _‣‣₀_ : Term Params₀ → Term Ty₀ → Term Params₀
  
  elim-Base₀ : (T : Term Base₀ → Type)
             → Term (T ty1₀) → Term (T ty2₀) → (b : Term Base₀) → Term (T b)

  elim-Ty₀ : (T : Term Ty₀ → Type)
           → (∀ b → Term (T (base₀ b)))
           → (∀ A → Term (T (ext₀ A)))
           → (∀ A B → Term (T (Π₀ A B)))
           → ∀ x → Term (T x)

  elim-Params₀ : (T : Term Params₀ → Type)
               → Term (T ●₀)
               → (∀ Δ A → Term (T Δ) → Term (T (Δ ‣‣₀ A)))
               → ∀ x → Term (T x)

module _ (T : Term Base₀ → Type) (h1 : Term (T ty1₀)) (h2 : Term (T ty2₀)) where

  postulate
    elim-Base₀-≡-ty1 : elim-Base₀ T h1 h2 ty1₀ ≡ h1
    elim-Base₀-≡-ty2 : elim-Base₀ T h1 h2 ty2₀ ≡ h2
  
  {-# REWRITE elim-Base₀-≡-ty1 elim-Base₀-≡-ty2 #-}

module _ (T : Term Ty₀ → Type) (h1 : ∀ b → Term (T (base₀ b))) (h2 : ∀ A → Term (T (ext₀ A))) (h3 : ∀ A B → Term (T (Π₀ A B))) where
  postulate
    elim-Ty₀-≡-b : ∀ b → elim-Ty₀ T h1 h2 h3 (base₀ b) ≡ h1 b
    elim-Ty₀-≡-e : ∀ x → elim-Ty₀ T h1 h2 h3 (ext₀ x) ≡ h2 x
    elim-Ty₀-≡-p : ∀ a b → elim-Ty₀ T h1 h2 h3 (Π₀ a b) ≡ h3 a b

  {-# REWRITE elim-Ty₀-≡-b elim-Ty₀-≡-e elim-Ty₀-≡-p #-}

module _ (T : Term Params₀ → Type) (h1 : Term (T ●₀)) (h2 : ∀ Δ A → Term (T Δ) → Term (T (Δ ‣‣₀ A))) where

  postulate
    elim-Params₀-≡-● : elim-Params₀ T h1 h2 ●₀ ≡ h1
    elim-Params₀-≡-‣‣ : ∀ Δ A → elim-Params₀ T h1 h2 (Δ ‣‣₀ A) ≡ h2 Δ A (elim-Params₀ T h1 h2 Δ)

  {-# REWRITE elim-Params₀-≡-● elim-Params₀-≡-‣‣ #-}

Ctor₀ : Type
Ctor₀ = Pair Params₀ Base₀

ctor₀ : Term Params₀ → Term Base₀ → Term Ctor₀
ctor₀ = pair

postulate
  Spec₀ : Type
  ◆₀ : Term Spec₀
  _‣₀_ : Term Spec₀ → Term Ctor₀ → Term Spec₀

  elim-Spec₀ : (T : Term Spec₀ → Type)
             → Term (T ◆₀)
             → (∀ Γ₀ C₀ → Term (T Γ₀) → Term (T (Γ₀ ‣₀ C₀)))
             → (Γ₀ : Term Spec₀) → Term (T Γ₀)

  Wk₀ : Term Spec₀ → Term Spec₀ → Type
  Id₀ : ∀ Γ₀ → Term (Wk₀ Γ₀ Γ₀)
  Drop₀ : ∀ Γ₀ C₀ → Term (Wk₀ (Γ₀ ‣₀ C₀) Γ₀)
  _·w₀_ : ∀{Γ₀ Ω₀ θ₀} → Term (Wk₀ Γ₀ Ω₀) → Term (Wk₀ Ω₀ θ₀) → Term (Wk₀ Γ₀ θ₀)

  elim-Wk₀ : (T : ∀{Γ Ω} → Term (Wk₀ Γ Ω) → Type)
             (h1 : ∀ Γ → Term (T (Id₀ Γ)))
             (h2 : ∀ Γ C → Term (T (Drop₀ Γ C)))
             (h3 : ∀{Γ₀ Ω₀ θ₀} (w : Term (Wk₀ Γ₀ Ω₀)) (w' : Term (Wk₀ Ω₀ θ₀))
                 → Term (T w) → Term (T w') → Term (T (w ·w₀ w')))
           → ∀ {Γ Ω} (w : Term (Wk₀ Γ Ω)) → Term (T w)

module _ (T : ∀{Γ Ω} → Term (Wk₀ Γ Ω) → Type)
         (h1 : ∀ Γ → Term (T (Id₀ Γ)))
         (h2 : ∀ Γ C → Term (T (Drop₀ Γ C)))
         (h3 : ∀{Γ₀ Ω₀ θ₀} (w : Term (Wk₀ Γ₀ Ω₀)) (w' : Term (Wk₀ Ω₀ θ₀))
                 → Term (T w) → Term (T w') → Term (T (w ·w₀ w')))
       where
  postulate
    elim-Wk₀-≡-Id : ∀ Γ → elim-Wk₀ T h1 h2 h3 (Id₀ Γ) ≡ h1 Γ
    elim-Wk₀-≡-Drop : ∀ Γ C → elim-Wk₀ T h1 h2 h3 (Drop₀ Γ C) ≡ h2 Γ C
    elim-Wk₀-≡-· : ∀{Γ₀ Ω₀ θ₀} (w : Term (Wk₀ Γ₀ Ω₀)) (w' : Term (Wk₀ Ω₀ θ₀))
                 → elim-Wk₀ T h1 h2 h3 (w ·w₀ w')
                 ≡ h3 w w' (elim-Wk₀ T h1 h2 h3 w) (elim-Wk₀ T h1 h2 h3 w')

  {-# REWRITE elim-Wk₀-≡-Id elim-Wk₀-≡-Drop elim-Wk₀-≡-· #-}

module _ (T : Term Spec₀ → Type) (h1 : Term (T ◆₀)) (h2 : ∀ Γ₀ C₀ → Term (T Γ₀) → Term (T (Γ₀ ‣₀ C₀))) where

  postulate
    elim-Spec₀-≡-◆ : elim-Spec₀ T h1 h2 ◆₀ ≡ h1
    elim-Spec₀-≡-‣ : ∀ Γ C → elim-Spec₀ T h1 h2 (Γ ‣₀ C) ≡ h2 Γ C (elim-Spec₀ T h1 h2 Γ)
  
  {-# REWRITE elim-Spec₀-≡-◆ elim-Spec₀-≡-‣ #-}

postulate
  CtorTm₀ : Term Spec₀ → Term Ctor₀ → Type
  cvz₀ : ∀ Γ₀ C₀ → Term (CtorTm₀ (Γ₀ ‣₀ C₀) C₀)
  cvs₀ : ∀ Γ₀ C₀ C'₀ → Term (CtorTm₀ Γ₀ C₀) → Term (CtorTm₀ (Γ₀ ‣₀ C'₀) C₀)

  elim-CtorTm₀ : (T : ∀ {Γ C} → Term (CtorTm₀ Γ C) → Type)
               → (∀ Γ C → Term (T (cvz₀ Γ C)))
               → (∀ Γ C C' c → Term (T c) → Term (T (cvs₀ Γ C C' c)))
               → ∀ Γ C (c : Term (CtorTm₀ Γ C)) → Term (T c)

module _ (T : ∀ {Γ C} → Term (CtorTm₀ Γ C) → Type)
         (h1 : ∀ Γ C → Term (T (cvz₀ Γ C)))
         (h2 : ∀ Γ C C' c → Term (T c) → Term (T (cvs₀ Γ C C' c))) where

  postulate
    elim-CtorTm₀-z : ∀ Γ C → elim-CtorTm₀ T h1 h2 _ _ (cvz₀ Γ C) ≡ h1 Γ C
    elim-CtorTm₀-s : ∀ Γ C C' c
                   → elim-CtorTm₀ T h1 h2 _ _ (cvs₀ Γ C C' c)
                   ≡ h2 Γ C C' c (elim-CtorTm₀ T h1 h2 _ _ c)

  {-# REWRITE elim-CtorTm₀-z elim-CtorTm₀-s #-}

wkc : ∀{Ω Γ C} → Term (Wk₀ Ω Γ) → Term (CtorTm₀ Γ C => CtorTm₀ Ω C)
wkc {C = C} w =
  elim-Wk₀ (λ {Ω} {Γ} _ → CtorTm₀ Γ C => CtorTm₀ Ω C)
    (λ Γ → lam (λ a → a))
    (λ Γ C → lam (λ c → cvs₀ _ _ _ c))
    (λ w w' h h' → lam (λ a → h $ (h' $ a))) w

Base₀-Alg₀ : Term Base₀ → Fam₀ → SType
Base₀-Alg₀ b f = elim-Base₀ (λ _ → U) (proj₁ f) (proj₂ f) b

Ty₀-Alg₀ : Term Ty₀ → Fam₀ → SType
Ty₀-Alg₀ A f =
  elim-Ty₀ (λ _ → U) (λ b → Base₀-Alg₀ b f) (λ x → x) (λ A B → A =>U (Base₀-Alg₀ B f)) A

Params₀-Alg₀ : Term Params₀ → Fam₀ → SType
Params₀-Alg₀ x f = elim-Params₀ (λ _ → U) 𝟙U (λ Δ A h → PairU h (Ty₀-Alg₀ A f)) x

Ctor₀-Alg₀ : Term Ctor₀ → Fam₀ → SType
Ctor₀-Alg₀ C f = Params₀-Alg₀ (fst C) f =>U Base₀-Alg₀ (snd C) f

Spec₀-Alg₀ : Term Spec₀ → Fam₀ → SType
Spec₀-Alg₀ Γ₀ F = elim-Spec₀ (λ _ → U) 𝟙U (λ Γ' C₀ h → PairU h (Ctor₀-Alg₀ C₀ F)) Γ₀

Wk₀-Alg₀ : ∀{F Ω Γ} → Term (Wk₀ Ω Γ) → STerm (Spec₀-Alg₀ Ω F =>U Spec₀-Alg₀ Γ F)
Wk₀-Alg₀ {F} = elim-Wk₀ (λ {Ω} {Γ} x → El (Spec₀-Alg₀ Ω F =>U Spec₀-Alg₀ Γ F))
  (λ Γ₁ → lam (λ a → a))
  (λ Γ C → lam (λ x → fst x))
  λ w w' h h' → lam (λ x → app h' (app h x))

Spec₀-Alg₀' : Term Spec₀ → Fam₀ → Type
Spec₀-Alg₀' Γ₀ F = Pi Ctor₀ λ C₀ → CtorTm₀ Γ₀ C₀ => El (Ctor₀-Alg₀ C₀ F)

Wk₀-Alg₀' : ∀{F Ω Γ} → Term (Wk₀ Ω Γ) → Term (Spec₀-Alg₀' Ω F) → Term (Spec₀-Alg₀' Γ F)
Wk₀-Alg₀' {F} w γ = lam λ _ → lam λ c → γ $ _ $ (wkc w $ c)

to-Spec₀-Alg₀ : ∀ {F} Γ → Term (Spec₀-Alg₀' Γ F => El (Spec₀-Alg₀ Γ F))
to-Spec₀-Alg₀ = elim-Spec₀ _
  (lam (λ γ' → star))
  λ Γ₀ C₀ h → lam (λ γc' → pair (h $ lam (λ _ → lam (λ c → γc' $ _ $ cvs₀ _ _ _ c)))
                                (γc' $ _ $ cvz₀ _ _))

CtorTm₀-Alg₀ : ∀ {Γ C F} → Term (CtorTm₀ Γ C)
             → STerm (Spec₀-Alg₀ Γ F) → STerm (Ctor₀-Alg₀ C F)
CtorTm₀-Alg₀ {F = F} c =
  let aux = elim-CtorTm₀ (λ {Γ} {C} _ → El (Spec₀-Alg₀ Γ F =>U Ctor₀-Alg₀ C F))
              (λ _ _ → lam snd)
              (λ Γ C C' c h → lam (λ γ → app h (fst γ)))
              _ _ c
  in app aux

to-Spec₀-Alg₀' : ∀ {F} Γ → Term (El (Spec₀-Alg₀ Γ F) => Spec₀-Alg₀' Γ F)
to-Spec₀-Alg₀' Γ = lam λ γ → lam λ C → lam λ c → CtorTm₀-Alg₀ c γ

Spec₀-Alg₀'-wk1 : ∀{F} Γ₀ C₀ → Term (Spec₀-Alg₀' (Γ₀ ‣₀ C₀) F)
                → Term (Spec₀-Alg₀' Γ₀ F)
Spec₀-Alg₀'-wk1 _ _ γ = lam λ _ → lam λ c → γ $ _ $ cvs₀ _ _ _ c

Spec₀-Alg₀'-wk2 : ∀{F} Γ₀ C₀ → Term (Spec₀-Alg₀' (Γ₀ ‣₀ C₀) F)
                → STerm (Ctor₀-Alg₀ C₀ F)
Spec₀-Alg₀'-wk2 _ _ γ = γ $ _ $ cvz₀ _ _

mk-Spec₀-Alg₀' : ∀ {F} Γ₀ C₀
               → Term (Spec₀-Alg₀' Γ₀ F)
               → STerm (Ctor₀-Alg₀ C₀ F)
               → Term (Spec₀-Alg₀' (Γ₀ ‣₀ C₀) F)
mk-Spec₀-Alg₀' Γ₀ C₀ γ f = to-Spec₀-Alg₀' (Γ₀ ‣₀ C₀) $ pair (to-Spec₀-Alg₀ Γ₀ $ γ) f

module _ {F₀} (D : DFam₀ F₀) where

  Base₀-DAlg₀ : (A : Term Base₀) → Term (El (Base₀-Alg₀ A F₀) => U)
  Base₀-DAlg₀ = elim-Base₀ _ (lam (proj₁ D)) (lam (proj₂ D))

  Ty₀-DAlg₀ : (A : Term Ty₀) → Term (El (Ty₀-Alg₀ A F₀) => U)
  Ty₀-DAlg₀ = elim-Ty₀ _ Base₀-DAlg₀ (λ X → lam (λ _ → X))
                         λ A B → lam (λ h → PiU A (λ x → app (Base₀-DAlg₀ B) (app h x)))

  Params₀-DAlg₀ : (Δ : Term Params₀) → Term (El (Params₀-Alg₀ Δ F₀) => U)
  Params₀-DAlg₀ = elim-Params₀ _ (lam (λ _ → 𝟙U))
                    λ Δ A h → lam (λ pd → PairU (app h (fst pd)) (app (Ty₀-DAlg₀ A) (snd pd)))

  Ctor₀-DAlg₀ : (C : Term Ctor₀) -> Term (El (Ctor₀-Alg₀ C F₀) => U)
  Ctor₀-DAlg₀ C = lam λ c →
    PiU (Params₀-Alg₀ (fst C) F₀) λ p₀ →
      (Params₀-DAlg₀ (fst C) $ p₀) =>U (Base₀-DAlg₀ (snd C) $ (c $ p₀))


  Spec₀-DAlg₀ : ∀ Γ → Term (El (Spec₀-Alg₀ Γ F₀) => U)
  Spec₀-DAlg₀ = elim-Spec₀ _ (lam λ _ → 𝟙U)
                  λ Γ₀ C₀ h → lam (λ γ → PairU (h $ fst γ) (Ctor₀-DAlg₀ C₀ $ snd γ))

  Spec₀-DAlg₀' : ∀ Γ → Term (Spec₀-Alg₀' Γ F₀ => U)
  Spec₀-DAlg₀' = elim-Spec₀ _ (lam λ a → 𝟙U)
    λ Γ₀ C₀ h → lam λ γ →
      PairU (h $ lam λ _ → lam λ c → γ $ _ $ cvs₀ _ _ _ c)
            (Ctor₀-DAlg₀ C₀ $ (γ $ _ $ cvz₀ _ _))

  Spec₀-DAlg₀'' : ∀ Γ → Term (Spec₀-Alg₀' Γ F₀) → Type
  Spec₀-DAlg₀'' Γ γ =
    Pi Ctor₀ λ C₀ → Pi (CtorTm₀ Γ C₀) λ c₀ →
      El (Ctor₀-DAlg₀ C₀ $ (γ $ _ $ c₀))

module _ {F₀} {F₀ᴰ : DFam₀ F₀} where
 
  CtorTm₀-DAlg₀ : ∀ {Γ₀ C₀} (c : Term (CtorTm₀ Γ₀ C₀))
                → Term (El (PiU (Spec₀-Alg₀ Γ₀ F₀) λ γ₀ →
                    (Spec₀-DAlg₀ F₀ᴰ Γ₀ $ γ₀)
                    =>U (Ctor₀-DAlg₀ F₀ᴰ C₀ $ CtorTm₀-Alg₀ c γ₀)))
  CtorTm₀-DAlg₀ = elim-CtorTm₀
    (λ {Γ₀} {C₀} c → El (PiU (Spec₀-Alg₀ Γ₀ F₀) λ γ₀ → (Spec₀-DAlg₀ F₀ᴰ Γ₀ $ γ₀)
                    =>U (Ctor₀-DAlg₀ F₀ᴰ C₀ $ CtorTm₀-Alg₀ c γ₀)))
    (λ Γ C → lam λ γ₀ → lam λ γd₀ → snd γd₀)
    (λ Γ C C' c h → lam λ γ₀ → lam λ γd₀ → h $ fst γ₀ $ fst γd₀) _ _

  CtorTm₀-DAlg₀'
    : ∀ {Γ₀ C₀} (c : Term (CtorTm₀ Γ₀ C₀))
    → Term (Pi (Spec₀-Alg₀' Γ₀ F₀) λ γ₀ →
               El ((Spec₀-DAlg₀' F₀ᴰ Γ₀ $ γ₀)
                    =>U (Ctor₀-DAlg₀ F₀ᴰ C₀ $ (γ₀ $ _ $ c))))
  CtorTm₀-DAlg₀' = elim-CtorTm₀
    (λ {Γ₀} {C₀} c → Pi (Spec₀-Alg₀' Γ₀ F₀) λ γ₀ → El ((Spec₀-DAlg₀' F₀ᴰ Γ₀ $ γ₀)
                    =>U (Ctor₀-DAlg₀ F₀ᴰ C₀ $ (γ₀ $ _ $ c))))
    (λ Γ C → lam λ γ₀ → lam λ γd₀ → snd γd₀)
    (λ Γ C C' c h → lam λ γ₀ → lam λ γd₀ → h $ _ $ fst γd₀) _ _

  to-Spec₀-DAlg₀''
    : ∀ Γ (γ : STerm (Spec₀-Alg₀ Γ F₀)) → STerm (Spec₀-DAlg₀ F₀ᴰ Γ $ γ)
    → Term (Spec₀-DAlg₀'' F₀ᴰ Γ (to-Spec₀-Alg₀' Γ $ γ))
  to-Spec₀-DAlg₀'' Γ γ γd = lam λ C → lam λ c → CtorTm₀-DAlg₀ c $ γ $ γd

double : ∀{F} Γ → Term (Spec₀-Alg₀' Γ F)
                → Term (Spec₀-Alg₀' Γ F)
double Γ γ = to-Spec₀-Alg₀' Γ $ (to-Spec₀-Alg₀ Γ $ γ)

