{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

module erased.initial.erasure where

open import lib hiding (fst ; snd)
open import IIT.spec
open import IIT.algebra
open import erased.initial.algebra-small
open import erased.initial.internal-algebra
open import hoas-postulated as H

erase-Base : Base Γ Δ → Term Base₀
erase-Base ty1 = ty1₀
erase-Base (ty2 x) = ty2₀

erase-Base-[] : (w : Wk Ω Γ) → erase-Base (B [ w ]b') ≡ erase-Base B
erase-Base-[] {B = ty1} w = refl
erase-Base-[] {B = ty2 x} w = refl
{-# REWRITE erase-Base-[] #-}

erase-Ty : Ty Γ Δ → Term Ty₀
erase-Ty (ext x) = ext₀ x
erase-Ty (base x) = base₀ (erase-Base x)
erase-Ty (Π A B) = Π₀ A (erase-Base B)
erase-Ty (A [ x ]) = erase-Ty A
erase-Ty (A [ w ]') = erase-Ty A

erase-Params : Params Γ → Term Params₀
erase-Params ● = ●₀
erase-Params (Δ ‣‣ x) = erase-Params Δ ‣‣₀ erase-Ty x
erase-Params (Δ [ x ]p) = erase-Params Δ

erase-Ctor : Ctor Γ → Term Ctor₀
erase-Ctor (ctor Δ B) = pair (erase-Params Δ) (erase-Base B)

-- erase-Ctor[] : (w : Wk Ω Γ) → erase-Ctor (C [ w ]c) ≡ erase-Ctor C
-- erase-Ctor[] {C = ctor _ ty1} w = refl
-- erase-Ctor[] {C = ctor _ (ty2 x)} w = refl

erase-Spec : Spec → Term Spec₀
erase-Spec init = ◆₀
erase-Spec (Γ ‣ C) = erase-Spec Γ ‣₀ erase-Ctor C

erase-Wk : Wk Ω Γ → Term (Wk₀ (erase-Spec Ω) (erase-Spec Γ))
erase-Wk Wk.Id = Id₀ _
erase-Wk Drop = Drop₀ _ _
erase-Wk (w ∘w w') = erase-Wk w ·w₀ erase-Wk w'

erase-CtorTm : CtorTm Γ C → Term (CtorTm₀ (erase-Spec Γ) (erase-Ctor C))
erase-CtorTm (v0c {Γ} {A}) = cvz₀ (erase-Spec Γ) (erase-Ctor A)
erase-CtorTm (dropc c) = cvs₀ _ _ _ (erase-CtorTm c)
erase-CtorTm (c [ w ]ctm) = wkc (erase-Wk w) $ erase-CtorTm c

Base-Alg-≡ : ∀{F₀} (A : Base Γ Δ) → Base₀-Alg A F₀ ≡ Base₀-Alg₀ (erase-Base A) F₀
Base-Alg-≡ ty1 = refl
Base-Alg-≡ (ty2 x) = refl
{-# REWRITE Base-Alg-≡ #-}

Ty-Alg-≡ : ∀{F₀} (A : Ty Γ Δ) → Ty₀-Alg A F₀ ≡ Ty₀-Alg₀ (erase-Ty A) F₀
Ty-Alg-≡ (ext x) = refl
Ty-Alg-≡ (base x) = refl -- Base-Alg-≡ x
Ty-Alg-≡ (Π A B) = refl -- cong (PiU _) (funext (λ _ → Base-Alg-≡ B))
Ty-Alg-≡ (A [ x ]) = Ty-Alg-≡ A
Ty-Alg-≡ (A [ w ]') = Ty-Alg-≡ A
{-# REWRITE Ty-Alg-≡ #-}

Params-Alg-≡ : ∀{F₀} (Δ : Params Γ) → Params₀-Alg Δ F₀ ≡ Params₀-Alg₀ (erase-Params Δ) F₀
Params-Alg-≡ ● = refl
Params-Alg-≡ (Δ ‣‣ A) = cong (λ z → PairU z (Ty₀-Alg A _)) (Params-Alg-≡ Δ)
Params-Alg-≡ (Δ [ x ]p) = Params-Alg-≡ Δ
{-# REWRITE Params-Alg-≡ #-}

ext-Spec-Alg' : ∀{F₀} Γ → Term (Spec₀-Alg₀' (erase-Spec Γ) F₀) → Spec₀-Alg' Γ F₀
ext-Spec-Alg' Γ γ {ctor Δ B} c = lam λ p → γ $ _ $ erase-CtorTm c $ p

--------------------------------------------------------------------------------

Base₀-DAlg₀-≡ : ∀{F D} (B : Base Γ Δ) (b₀ : STerm (Base₀-Alg B F))
              → Base₀-DAlg B b₀ D ≡ (Base₀-DAlg₀ D (erase-Base B) $ b₀)
Base₀-DAlg₀-≡ ty1 b₀ = refl
Base₀-DAlg₀-≡ (ty2 x) b₀ = refl
{-# REWRITE Base₀-DAlg₀-≡ #-}

Ty₀-DAlg₀-≡ : ∀{F D} (B : Ty Γ Δ) (b₀ : STerm (Ty₀-Alg B F))
              → Ty₀-DAlg B b₀ D ≡ (Ty₀-DAlg₀ D (erase-Ty B) $ b₀)
Ty₀-DAlg₀-≡ (ext x) b₀ = refl
Ty₀-DAlg₀-≡ (base x) b₀ = refl
Ty₀-DAlg₀-≡ (Π A x) b₀ = refl
Ty₀-DAlg₀-≡ (B [ x ]) b₀ = Ty₀-DAlg₀-≡ B b₀
Ty₀-DAlg₀-≡ (B [ w ]') b₀ = Ty₀-DAlg₀-≡ B b₀
{-# REWRITE Ty₀-DAlg₀-≡ #-}

Params₀-DAlg₀-≡ : ∀{F D} (Δ : Params Γ) (p₀ : STerm (Params₀-Alg Δ F))
              → Params₀-DAlg Δ p₀ D ≡ (Params₀-DAlg₀ D (erase-Params Δ) $ p₀)
Params₀-DAlg₀-≡ ● p₀ = refl
Params₀-DAlg₀-≡ {D = D} (Δ ‣‣ x) p₀ = cong (λ z → PairU z (Ty₀-DAlg x (snd p₀) D)) (Params₀-DAlg₀-≡ Δ (fst p₀))
Params₀-DAlg₀-≡ (Δ [ x ]p) p₀ = Params₀-DAlg₀-≡ Δ p₀
{-# REWRITE Params₀-DAlg₀-≡ #-}

ext-Spec₀-DAlg : ∀{F D} Γ
             → (γ : Term (Spec₀-Alg₀' (erase-Spec Γ) F))
             → (γd : Spec₀-DAlg' Γ (ext-Spec-Alg' Γ γ) D)
             → STerm (Spec₀-DAlg₀' D (erase-Spec Γ) $ γ)
ext-Spec₀-DAlg init γ γd = star
ext-Spec₀-DAlg {F} {D} (Γ ‣ C) γ γd =
  pair (ext-Spec₀-DAlg {F} {D} Γ _ (λ c → γd (dropc c))) (γd v0c)

CtorTm-DAlg-wk
  : ∀{F D} (w : Wk Γ Ω) (c : CtorTm Ω C)
    (γ : Term (Spec₀-Alg₀' (erase-Spec Γ) F))
  → (γd : Spec₀-DAlg' Γ (ext-Spec-Alg' Γ γ) D)
  → (CtorTm₀-DAlg₀' {F} {D} (wkc (erase-Wk w) $ erase-CtorTm c) $ γ $ ext-Spec₀-DAlg {F} {D} Γ γ γd)
    ≡ (CtorTm₀-DAlg₀' {F} {D} (erase-CtorTm c) $ Wk₀-Alg₀' (erase-Wk w) γ $ ext-Spec₀-DAlg {F} {D} Ω _ λ c' → γd (c' [ w ]ctm))
CtorTm-DAlg-wk Wk.Id c γ γd = refl
CtorTm-DAlg-wk Drop c γ γd = refl
CtorTm-DAlg-wk (w ∘w w') c γ γd =
  trans (CtorTm-DAlg-wk w (c [ w' ]ctm) γ γd) (CtorTm-DAlg-wk w' c _ (λ c' → γd (c' [ w ]ctm)))

ext-CtorTm-DAlg
  : ∀{F D} (γ : Term (Spec₀-Alg₀' (erase-Spec Γ) F))
  → (γd : Spec₀-DAlg' Γ (ext-Spec-Alg' Γ γ) D)
  → (c : CtorTm Γ C) -- (ctor Δ B))
  → (CtorTm₀-DAlg₀' {F} {D} (erase-CtorTm c) $ γ $ ext-Spec₀-DAlg {F} {D} Γ γ γd)
  ≡ γd c
ext-CtorTm-DAlg γ γd v0c = refl
ext-CtorTm-DAlg γ γd (dropc c) = ext-CtorTm-DAlg _ _ c
ext-CtorTm-DAlg γ γd (c [ w ]ctm) =
  trans (CtorTm-DAlg-wk w c γ γd) aux
  where
    w₀ = erase-Wk w
    aux = ext-CtorTm-DAlg (Wk₀-Alg₀' w₀ γ) (λ c' → γd (c' [ w ]ctm)) c

{-
ext-Spec₀-DAlg-ind : ∀{F D} Γ
             → (γ : Term (Spec₀-Alg₀' (erase-Spec Γ) F))
             → (γd : Spec₀-DAlg' Γ (ext-Spec-Alg' Γ γ) D)
             → STerm (Spec₀-DAlg₀' D (erase-Spec Γ) $ γ)
ext-Spec₀-DAlg-ind init γ γd = star
ext-Spec₀-DAlg-ind (Γ ‣ C) γ γd =
  pair (ext-Spec₀-DAlg-ind Γ _ (proj₁ γd)) (proj₂ γd)

CtorTm-DAlg-wk
  : ∀{F D} (w : Wk Γ Ω) (c : CtorTm Ω C)
    (γ : Term (Spec₀-Alg₀' (erase-Spec Γ) F))
  → (γd : Spec₀-DAlg' Γ (ext-Spec-Alg' Γ γ) D)
  → (CtorTm₀-DAlg₀' {F} {D} (wkc (erase-Wk w) $ erase-CtorTm c) $ γ $ ext-Spec₀-DAlg-ind {F} {D} Γ γ γd)
    ≡ (CtorTm₀-DAlg₀' {F} {D} (erase-CtorTm c) $ Wk₀-Alg₀' (erase-Wk w) γ $ ext-Spec₀-DAlg-ind {F} {D} Ω _ (Wk₀-DAlg' w γd))
CtorTm-DAlg-wk Wk.Id c γ γd = refl
CtorTm-DAlg-wk Drop c γ γd = refl
CtorTm-DAlg-wk (w ∘w w') c γ γd =
  trans (CtorTm-DAlg-wk w (c [ w' ]ctm) γ γd) (CtorTm-DAlg-wk w' c _ (Wk₀-DAlg' w γd))

ext-CtorTm-DAlg
  : ∀{F D} (γ : Term (Spec₀-Alg₀' (erase-Spec Γ) F))
  → (γd : Spec₀-DAlg' Γ (ext-Spec-Alg' Γ γ) D)
  → (c : CtorTm Γ C) -- (ctor Δ B))
  → (CtorTm₀-DAlg₀' {F} {D} (erase-CtorTm c) $ γ $ ext-Spec₀-DAlg-ind {F} {D} Γ γ γd)
  ≡ CtorTm₀-DAlg' c γd
ext-CtorTm-DAlg γ γd v0c = refl
ext-CtorTm-DAlg γ γd (dropc c) = ext-CtorTm-DAlg _ _ c
ext-CtorTm-DAlg {F = F} {D} γ γd (c [ w ]ctm) =
  trans (CtorTm-DAlg-wk w c γ γd) aux
  where
    w₀ = erase-Wk w
    aux = ext-CtorTm-DAlg (Wk₀-Alg₀' w₀ γ) (Wk₀-DAlg' {F} {D} w γd) c
-}
