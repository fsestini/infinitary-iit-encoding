{-# OPTIONS --prop --rewriting --show-irrelevant #-}

module sigma-construction where

open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import predicate.algebra
open import lib hiding (Fam ; fst ; snd ; fstP ; sndP)
open import hoas-postulated

-- Σ-Fam : (s : Set × Set) → BasePreds s → Fam
-- Σ-Fam (C , T) (P , Q) = (Σp C P) , λ x → Σp T (Q (fst x))

Σ-Fam : (F₀ : Fam₀) → Fam₁ F₀ → Fam
Σ-Fam (C , T) (P , Q) = Sigmap C P , λ x → Sigmap T (Q (fstp x))

module _ {F₀} {F₁} where

  Σ-Spec : (Γ : Spec) (γ₀ : Spec₀-Alg Γ F₀) → Spec₁-Alg Γ γ₀ F₁ → Spec-Alg Γ (Σ-Fam F₀ F₁)
  Σ-Ctor : (A : Ctor Γ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁)
           (a₀ : STerm (Ctor₀-Alg A F₀)) (a₁ : PTerm (Ctor₁-Alg A γ₀ a₀ F₁))
         → STerm (Ctor-Alg A (Σ-Spec Γ γ₀ γ₁))
  Σ-Params : (Δ : Params Γ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁)
             (p₀ : STerm (Params₀-Alg Δ F₀)) (p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁))
           → STerm (Params-Alg Δ (Σ-Spec Γ γ₀ γ₁))
  Σ-Base : (A : Base Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁)
           {p₀ : STerm (Params₀-Alg Δ F₀)} (p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁))
           (a₀ : STerm (Base₀-Alg A F₀)) (a' : PTerm (Base₁-Alg A γ₀ p₀ a₀ F₁))
         → STerm (Base-Alg A (Σ-Spec Γ γ₀ γ₁) (Σ-Params Δ γ₁ p₀ p₁))
  Σ-Ty : (A : Ty Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁)
         {p₀ : STerm (Params₀-Alg Δ F₀)} (p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁))
         (a₀ : STerm (Ty₀-Alg A F₀)) (a' : PTerm (Ty₁-Alg A γ₀ p₀ a₀ F₁))
       → STerm (Ty-Alg A (Σ-Spec Γ γ₀ γ₁) (Σ-Params Δ γ₁ p₀ p₁))
  Σ-CtorTm : (t : CtorTm Γ C) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
           → CtorTm-Alg t (Σ-Spec Γ γ₀ γ₁)
           ≡ Σ-Ctor C γ₁ (CtorTm₀-Alg t γ₀) (CtorTm₁-Alg t γ₁)
  Σ-Tm' : (t : Tm Γ Δ A) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
         (p₀ : STerm (Params₀-Alg Δ F₀)) (p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁))
       → Tm-Alg t (Σ-Spec Γ γ₀ γ₁) (Σ-Params Δ γ₁ p₀ p₁) ≡ Σ-Ty A _ _ _ (Tm₁-Alg t γ₁ p₁)
  Σ-Sub : (σ : Sub {Γ} ∇ Δ) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
          {p₀ : STerm (Params₀-Alg ∇ F₀)} {p₁ : PTerm (Params₁-Alg ∇ γ₀ p₀ F₁)}
        → Σ-Params Δ _ _ (Sub₁-Alg σ γ₁ p₁) ≡ Sub-Alg σ (Σ-Params ∇ γ₁ p₀ p₁)
  Σ-Sub' : (σ : Sub {Γ} ∇ Δ) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
          {p₀ : STerm (Params₀-Alg ∇ F₀)} {p₁ : PTerm (Params₁-Alg ∇ γ₀ p₀ F₁)}
        → Sub-Alg σ (Σ-Params ∇ γ₁ p₀ p₁) ≡ Σ-Params Δ _ _ (Sub₁-Alg σ γ₁ p₁)
  Σ-Wk : (w : Wk Ω Γ) (γ₀ : Spec₀-Alg _ F₀) (γ₁ : Spec₁-Alg _ γ₀ F₁)
       → Σ-Spec Γ _ (Wk₁-Alg w γ₁) ≡ Wk-Alg w (Σ-Spec Ω γ₀ γ₁)
  Σ-Wk' : (w : Wk Ω Γ) (γ₀ : Spec₀-Alg _ F₀) (γ₁ : Spec₁-Alg _ γ₀ F₁)
       → Wk-Alg w (Σ-Spec Ω γ₀ γ₁) ≡ Σ-Spec Γ _ (Wk₁-Alg w γ₁)
  -- Σ-Tm : (t : Tm Γ Δ A)
  --        (p₀ : STerm (Params₀-Alg Δ)) (p₁ : PTerm (Params₁-Alg Δ γ₀ p₀))
  --      → Σ-Ty A _ (Tm₁-Alg t γ₁ p₁) ≡ Tm-Alg t (Σ-Spec Γ γ₀ γ₁) (Σ-Params Δ p₀ p₁)
  
  Σ-Params-fst : (Δ : Params Γ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁)
               → STerm (Params-Alg Δ (Σ-Spec Γ γ₀ γ₁)) → STerm (Params₀-Alg Δ F₀)
  Σ-Ty-fst : (A : Ty Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁) {p : _}
           → STerm (Ty-Alg A (Σ-Spec Γ γ₀ γ₁) p) → STerm (Ty₀-Alg A F₀)
  Σ-Base-fst : (A : Base Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁) {p : _}
           → STerm (Base-Alg A (Σ-Spec Γ γ₀ γ₁) p) → STerm (Base₀-Alg A F₀)

  Σ-Params-snd : (Δ : Params Γ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁)
                 (p : STerm (Params-Alg Δ (Σ-Spec Γ γ₀ γ₁)))
               → PTerm (Params₁-Alg Δ γ₀ (Σ-Params-fst Δ γ₁ p) F₁)

  Σ-Ty-snd : (A : Ty Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁)
             {p : _} (a : STerm (Ty-Alg A (Σ-Spec Γ γ₀ γ₁) p))
           → PTerm (Ty₁-Alg A γ₀ (Σ-Params-fst Δ γ₁ p) (Σ-Ty-fst A γ₁ a) F₁)
  Σ-Ty-snd' : (A : Ty Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁)
              {p₀ : _} (p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁))
              (a : STerm (Ty-Alg A (Σ-Spec Γ γ₀ γ₁) (Σ-Params Δ γ₁ p₀ p₁)))
           → PTerm (Ty₁-Alg A γ₀ p₀ (Σ-Ty-fst A γ₁ a) F₁)
  
  Σ-Params-β-fst : (Δ : Params Γ) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
                   (p₀ : STerm (Params₀-Alg Δ F₀)) (p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁))
                   -- {p : Params₀-Alg Δ (p' : Params₁-Alg Δ γ p bp)
                 → Σ-Params-fst Δ γ₁ (Σ-Params Δ γ₁ p₀ p₁) ≡ p₀

  Σ-Ty-β-fst : (A : Ty Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
               {p₀ : STerm (Params₀-Alg Δ F₀)} {p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁)}
               (a₀ : STerm (Ty₀-Alg A F₀)) (a₁ : PTerm (Ty₁-Alg A γ₀ p₀ a₀ F₁))
             → Σ-Ty-fst A γ₁ (Σ-Ty A γ₁ p₁ a₀ a₁) ≡ a₀

  Σ-Base-β-fst : (A : Base Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
               {p₀ : STerm (Params₀-Alg Δ F₀)} {p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁)}
               (a₀ : STerm (Base₀-Alg A F₀)) (a₁ : PTerm (Base₁-Alg A γ₀ p₀ a₀ F₁))
             → Σ-Base-fst A γ₁ (Σ-Base A γ₁ p₁ a₀ a₁) ≡ a₀


  Σ-Params-η : (Δ : Params Γ) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
               (p : STerm (Params-Alg Δ (Σ-Spec Γ γ₀ γ₁)))
             → Σ-Params Δ γ₁ (Σ-Params-fst Δ γ₁ p) (Σ-Params-snd Δ γ₁ p) ≡ p

  Σ-Ty-η : (A : Ty Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
           {p : _} (a : STerm (Ty-Alg A (Σ-Spec Γ γ₀ γ₁) p))
         → transp (λ z → STerm (Ty-Alg A _ z)) (from-≡ (Σ-Params-η Δ p))
             (Σ-Ty A _ _ _ (Σ-Ty-snd A γ₁ a))
         ≡ a

  -- Σ-Base-snd : (A : Base Γ Δ)
  --            {p : _} (a : Term (Base-Alg A (Σ-Spec Γ γ₀ γ₁) p))
  --          → PTerm (Base₁-Alg A γ₀ (Σ-Params-fst Δ p) (Σ-Base-fst A a))

  Σ-Base-snd' : (A : Base Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} (γ₁ : Spec₁-Alg Γ γ₀ F₁)
                {p₀ : _} (p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁))
                (a : STerm (Base-Alg A (Σ-Spec Γ γ₀ γ₁) (Σ-Params Δ γ₁ _ p₁)))
           → PTerm (Base₁-Alg A γ₀ p₀ (Σ-Base-fst A γ₁ a) F₁)

  Σ-Base-η' : (A : Base Γ Δ) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
              {p₀ : _} {p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁)}
              (a : STerm (Base-Alg A (Σ-Spec Γ γ₀ γ₁) (Σ-Params Δ γ₁ p₀ p₁)))
            → Σ-Base A _ _ _ (Σ-Base-snd' A γ₁ p₁ a)
            ≡ a

  -- Σ-Base-η : (A : Base Γ Δ)
  --          {p : _} (a : Term (Base-Alg A (Σ-Spec Γ γ₀ γ₁) p))
  --        → transp (λ z → Term (Base-Alg A _ z)) (from-≡ (Σ-Params-η Δ p))
  --            (Σ-Base A _ (Σ-Base-snd A a))
  --        ≡ a

{-

Σ-Base-snd : ∀{Γ Δ s bp γ} (A : Base Γ Δ) (γ' : Spec₁-Alg {s = s} Γ γ bp)
            (p : _) (a : Base-Alg A (Σ-Spec Γ γ') p)
         → Base₁-Alg A γ (Σ-Params-fst Δ γ' p) (Σ-Base-fst A γ' a) bp
Σ-Base-snd' : ∀{Γ Δ s bp γ} (A : Base Γ Δ) (γ' : Spec₁-Alg {s = s} Γ γ bp)
               {p : _} (p' : Params₁-Alg Δ γ p _) (a : Base-Alg A (Σ-Spec Γ γ') (Σ-Params Δ γ' p'))
         → Base₁-Alg A γ p (Σ-Base-fst A γ' a) bp




-}

  Σ-Spec init _ _ = tt
  Σ-Spec (Γ ‣ A) (γ , a) (γ' ,P a') = Σ-Spec Γ _ γ' , Σ-Ctor A γ' a a'

  Σ-Wk Id _ _ = refl
  Σ-Wk Drop _ _ = refl
  Σ-Wk (w ∘w w') γ₀ γ₁ =
    trans (Σ-Wk w' _ (Wk₁-Alg w γ₁)) (cong (Wk-Alg w') (Σ-Wk w _ γ₁))

  Σ-Wk' x y z = sym (Σ-Wk x y z)
  {-# REWRITE Σ-Wk' #-}
  
  Σ-Params ● _ _ _ = star
  Σ-Params (Δ ‣‣ A) _ ps ps' = pair (Σ-Params Δ _ _ (fstP ps')) (Σ-Ty A _ _ _ (sndP ps'))
  Σ-Params (Δ [ x ]p) _ _ p₁ = Σ-Params Δ _ _ p₁

  Σ-Params-fst ● _ x = star
  Σ-Params-fst (Δ ‣‣ A) γ₁ p = pair (Σ-Params-fst Δ γ₁ (fst p)) (Σ-Ty-fst A γ₁ (snd p))
  Σ-Params-fst (Δ [ w ]p) γ₁ = Σ-Params-fst Δ (Wk₁-Alg w γ₁)

  Σ-Params-snd ● _ _ = truth
  Σ-Params-snd (Δ ‣‣ A) γ₁ p = pairP (Σ-Params-snd Δ γ₁ (fst p)) (Σ-Ty-snd A γ₁ (snd p))
  Σ-Params-snd (Δ [ x ]p) γ₁ = Σ-Params-snd Δ (Wk₁-Alg x γ₁)

  Σ-Ty (ext x) _ _ a₀ _ = a₀
  Σ-Ty (base x) = Σ-Base x
  Σ-Ty (Π A B) γ₁ p₁ f₀ f₁ =
    lam λ a → Σ-Base B _ (pairP p₁ truth) _ (appp f₁ a)
  Σ-Ty (A [ x ]) γ₁ p₁ a₀ a₁ =
    transp (λ z → STerm (Ty-Alg A _ z)) (from-≡ (Σ-Sub x))
      (Σ-Ty A γ₁ (Sub₁-Alg x γ₁ p₁) a₀ a₁)
  Σ-Ty (A [ w ]') γ₁ = Σ-Ty A (Wk₁-Alg w γ₁)

  Σ-Sub Id = refl
  Σ-Sub (Ext σ x) = pair-≡ (Σ-Sub σ) (sym (Σ-Tm' x _ _))
  Σ-Sub Drop = refl
  Σ-Sub (σ ∘ τ) = trans (Σ-Sub τ) (cong (Sub-Alg τ) (Σ-Sub σ))
  Σ-Sub (σ [ w ]ws) = Σ-Sub σ

  Σ-Sub' σ = sym (Σ-Sub σ)
  {-# REWRITE Σ-Sub' #-}

  {-# TERMINATING #-}
  Σ-Base ty1 _ _ a₀ a₁ = pairp a₀ a₁
  Σ-Base (ty2 x) γ₁ p₁ a₀ a₁ =
    pairp _ (transp-P (λ z → PTerm (proj₂ F₁ z _))
              (from-≡ (cong fstp (sym (Σ-Tm' x _ p₁)))) a₁)

  Σ-Base[]b'
    : (A : Base Γ Δ) (w : Wk Ω Γ)
      {γ₀ : Spec₀-Alg Ω F₀} {γ₁ : Spec₁-Alg Ω γ₀ F₁}
      {p₀ : STerm (Params₀-Alg Δ F₀)} {p₁ : PTerm (Params₁-Alg Δ (Wk₀-Alg w γ₀) p₀ F₁)}
      (a₀ : STerm (Base₀-Alg A F₀)) (a₁ : PTerm (Base₁-Alg A (Wk₀-Alg w γ₀) p₀ a₀ F₁))
    → Σ-Base (A [ w ]b') γ₁ p₁ a₀ a₁ ≡ Σ-Base A _ p₁ a₀ a₁
  Σ-Base[]b' ty1 w a₀ a₁ = refl
  Σ-Base[]b' (ty2 x) w a₀ a₁ = refl
  {-# REWRITE Σ-Base[]b' #-}

  Σ-Params-β-fst ● p₀ p₁ = sym (Unit-η _)
  Σ-Params-β-fst (Δ ‣‣ A) {γ₁ = γ₁} p₀ p₁ =
    pair-≡ (Σ-Params-β-fst Δ {γ₁ = γ₁} _ (fstP p₁))
           (Σ-Ty-β-fst A {γ₁ = γ₁} {p₁ = fstP p₁} _ (sndP p₁))
  Σ-Params-β-fst (Δ [ x ]p) p₀ p₁ = Σ-Params-β-fst Δ _ p₁
  {-# REWRITE Σ-Params-β-fst #-}

  Σ-Params-η ● p = sym (Unit-η _)
  Σ-Params-η (Δ ‣‣ A) p = pair-≡ (Σ-Params-η Δ (fst p)) (Σ-Ty-η A (snd p))
  Σ-Params-η (Δ [ x ]p) p = Σ-Params-η Δ p
  {-# REWRITE Σ-Params-η #-}

  Σ-Ctor (ctor Δ B) γ₁ c₀ c₁ =
    lam λ p → Σ-Base B _ (Σ-Params-snd Δ γ₁ p) _
      (c₁ $p _ $P Σ-Params-snd Δ γ₁ p)

  Σ-Ty-fst (ext A) _ x = x
  Σ-Ty-fst (base B) x = Σ-Base-fst B x
  Σ-Ty-fst (Π A B) γ₁ f = lam (λ a → Σ-Base-fst B γ₁ (app f a))
  Σ-Ty-fst (A [ σ ]) γ₁ p = Σ-Ty-fst A γ₁ p
  Σ-Ty-fst (A [ w ]') γ₁ = Σ-Ty-fst A (Wk₁-Alg w γ₁)

  Σ-Ty-snd' (ext x) _ _ _ = truth
  Σ-Ty-snd' (base x) = Σ-Base-snd' x
  Σ-Ty-snd' (Π A B) γ₁ p₁ f = lamp (λ a → Σ-Base-snd' B γ₁ (pairP p₁ truth) (app f a))
  Σ-Ty-snd' (A [ x ]) γ₁ p₁ a = Σ-Ty-snd' A γ₁ (Sub₁-Alg x γ₁ p₁) a
  Σ-Ty-snd' (A [ w ]') γ₁ p₁ a = Σ-Ty-snd' A (Wk₁-Alg w γ₁) p₁ a

  Σ-Ty-snd {Δ = Δ} A γ₁ {p = p} a = Σ-Ty-snd' A γ₁ (Σ-Params-snd Δ γ₁ p) a

  Σ-Ty-η' : (A : Ty Γ Δ)
            {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
            {p₀ : _} {p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁)}
            (a : STerm (Ty-Alg A (Σ-Spec Γ γ₀ γ₁) (Σ-Params Δ γ₁ p₀ p₁)))
          → Σ-Ty A γ₁ p₁ (Σ-Ty-fst A γ₁ a) (Σ-Ty-snd' A γ₁ p₁ a)
          ≡ a

  Σ-Ty-η' (ext x) a = refl
  Σ-Ty-η' (base x) {p₁ = p₁} a = Σ-Base-η' x {p₁ = p₁} a
  Σ-Ty-η' (Π A B) f = Pi-funext (λ a → Σ-Base-η' B (app f a))
  Σ-Ty-η' (A [ σ ]) {γ₁ = γ₁} {p₁ = p₁} a = Σ-Ty-η' A {p₁ = Sub₁-Alg σ γ₁ p₁} a
  Σ-Ty-η' (A [ w ]') {p₁ = p₁} a = Σ-Ty-η' A {p₁ = p₁} a

  Σ-Ty-η {Δ = Δ} A {γ₁ = γ₁} {p = p} a = Σ-Ty-η' A {p₁ = Σ-Params-snd Δ γ₁ p} a

  Σ-Tm' vz p₀ p₁ = refl
  Σ-Tm' vz1 p₀ p₁ = refl
  Σ-Tm' (vs t) p₀ p₁ = Σ-Tm' t _ (fstP p₁)
  Σ-Tm' (ext A x) p₀ p₁ = refl
  Σ-Tm' {Γ} {Δ = Δ} (ctor {Δ = ∇} {A = A} x σ) {γ₀ = γ₀} {γ₁} p₀ p₁ =
    cong (λ f → app f (Sub-Alg σ (Σ-Params Δ γ₁ p₀ p₁))) (Σ-CtorTm x)
  Σ-Tm' {Δ = Δ} (ctor-1 x σ) {γ₁ = γ₁} p₀ p₁ =
    cong (λ f → app f (Sub-Alg σ (Σ-Params Δ γ₁ p₀ p₁))) (Σ-CtorTm x)
  Σ-Tm' (App t) p₀ p₁ = cong (λ f → app f (snd p₀)) (Σ-Tm' t _ (fstP p₁))
  Σ-Tm' (App-U t f) p₀ p₁ = cong (λ x → app f x) (Σ-Tm' t _ p₁)
  Σ-Tm' (Lam t) p₀ p₁ = Pi-funext (λ a → Σ-Tm' t (pair p₀ a) (pairP p₁ truth))
  Σ-Tm' (t [ σ ]tm) {γ₁ = γ₁} p₀ p₁ = Σ-Tm' t _ (Sub₁-Alg σ γ₁ p₁)
  Σ-Tm' (t [ w ]tm') p₀ p₁ = Σ-Tm' t _ p₁
  Σ-Tm' (t [ w ]tm'-1) p₀ p₁ = Σ-Tm' t _ p₁
  {-# REWRITE Σ-Tm' #-}

  -- Σ-Tm'' : (t : Tm Γ Δ A) {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁} (p : _)
  --      → Tm-Alg t (Σ-Spec Γ γ₀ γ₁) p ≡ {!Σ-Ty A (Tm₀-Alg t γ₀ ?) (Tm₁-Alg t γ₁ ?)!} -- Σ-Ty A _ (Tm₁-Alg t γ₁ ?)
  -- Σ-Tm'' = {!!}

  Σ-Base-fst ty1 _ x = fstp x
  Σ-Base-fst (ty2 _) _ x = fstp x

  Σ-Base-snd' ty1 _ _ a = sndp a
  Σ-Base-snd' (ty2 x) _ _ a = sndp a

  Σ-Base-η' ty1 a = refl
  Σ-Base-η' (ty2 x) a = refl

  Σ-CtorTm (v0c {A = ctor _ _}) = refl
  Σ-CtorTm (dropc {A = ctor _ _} t) = Σ-CtorTm t
  Σ-CtorTm (_[_]ctm {A = ctor _ _} t w) = Σ-CtorTm t
  {-# REWRITE Σ-CtorTm #-}

  Σ-Base-β-fst ty1 a₀ a₁ = refl
  Σ-Base-β-fst (ty2 x) a₀ a₁ = refl

  Σ-Ty-β-fst (ext x) a₀ a₁ = refl
  Σ-Ty-β-fst (base x) a₀ a₁ = Σ-Base-β-fst x _ a₁
  Σ-Ty-β-fst (Π A B) f₀ f₁ = Pi-funext (λ a → Σ-Base-β-fst B _ (appp f₁ a))
  Σ-Ty-β-fst (A [ x ]) a₀ a₁ = Σ-Ty-β-fst A _ a₁
  Σ-Ty-β-fst (A [ w ]') a₀ a₁ = Σ-Ty-β-fst A _ a₁

  -- module _ {Y : _} where
  --   open DisplayedAlgebra {Y}

  --   Σ-CtorTm-DAlg
  --     : (c : CtorTm Γ (ctor Δ B)) (γᴰ : Spec-DAlg Γ (Σ-Spec Γ γ₀ γ₁))
  --       (p₀ : _) (p₁ : _) (p : STerm (Params-DAlg Δ γᴰ (Σ-Params Δ p₀ p₁)))
  --     → STerm (Base-DAlg B γᴰ p (Σ-Base B _ (CtorTm₁-Alg c γ₁ $p p₀ $P p₁)))
  --     -- (Ctor-DAlg C γᴰ (Σ-Ctor C _ _))
  --   Σ-CtorTm-DAlg c γᴰ p₀ p₁ p = {!!} --  CtorTm-DAlg c γᴰ

  -- Σ-CtorTm-Alg
  --   : (γ₁ : Spec₁-Alg Γ γ₀) (p₀ : _) (p₁ : PTerm (Params₁-Alg Δ γ₀ p₀))
  --     (c : CtorTm Γ (ctor Δ B))
  --   → (CtorTm-Alg c (Σ-Spec Γ γ₀ γ₁) $ Σ-Params Δ p₀ p₁)
  --   ≡ Σ-Base B _ (CtorTm₁-Alg c γ₁ $p p₀ $P p₁)
  -- Σ-CtorTm-Alg {Δ = Δ} γ₁ p₀ p₁ c = ?
   -- cong (λ f → f $ Σ-Params Δ p₀ p₁) (Σ-CtorTm {γ₁ = γ₁} c)
--  {-# REWRITE Σ-CtorTm-Alg #-}

  -- Σ-CtorTm-Alg'
  --   : ∀{Γ Δ A s bp γ} (γ' : Spec₁-Alg {s = s} Γ γ bp) (p : Params-Alg Δ (Σ-Spec Γ γ'))
  --     (c : CtorTm Γ (ctor Δ A))
  --   → let p' = Σ-Params-snd Δ γ' p
  --     in CtorTm-Alg c (Σ-Spec Γ γ') p ≡ Σ-Base A γ' p' (CtorTm₁-Alg c γ' p')
  -- Σ-CtorTm-Alg' {Δ = Δ} γ' p c = Σ-CtorTm-Alg γ' (Σ-Params-snd Δ γ' p) c
  -- {-# REWRITE Σ-CtorTm-Alg' #-}



{-

Σ-Ty-η'' : ∀{Γ Δ s bp γ} (A : Ty Γ Δ) (γ' : Spec₁-Alg {s = s} Γ γ bp)
            {p : _} (p' : Params₁-Alg Δ γ p _) (a : Ty-Alg A (Σ-Spec Γ γ') (Σ-Params Δ γ' p'))
         → Σ-Ty A γ' p' (Σ-Ty-snd' A γ' p' a)
         ≡p a

Σ-Ty-η {Δ = Δ} A γ' p a = Σ-Ty-η'' A γ' (Σ-Params-snd Δ γ' p) a

Σ-Base-η : ∀{Γ Δ s bp γ} (A : Base Γ Δ) (γ' : Spec₁-Alg {s = s} Γ γ bp)
            (p : _) (a : Base-Alg A (Σ-Spec Γ γ') p)
         → Σ-Base A γ' (Σ-Params-snd Δ γ' p) (Σ-Base-snd A γ' p a) ≡p a

Σ-Base-η' : ∀{Γ Δ s bp γ} (A : Base Γ Δ) (γ' : Spec₁-Alg {s = s} Γ γ bp)
             {p : _} (p' : Params₁-Alg Δ γ p bp) (a : Base-Alg A (Σ-Spec Γ γ') (Σ-Params Δ γ' p'))
         → Σ-Base A γ' p' (Σ-Base-snd' A γ' p' a)
         ≡p a

Σ-Base-η {Δ = Δ} A γ' p a = Σ-Base-η' A γ' (Σ-Params-snd Δ γ' p) a

Σ-Ty-fst ext γ' x = liftSet x
Σ-Ty-fst (base b) γ' x = Σ-Base-fst b γ' x
Σ-Ty-fst (Π B) γ' f = λ n → Σ-Base-fst B γ' (f n)
Σ-Ty-fst (A [ x ]) γ a = Σ-Ty-fst A γ a
Σ-Ty-fst (A [ w ]') γ a = Σ-Ty-fst A (Wk₁-Alg w γ) a

{-# REWRITE Σ-Sub' #-}

Σ-Ty-snd' ext γ' p' a = ttp
Σ-Ty-snd' (base x) γ' p' a = Σ-Base-snd' x γ' p' a
Σ-Ty-snd' (Π x) γ' p' f = λ n → Σ-Base-snd' x γ' (p' ,P ttp) (f n)
Σ-Ty-snd' (A [ x ]) γ' p' a = Σ-Ty-snd' A γ' (Sub₁-Alg x γ' p') a
Σ-Ty-snd' (A [ w ]') γ' p' a = Σ-Ty-snd' A (Wk₁-Alg w γ') p' a

Σ-Ty-snd {Δ = Δ} A γ' p a = Σ-Ty-snd' A γ' (Σ-Params-snd Δ γ' p) a

Σ-Base-snd {Δ = Δ} A γ' p a = Σ-Base-snd' A γ' (Σ-Params-snd Δ γ' p) a

Σ-Ty-η'' ext γ' p' a = reflp
Σ-Ty-η'' (base x) γ' p' a = Σ-Base-η' x γ' p' a
Σ-Ty-η'' (Π B) γ' p' f = funextp (λ n → Σ-Base-η' B γ' (p' ,P ttp) (f n))
Σ-Ty-η'' (A [ x ]) γ' p' a = Σ-Ty-η'' A γ' (Sub₁-Alg x γ' p') a
Σ-Ty-η'' (A [ w ]') γ' p' a = Σ-Ty-η'' A (Wk₁-Alg w γ') p' a

Σ-Ty-β-fst ext γ' p' a' = from-≡ lift-unlift
Σ-Ty-β-fst (base x) γ' p' a' = Σ-Base-β-fst x γ' p' a'
Σ-Ty-β-fst (Π B) γ' p' a' = funextp (λ x → Σ-Base-β-fst B γ' (p' ,P ttp) (a' x))
Σ-Ty-β-fst (A [ x ]) γ' p' a' = Σ-Ty-β-fst A γ' (Sub₁-Alg x γ' p') a'
Σ-Ty-β-fst (A [ w ]') γ' p' a' = Σ-Ty-β-fst A (Wk₁-Alg w γ') p' a'

{-# TERMINATING #-}
Σ-Tm vz γ p = reflp
Σ-Tm vz1 γ p = reflp
Σ-Tm (vs t) γ p = Σ-Tm t γ (fstP p)
Σ-Tm (ext x) γ p = reflp
Σ-Tm {Γ = Γ} (ctor {Δ = Δ} {∇ = ∇} {A = A} c σ) γ p rewrite Σ-CtorTm c γ = reflp
Σ-Tm (lam t) γ p = funextp (λ n → Σ-Tm t γ (p ,P ttp))
Σ-Tm {p = p , liftSet n} (app t) γ (p' ,P ttp) = cong' (λ f → f n) (Σ-Tm t γ p')
Σ-Tm (t [ σ ]tm) γ p = Σ-Tm t γ (Sub₁-Alg σ γ p)
Σ-Tm (t [ w ]tm') γ p = Σ-Tm t (Wk₁-Alg w γ) p
Σ-Tm (t [ w ]tm'-1) γ p = Σ-Tm t (Wk₁-Alg w γ) p
Σ-Tm (ctor-1 c σ) γ p rewrite Σ-CtorTm c γ = reflp

Σ-CtorTm (v0c {A = ctor _ _}) γ' = refl
Σ-CtorTm (dropc {A = ctor _ _} t) γ' = Σ-CtorTm t (fst γ')
Σ-CtorTm (_[_]ctm {A = ctor _ _} c w) γ' = Σ-CtorTm c (Wk₁-Alg w γ')

Σ-Base-fst ty1 γ x = fst x
Σ-Base-fst (ty2 x₁) γ x = fst x
-- Σ-Base-fst (B [ w ]b') γ x = Σ-Base-fst B (Wk₁-Alg w γ) x

Σ-Tm' : ∀{Γ Δ A s bp γ p} (t : Tm Γ Δ A)
        (γ' : Spec₁-Alg {s = s} Γ γ bp) (p' : Params₁-Alg Δ γ p bp)
     → Tm-Alg t (Σ-Spec Γ γ') (Σ-Params Δ γ' p') ≡ Σ-Ty A γ' p' (Tm₁-Alg t γ' p')
Σ-Tm' t γ' p' = sym (to-≡ (Σ-Tm t γ' p'))
{-# REWRITE Σ-Tm' #-}

Σ-Base-snd' ty1 γ' p' a = snd a
Σ-Base-snd' (ty2 x) γ' p' a = snd a
-- Σ-Base-snd' (A [ w ]b') γ' p' a = Σ-Base-snd' A (Wk₁-Alg w γ') p' a

Σ-Base-η' ty1 γ' p' (a ,p a') = reflp
Σ-Base-η' (ty2 x) γ' p' a = reflp
-- Σ-Base-η' (A [ w ]b') γ' p' a = Σ-Base-η' A (Wk₁-Alg w γ') p' a

Σ-Base-β-fst ty1 γ' p' a' = reflp
Σ-Base-β-fst (ty2 x) γ' p' a' = reflp
-- Σ-Base-β-fst (A [ w ]b') γ' p' a' = Σ-Base-β-fst A (Wk₁-Alg w γ') p' a'

Σ-CtorTm-Alg
  : ∀{Γ Δ A s bp γ p} (γ' : Spec₁-Alg {s = s} Γ γ bp) (p' : Params₁-Alg Δ γ p bp)
    (c : CtorTm Γ (ctor Δ A))
  → CtorTm-Alg c (Σ-Spec Γ γ') (Σ-Params Δ γ' p') ≡ Σ-Base A γ' p' (CtorTm₁-Alg c γ' p')
Σ-CtorTm-Alg {Δ = Δ} γ' p' c = cong (λ f → f (Σ-Params Δ γ' p')) (Σ-CtorTm c γ')
{-# REWRITE Σ-CtorTm-Alg #-}

Σ-CtorTm-Alg'
  : ∀{Γ Δ A s bp γ} (γ' : Spec₁-Alg {s = s} Γ γ bp) (p : Params-Alg Δ (Σ-Spec Γ γ'))
    (c : CtorTm Γ (ctor Δ A))
  → let p' = Σ-Params-snd Δ γ' p
    in CtorTm-Alg c (Σ-Spec Γ γ') p ≡ Σ-Base A γ' p' (CtorTm₁-Alg c γ' p')
Σ-CtorTm-Alg' {Δ = Δ} γ' p c = Σ-CtorTm-Alg γ' (Σ-Params-snd Δ γ' p) c
{-# REWRITE Σ-CtorTm-Alg' #-}
-}

{-

-}

