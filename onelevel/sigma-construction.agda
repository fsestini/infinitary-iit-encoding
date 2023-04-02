{-# OPTIONS --prop --rewriting --show-irrelevant #-}

module sigma-construction where

open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import predicate.algebra
open import lib

Σ-Fam : (F₀ : Set × Set) → BasePreds F₀ → Fam
Σ-Fam (C , T) (P , Q) = (Σp C P) , λ x → Σp T (Q (fst x))

Σ-Spec : (Γ : Spec) {γ : Spec₀-Alg Γ F₀} → Spec₁-Alg Γ γ F₁
       → Spec-Alg Γ (Σ-Fam F₀ F₁)
Σ-Ctor : (A : Ctor Γ) {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
         {a : Ctor₀-Alg A F₀} (a' : Ctor₁-Alg A γ a F₁)
       → Ctor-Alg A (Σ-Spec Γ γ')
Σ-Params : (Δ : Params Γ) {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
           {p : Params₀-Alg Δ F₀} (p' : Params₁-Alg Δ γ p F₁)
         → Params-Alg Δ (Σ-Spec Γ γ')

Σ-Base : (A : Base Γ Δ)
         {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
         {p : Params₀-Alg Δ F₀} (p' : Params₁-Alg Δ γ p F₁)
         {a : Base₀-Alg A F₀} (a' : Base₁-Alg A γ p a F₁)
       → Base-Alg A (Σ-Spec Γ γ') (Σ-Params Δ γ' p')

Σ-Ty : (A : Ty Γ Δ)
       {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
       {p : Params₀-Alg Δ F₀} (p' : Params₁-Alg Δ γ p F₁)
       {a : Ty₀-Alg A F₀} (a' : Ty₁-Alg A γ p a F₁)
     → Ty-Alg A (Σ-Spec Γ γ') (Σ-Params Δ γ' p')

Σ-CtorTm : (t : CtorTm Γ C)
        {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
     → CtorTm-Alg t (Σ-Spec Γ γ')
     ≡ Σ-Ctor C γ' (CtorTm₁-Alg t γ')

Σ-Sub : (σ : Sub {Γ} ∇ Δ) {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
           {p : Params₀-Alg ∇ F₀} (p' : Params₁-Alg ∇ γ p F₁)
       → Σ-Params Δ γ' (Sub₁-Alg σ γ' p') ≡p Sub-Alg σ (Σ-Params ∇ γ' p')
Σ-Sub' : (σ : Sub {Γ} ∇ Δ) {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
           {p : Params₀-Alg ∇ F₀} (p' : Params₁-Alg ∇ γ p F₁)
       → Sub-Alg σ (Σ-Params ∇ γ' p') ≡ Σ-Params Δ γ' (Sub₁-Alg σ γ' p')
Σ-Wk : ∀ Γ (w : Wk Ω Γ)
       {γ : Spec₀-Alg _ F₀} (γ' : Spec₁-Alg _ γ F₁)
     → Σ-Spec Γ (Wk₁-Alg w γ') ≡ Wk-Alg w (Σ-Spec Ω γ')
Σ-Wk' : ∀ Γ (w : Wk Ω Γ)
       {γ : Spec₀-Alg _ F₀} (γ' : Spec₁-Alg _ γ F₁)
     → Wk-Alg w (Σ-Spec Ω γ') ≡ Σ-Spec Γ (Wk₁-Alg w γ')

Σ-Tm : (t : Tm Γ Δ A) {γ₀ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ₀ F₁) {p : _} (p' : Params₁-Alg Δ γ₀ p F₁)
     → Σ-Ty A γ' p' (Tm₁-Alg t γ' p') ≡p Tm-Alg t (Σ-Spec Γ γ') (Σ-Params Δ γ' p')

Σ-Params-fst : (Δ : Params Γ) {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
           → Params-Alg Δ (Σ-Spec Γ γ') → Params₀-Alg Δ F₀
Σ-Ty-fst : (A : Ty Γ Δ) {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁) {p : _}
         → Ty-Alg A (Σ-Spec Γ γ') p → Ty₀-Alg A F₀
Σ-Base-fst : (A : Base Γ Δ) {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁) {p : _}
         → Base-Alg A (Σ-Spec Γ γ') p → Base₀-Alg A F₀

Σ-Params-snd : (Δ : Params Γ) {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
             (p : Params-Alg Δ (Σ-Spec Γ γ'))
           → Params₁-Alg Δ γ (Σ-Params-fst Δ γ' p) F₁

Σ-Ty-snd : (A : Ty Γ Δ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
            (p : _) (a : Ty-Alg A (Σ-Spec Γ γ') p)
         → Ty₁-Alg A γ (Σ-Params-fst Δ γ' p) (Σ-Ty-fst A γ' a) F₁
Σ-Ty-snd' : (A : Ty Γ Δ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
            {p : _} (p' : Params₁-Alg Δ γ p _) (a : Ty-Alg A (Σ-Spec Γ γ') (Σ-Params Δ γ' p'))
         → Ty₁-Alg A γ p (Σ-Ty-fst A γ' a) F₁

Σ-Params-β-fst : (Δ : Params Γ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
                 {p : Params₀-Alg Δ F₀} (p' : Params₁-Alg Δ γ p F₁)
               → Σ-Params-fst Δ γ' (Σ-Params Δ γ' p') ≡ p

Σ-Ty-β-fst : (A : Ty Γ Δ)
              {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
              {p : Params₀-Alg Δ F₀} (p' : Params₁-Alg Δ γ p F₁)
              {a : Ty₀-Alg A F₀} (a' : Ty₁-Alg A γ p a F₁)
           → Σ-Ty-fst A γ' (Σ-Ty A γ' p' a') ≡p a

Σ-Base-snd : (A : Base Γ Δ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
            (p : _) (a : Base-Alg A (Σ-Spec Γ γ') p)
         → Base₁-Alg A γ (Σ-Params-fst Δ γ' p) (Σ-Base-fst A γ' a) F₁
Σ-Base-snd' : (A : Base Γ Δ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
               {p : _} (p' : Params₁-Alg Δ γ p _) (a : Base-Alg A (Σ-Spec Γ γ') (Σ-Params Δ γ' p'))
         → Base₁-Alg A γ p (Σ-Base-fst A γ' a) F₁



Σ-Base-β-fst : (A : Base Γ Δ)
                {γ : Spec₀-Alg Γ F₀} (γ' : Spec₁-Alg Γ γ F₁)
                {p : Params₀-Alg Δ F₀} (p' : Params₁-Alg Δ γ p F₁)
                {a : Base₀-Alg A F₀} (a' : Base₁-Alg A γ p a F₁)
             → Σ-Base-fst A γ' (Σ-Base A γ' p' a') ≡p a

Σ-Params-η : (Δ : Params Γ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
             (p : Params-Alg Δ (Σ-Spec Γ γ'))
           → Σ-Params Δ γ' {Σ-Params-fst Δ γ' p} (Σ-Params-snd Δ γ' p) ≡ p

Σ-Ty-η : (A : Ty Γ Δ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
            (p : _) (a : Ty-Alg A (Σ-Spec Γ γ') p)
         → transp (Ty-Alg A _) (from-≡ (Σ-Params-η Δ γ' p)) (Σ-Ty A γ' (Σ-Params-snd Δ γ' p) (Σ-Ty-snd A γ' p a))
         ≡p a

Σ-Spec init x = tt
-- Σ-Spec (Γ ‣ A) (γ' ,p a') = Σ-Spec Γ γ' , Σ-Ctor A γ' a'
Σ-Spec (Γ ‣ A) (γ₁ ,P a₁) = Σ-Spec Γ γ₁ , Σ-Ctor A γ₁ a₁

Σ-Wk Γ Id γ' = refl
Σ-Wk Γ Drop γ' = refl
Σ-Wk Γ (w ∘w w') γ' =
  trans (Σ-Wk _ w' (Wk₁-Alg w γ')) (cong (Wk-Alg w') (Σ-Wk _ w γ'))

Σ-Wk' x y z = sym (Σ-Wk x y z)
{-# REWRITE Σ-Wk' #-}

Σ-Params ● γ' p' = tt
Σ-Params (Δ ‣‣ A) γ' (p' ,P a') = Σ-Params Δ γ' p' , Σ-Ty A γ' p' a'
Σ-Params (Δ [ x ]p) γ₁ p₁ = Σ-Params Δ (Wk₁-Alg x γ₁) p₁

Σ-Params-fst ● γ' x = tt
Σ-Params-fst (Δ ‣‣ A) γ' (p' , x') = Σ-Params-fst Δ γ' p' , Σ-Ty-fst A γ' x' 
Σ-Params-fst (Δ [ x ]p) γ p = Σ-Params-fst Δ (Wk₁-Alg x γ) p

Σ-Params-snd ● γ' p = ttp
Σ-Params-snd (Δ ‣‣ A) γ' (p , a) = Σ-Params-snd Δ γ' p ,P Σ-Ty-snd A γ' p a
Σ-Params-snd (Δ [ x ]p) γ p = Σ-Params-snd Δ (Wk₁-Alg x γ) p

Σ-Ty (ext A) γ' p' {a} a' = a
Σ-Ty (base x) γ' p' a' = Σ-Base x γ' p' a'
Σ-Ty (Π A B) γ' p' f = λ n → Σ-Base B γ' (p' ,P ttp) (f n)
Σ-Ty (A [ x ]) γ₁ p₁ a = transp (Ty-Alg A _) (Σ-Sub x γ₁ p₁) (Σ-Ty A γ₁ (Sub₁-Alg x γ₁ p₁) a)
Σ-Ty (A [ w ]') γ₁ p₁ a = Σ-Ty A (Wk₁-Alg w γ₁) p₁ a

Σ-Sub Id γ' p' = reflp
Σ-Sub (Ext σ x) γ' p' = Σ-≡p (Σ-Sub σ γ' p') (Σ-Tm x γ' p')
Σ-Sub Drop γ' p' = reflp
Σ-Sub (σ ∘ τ) γ' p' =
  trans' (Σ-Sub τ γ' (Sub₁-Alg σ γ' p')) (cong' (Sub-Alg τ) (Σ-Sub σ γ' p'))
Σ-Sub (σ [ w ]ws) γ' p' = Σ-Sub σ (Wk₁-Alg w γ') p'

Σ-Sub' σ γ' p' = sym (to-≡ (Σ-Sub σ γ' p'))


Σ-Base ty1 γ' p' a' = _ ,p a'
Σ-Base {F₁ = F₁} (ty2 x) γ' p' a' =
  _ ,p transp-P (λ z → proj₂ F₁ z _) (cong' fst (Σ-Tm x γ' p')) a'
-- Σ-Base (B [ w ]b') γ p a = Σ-Base B (Wk₁-Alg w γ) p a

Σ-Base[]b'
  : (A : Base Γ Δ) (w : Wk Ω Γ)
    {γ : Spec₀-Alg Ω F₀} (γ' : Spec₁-Alg Ω γ F₁)
    {p : Params₀-Alg Δ F₀} (p' : Params₁-Alg Δ _ p F₁)
    {a : Base₀-Alg A F₀} (a' : Base₁-Alg A _ p a F₁)
  → Σ-Base (A [ w ]b') γ' p' a' ≡ Σ-Base A (Wk₁-Alg w γ') p' a'
Σ-Base[]b' ty1 w γ' p' a' = refl
Σ-Base[]b' (ty2 x) w γ' p' a' = refl
{-# REWRITE Σ-Base[]b' #-}

Σ-Params-β-fst ● γ' p' = refl
Σ-Params-β-fst (Δ ‣‣ x) γ' (p ,P q) rewrite Σ-Params-β-fst Δ γ' p | to-≡ (Σ-Ty-β-fst x γ' p q) = refl
Σ-Params-β-fst (Δ [ x ]p) γ p = Σ-Params-β-fst Δ (Wk₁-Alg x γ) p
{-# REWRITE Σ-Params-β-fst #-}

Σ-Params-η ● γ' p = refl
Σ-Params-η (Δ ‣‣ A) γ' (p , a) = to-≡ (Σ-≡p (from-≡ (Σ-Params-η Δ γ' p)) (Σ-Ty-η A γ' p a))
Σ-Params-η (Δ [ x ]p) γ p = Σ-Params-η Δ (Wk₁-Alg x γ) p
{-# REWRITE Σ-Params-η #-}

Σ-Ctor (ctor {Γ = Γ} Δ A) γ' a' p =
  Σ-Base A γ' (Σ-Params-snd Δ γ' p) (a' (Σ-Params-snd Δ γ' p))

Σ-Ty-η'' : (A : Ty Γ Δ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
            {p : _} (p' : Params₁-Alg Δ γ p _) (a : Ty-Alg A (Σ-Spec Γ γ') (Σ-Params Δ γ' p'))
         → Σ-Ty A γ' p' (Σ-Ty-snd' A γ' p' a)
         ≡p a

Σ-Ty-η {Δ = Δ} A γ' p a = Σ-Ty-η'' A γ' (Σ-Params-snd Δ γ' p) a

Σ-Base-η : (A : Base Γ Δ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
            (p : _) (a : Base-Alg A (Σ-Spec Γ γ') p)
         → Σ-Base A γ' (Σ-Params-snd Δ γ' p) (Σ-Base-snd A γ' p a) ≡p a

Σ-Base-η' : (A : Base Γ Δ) {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁)
             {p : _} (p' : Params₁-Alg Δ γ p F₁) (a : Base-Alg A (Σ-Spec Γ γ') (Σ-Params Δ γ' p'))
         → Σ-Base A γ' p' (Σ-Base-snd' A γ' p' a)
         ≡p a

Σ-Base-η {Δ = Δ} A γ' p a = Σ-Base-η' A γ' (Σ-Params-snd Δ γ' p) a

Σ-Ty-fst (ext A) γ' x = x
Σ-Ty-fst (base b) γ' x = Σ-Base-fst b γ' x
Σ-Ty-fst (Π A B) γ' f = λ n → Σ-Base-fst B γ' (f n)
Σ-Ty-fst (A [ x ]) γ a = Σ-Ty-fst A γ a
Σ-Ty-fst (A [ w ]') γ a = Σ-Ty-fst A (Wk₁-Alg w γ) a

{-# REWRITE Σ-Sub' #-}

Σ-Ty-snd' (ext A) γ' p' a = ttp
Σ-Ty-snd' (base x) γ' p' a = Σ-Base-snd' x γ' p' a
Σ-Ty-snd' (Π A x) γ' p' f = λ n → Σ-Base-snd' x γ' (p' ,P ttp) (f n)
Σ-Ty-snd' (A [ x ]) γ' p' a = Σ-Ty-snd' A γ' (Sub₁-Alg x γ' p') a
Σ-Ty-snd' (A [ w ]') γ' p' a = Σ-Ty-snd' A (Wk₁-Alg w γ') p' a

Σ-Ty-snd {Δ = Δ} A γ' p a = Σ-Ty-snd' A γ' (Σ-Params-snd Δ γ' p) a

Σ-Base-snd {Δ = Δ} A γ' p a = Σ-Base-snd' A γ' (Σ-Params-snd Δ γ' p) a

Σ-Ty-η'' (ext A) γ' p' a = reflp
Σ-Ty-η'' (base x) γ' p' a = Σ-Base-η' x γ' p' a
Σ-Ty-η'' (Π A B) γ' p' f = funextp (λ n → Σ-Base-η' B γ' (p' ,P ttp) (f n))
Σ-Ty-η'' (A [ x ]) γ' p' a = Σ-Ty-η'' A γ' (Sub₁-Alg x γ' p') a
Σ-Ty-η'' (A [ w ]') γ' p' a = Σ-Ty-η'' A (Wk₁-Alg w γ') p' a

Σ-Ty-β-fst (ext A) γ' p' a' = reflp
Σ-Ty-β-fst (base x) γ' p' a' = Σ-Base-β-fst x γ' p' a'
Σ-Ty-β-fst (Π A B) γ' p' a' = funextp (λ x → Σ-Base-β-fst B γ' (p' ,P ttp) (a' x))
Σ-Ty-β-fst (A [ x ]) γ' p' a' = Σ-Ty-β-fst A γ' (Sub₁-Alg x γ' p') a'
Σ-Ty-β-fst (A [ w ]') γ' p' a' = Σ-Ty-β-fst A (Wk₁-Alg w γ') p' a'

{-# TERMINATING #-}
Σ-Tm vz γ p = reflp
Σ-Tm vz1 γ p = reflp
Σ-Tm (vs t) γ p = Σ-Tm t γ (fstP p)
Σ-Tm (ext A x) γ p = reflp
Σ-Tm {Γ = Γ} (ctor {Δ = Δ} {∇ = ∇} {A = A} c σ) γ p = sym' (from-≡ (cong (λ f → f (Σ-Params Δ γ (Sub₁-Alg σ γ p))) (Σ-CtorTm c γ)))
Σ-Tm (lam t) γ p = funextp (λ n → Σ-Tm t γ (p ,P ttp))
Σ-Tm (app t) γ {p = p , n} (p' ,P ttp) = cong' (λ f → f n) (Σ-Tm t γ p')
Σ-Tm (t [ σ ]tm) γ p = Σ-Tm t γ (Sub₁-Alg σ γ p)
Σ-Tm (t [ w ]tm') γ p = Σ-Tm t (Wk₁-Alg w γ) p
Σ-Tm (t [ w ]tm'-1) γ p = Σ-Tm t (Wk₁-Alg w γ) p
Σ-Tm (ctor-1 {Δ = Δ} c σ) γ p = sym' (from-≡ (cong (λ f → f (Σ-Params Δ γ (Sub₁-Alg σ γ p))) (Σ-CtorTm c γ)))
Σ-Tm (app-U t f) γ p = cong' (λ x → f x) (Σ-Tm t γ p)

Σ-CtorTm (v0c {A = ctor _ _}) γ' = refl
Σ-CtorTm (dropc {A = ctor _ _} t) (γ₁ ,P a₁) = Σ-CtorTm t γ₁
Σ-CtorTm (_[_]ctm {A = ctor _ _} c w) γ' = Σ-CtorTm c (Wk₁-Alg w γ')
{-# REWRITE Σ-CtorTm #-}

Σ-Base-fst ty1 γ x = fst x
Σ-Base-fst (ty2 x₁) γ x = fst x

Σ-Tm' : (t : Tm Γ Δ A)
        {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁) {p : _}(p' : Params₁-Alg Δ γ p F₁)
     → Tm-Alg t (Σ-Spec Γ γ') (Σ-Params Δ γ' p') ≡ Σ-Ty A γ' p' (Tm₁-Alg t γ' p')
Σ-Tm' t γ' p' = sym (to-≡ (Σ-Tm t γ' p'))
{-# REWRITE Σ-Tm' #-}

Σ-Base-snd' ty1 γ' p' a = snd a
Σ-Base-snd' (ty2 x) γ' p' a = snd a

Σ-Base-η' ty1 γ' p' (a ,p a') = reflp
Σ-Base-η' (ty2 x) γ' p' a = reflp

Σ-Base-β-fst ty1 γ' p' a' = reflp
Σ-Base-β-fst (ty2 x) γ' p' a' = reflp

{-
Σ-CtorTm-Alg
  : {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg Γ γ F₁) {p : _} (p' : Params₁-Alg Δ γ p F₁)
    (c : CtorTm Γ (ctor Δ B))
  → CtorTm-Alg c (Σ-Spec Γ γ') (Σ-Params Δ γ' p') ≡ Σ-Base B γ' p' (CtorTm₁-Alg c γ' p')
Σ-CtorTm-Alg {Δ = Δ} γ' p' c = cong (λ f → f (Σ-Params Δ γ' p')) (Σ-CtorTm c γ')
{-# REWRITE Σ-CtorTm-Alg #-}

Σ-CtorTm-Alg'
  : ∀{Γ Δ A s bp} {γ : Spec₀-Alg Γ F₀}(γ' : Spec₁-Alg {s = F₀} Γ γ F₁) (p : Params-Alg Δ (Σ-Spec Γ γ'))
    (c : CtorTm Γ (ctor Δ A))
  → let p' = Σ-Params-snd Δ γ' p
    in CtorTm-Alg c (Σ-Spec Γ γ') p ≡ Σ-Base A γ' p' (CtorTm₁-Alg c γ' p')
Σ-CtorTm-Alg' {Δ = Δ} γ' p c = Σ-CtorTm-Alg γ' (Σ-Params-snd Δ γ' p) c
{-# REWRITE Σ-CtorTm-Alg' #-}
-}
