{-# OPTIONS --prop --rewriting #-}

module predicate.initial where

open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import erased.section
open import predicate.algebra
open import lib hiding (fst ; snd ; fstP ; sndP)
open import hoas-postulated

module InitPred {F₀} (Ω) (γ₀ : Spec₀-Alg Ω F₀) (init₀ : is-initial₀ γ₀) where

  private
    tys : DFam₀ F₀
    tys = (λ _ → P) , (λ _ → El (proj₁ F₀) => P)

    base-to-P : ∀ (w : Wk Ω Γ) (A : Base Γ Δ) (p₀ : STerm (Params₀-Alg Δ F₀))
                 {a₀ : STerm (Base₀-Alg A F₀)} → Term (Base₀-DAlg A a₀ tys) → Term P
    base-to-P w ty1 _ x = x
    base-to-P w (ty2 t) p₀ x = app x (Tm₀-Alg t (Wk₀-Alg w γ₀) p₀)

    ty-to-P : ∀ (w : Wk Ω Γ) (A : Ty Γ Δ) (p₀ : STerm (Params₀-Alg Δ F₀))
              {a₀ : STerm (Ty₀-Alg A F₀)} → Term (Ty₀-DAlg A a₀ tys) → Term P
    ty-to-P w (ext x) _ a = Top
    ty-to-P w (base x) = base-to-P w x
    ty-to-P w (Π A B) p₀ f =
      Pip A (λ x → base-to-P w B (pair p₀ x) (app f x))
    ty-to-P w (A [ σ ]) p₀ a = ty-to-P w A (Sub₀-Alg σ (Wk₀-Alg w γ₀) p₀) a
    ty-to-P w (A [ w' ]') p₀ a = ty-to-P (w ∘w w') A p₀ a

    to-P : ∀ (w : Wk Ω Γ) (Δ : Params Γ)
             {p₀ : STerm (Params₀-Alg Δ F₀)} → Term (Params₀-DAlg Δ p₀ tys) → Term P
    to-P w ● x = Top
    to-P w (Δ ‣‣ A) {p₀} x =
      SigmaP h-Δ λ _ → h-A
      where
        h-Δ = to-P w Δ (hoas-postulated.fst x)
        h-A = ty-to-P w A (hoas-postulated.fst p₀) (hoas-postulated.snd x)
    to-P w (Δ [ w' ]p) x = to-P (w ∘w w') Δ x

    alg : Spec₀-DAlg Ω γ₀ tys
    alg {ctor Δ ty1} c = lam λ p₀ → lam λ pd₀ → to-P Wk.Id Δ pd₀
    alg {ctor Δ (ty2 t)} c = lam λ p₀ → lam λ pd₀ → lam λ a →
      SigmaP (to-P Wk.Id Δ pd₀) λ _ →
      hoas-postulated.Id (proj₁ F₀) a (Tm₀-Alg t γ₀ p₀)

    the-init = init₀ alg

    m₀ = lib.fst the-init

  Pred1 : STerm (proj₁ F₀) → Term P
  Pred1 = app (proj₁ (lib.fst the-init))

  Pred2 : STerm (proj₁ F₀) → STerm (proj₂ F₀) → Term P
  Pred2 a b = proj₂ (lib.fst the-init) $ b $ a

  preds : Fam₁ F₀
  preds = Pred1 , Pred2

  private
    sect-≡-B : (w : Wk Ω Γ) (B : Base Γ Δ) {p₀ : _} {a₀ : _}
             → Base₁-Alg B (Wk₀-Alg w γ₀) p₀ a₀ preds
             ≡ base-to-P w B p₀ (Base₀-Sect B a₀ m₀)
    sect-≡-B w ty1 = refl
    sect-≡-B w (ty2 x) = refl

    sect-≡-T : (w : Wk Ω Γ) (B : Ty Γ Δ) {p₀ : _} {a₀ : _}
             → Ty₁-Alg B (Wk₀-Alg w γ₀) p₀ a₀ preds
             ≡ ty-to-P w B p₀ (Ty₀-Sect B a₀ m₀)
    sect-≡-T w (ext x) = refl
    sect-≡-T w (base x) = sect-≡-B w x
    sect-≡-T w (Π A B) = cong (Pip A) (funext (λ a → sect-≡-B w B))
    sect-≡-T w (A [ x ]) = sect-≡-T w A
    sect-≡-T w (A [ w' ]') = sect-≡-T (w ∘w w') A

    sect-≡-P : (w : Wk Ω Γ) (Δ : Params Γ) {p₀ : _}
             → Params₁-Alg Δ (Wk₀-Alg w γ₀) p₀ preds
             ≡ to-P w Δ (Params₀-Sect Δ p₀ m₀)
    sect-≡-P w ● = refl
    sect-≡-P w (Δ ‣‣ A) {p₀}
      rewrite sect-≡-P w Δ {hoas-postulated.fst p₀} | sect-≡-T w A {hoas-postulated.fst p₀} {hoas-postulated.snd p₀} =
      refl
    sect-≡-P w (Δ [ x ]p) = sect-≡-P (w ∘w x) Δ

    sec-lemma : (w : Wk Ω Γ) (Δ : Params Γ) {p₀ : _}
              → PTerm (Params₁-Alg Δ (Wk₀-Alg w γ₀) p₀ preds)
              → PTerm (to-P w Δ (Params₀-Sect Δ p₀ m₀))
    sec-lemma w Δ {p₀} p₁ = substP PTerm (sect-≡-P w Δ {p₀}) p₁

    sec-lemma' : (w : Wk Ω Γ) (Δ : Params Γ) {p₀ : _}
               → PTerm (to-P w Δ (Params₀-Sect Δ p₀ m₀))
               → PTerm (Params₁-Alg Δ (Wk₀-Alg w γ₀) p₀ preds)
    sec-lemma' w Δ {p₀} p₁ = substP PTerm (sym (sect-≡-P w Δ {p₀})) p₁

    Pred1-≡ : (c : CtorTm Ω (ctor Δ ty1)) (p₀ : _)
            → Pred1 (CtorTm₀-Alg c γ₀ $ p₀) ≡p (alg c $ p₀ $ Params₀-Sect Δ p₀ m₀)
    Pred1-≡ c p = lib.snd the-init c p

    Pred2-≡ : ∀{t} (c : CtorTm Ω (ctor Δ (ty2 t))) (p₀ : _) {a₀ : _}
            → Pred2 a₀ (CtorTm₀-Alg c γ₀ $ p₀)
            ≡p (alg c $ p₀ $ Params₀-Sect Δ p₀ m₀ $ a₀)
    Pred2-≡ c p₀ {a₀} = cong' (λ f → app f a₀) (lib.snd the-init c p₀)

    is-pred-alg' : Spec₁-Alg' Ω γ₀ preds
    is-pred-alg' {ctor Δ ty1} c = lamp λ p₀ → lamP λ p₁
      → let aux : PTerm (to-P Wk.Id Δ (Params₀-Sect Δ p₀ m₀))
            aux = sec-lemma _ Δ p₁
            goal : PTerm (Pred1 (CtorTm₀-Alg c γ₀ $ p₀))
            goal = transp-P (λ x → PTerm x) (sym' (Pred1-≡ c p₀)) aux
        in goal
    is-pred-alg' {ctor Δ (ty2 x)} c = lamp λ p₀ → lamP λ p₁
      → let aux : PTerm (alg c $ p₀ $ Params₀-Sect Δ p₀ m₀ $ Tm₀-Alg x γ₀ p₀)
            aux = pairP (sec-lemma _ Δ p₁) (Refl _)
            goal : PTerm (Pred2 (Tm₀-Alg x γ₀ p₀) (CtorTm₀-Alg c γ₀ $ p₀))
            goal = transp-P (λ x → PTerm x) (sym' (Pred2-≡ c p₀)) aux
        in goal

  init-is-pred-alg : Spec₁-Alg Ω γ₀ preds
  init-is-pred-alg = to-Spec₁-Alg Ω is-pred-alg'

  pred-inv : (c : CtorTm Ω (ctor Δ B)) (p₀ : _)
           → PTerm (Base₁-Alg B γ₀ p₀ (CtorTm₀-Alg c γ₀ $ p₀) preds)
           → PTerm (Params₁-Alg Δ γ₀ p₀ preds)
  pred-inv {Δ = Δ} {B = ty1} c p₀ a₁ =
    sec-lemma' Wk.Id Δ (transp-P (λ x → PTerm x) (Pred1-≡ c p₀) a₁)
  pred-inv {Δ} {B = ty2 x} c p₀ a₁ =
    sec-lemma' Wk.Id Δ (fstP aux)
    where
      have : PTerm (Pred2 (Tm₀-Alg x γ₀ p₀) (CtorTm₀-Alg c γ₀ $ p₀))
      have = a₁
      aux : PTerm (alg c $ p₀ $ Params₀-Sect Δ p₀ m₀ $ Tm₀-Alg x γ₀ p₀)
      aux = transp-P (λ x → PTerm x) (Pred2-≡ c p₀) a₁

  pred-ix-inv : ∀{t} (c : CtorTm Ω (ctor Δ (ty2 t))) (p₀ : _) (a₀ : _)
              → PTerm (Pred2 a₀ (CtorTm₀-Alg c γ₀ $ p₀))
              → PTerm (hoas-postulated.Id _ a₀ (Tm₀-Alg t γ₀ p₀))
  pred-ix-inv {Δ = Δ} {t = t} c p₀ a₀ x = sndP aux
    where
      aux : PTerm (alg c $ p₀ $ Params₀-Sect Δ p₀ m₀ $ a₀)
      aux = transp-P (λ x → PTerm x) (Pred2-≡ c p₀) x
