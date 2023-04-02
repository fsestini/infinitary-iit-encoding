{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

module predicate.recursive where

open import IIT.spec
open import IIT.algebra
open import erased.algebra
open import erased.section
open import predicate.algebra
open import lib

module _ (Ω : Spec) {F₀} (ω₀ : Spec₀-Alg Ω F₀) (init₀ : is-initial₀ ω₀) where

  private
    preds-ty : DFam₀ F₀
    preds-ty = (λ a₀ → Prop) , λ b₀ → proj₁ F₀ → Prop

    B-to-Prop : (A : Base Γ Δ) (w : Wk Ω Γ) (p₀ : Params₀-Alg Δ F₀) {a₀ : _} → Base₀-DAlg A preds-ty a₀ → Prop
    B-to-Prop ty1 w p₀ a = a
    B-to-Prop (ty2 x) w p₀ a = a (Tm₀-Alg x (Wk₀-Alg w ω₀) p₀)

    T-to-Prop : (A : Ty Γ Δ) (w : Wk Ω Γ) (p₀ : Params₀-Alg Δ F₀) {a₀ : _} → Ty₀-DAlg A preds-ty a₀ → Prop
    T-to-Prop (ext x) w p₀ a₀ᴰ = ⊤p
    T-to-Prop (base x) = B-to-Prop x
    T-to-Prop (Π A B) w p₀ f₀ᴰ = (x : El A) → B-to-Prop B w (p₀ , x) (f₀ᴰ x)
    T-to-Prop (A [ x ]) w p a = T-to-Prop A w (Sub₀-Alg x (Wk₀-Alg w ω₀) p) a
    T-to-Prop (A [ w' ]') w p₀ a₀ᴰ = T-to-Prop A (w ∘w w') p₀ a₀ᴰ

    P-to-Prop : (Δ : Params Γ) (w : Wk Ω Γ) {p₀ : _} → Params₀-DAlg Δ preds-ty p₀ → Prop
    P-to-Prop ● _ p₀ᴰ = ⊤p
    P-to-Prop (Δ ‣‣ A) w {p₀ , _} (p₀ᴰ , a₀ᴰ) = P-to-Prop Δ w p₀ᴰ ×p T-to-Prop A w p₀ a₀ᴰ
    P-to-Prop (Δ [ x ]p) w p₀ᴰ = P-to-Prop Δ (w ∘w x) p₀ᴰ

    preds-alg : Spec₀-DAlg Ω ω₀ preds-ty
    preds-alg {ctor Δ ty1} c {p₀} p₀ᴰ = P-to-Prop Δ Id p₀ᴰ
    preds-alg {ctor Δ (ty2 x)} c {p₀} p₀ᴰ a₀ =
      P-to-Prop Δ Id p₀ᴰ ×p (a₀ ≡p Tm₀-Alg x ω₀ p₀)

    ps = init₀ preds-alg

  Inits₁ : BasePreds F₀
  Inits₁ = proj₁ (fst ps) , λ a b → proj₂ (fst ps) b a

  private
    inits₁-alg' : Spec₁-Alg' Ω ω₀ Inits₁
    inits₁-alg' {ctor Δ ty1} c p₁ = {!!}
    inits₁-alg' {ctor Δ (ty2 x)} c p₁ = {!!}

  Init₁-alg : Spec₁-Alg Ω ω₀ Inits₁
  Init₁-alg = to-Spec₁-Alg _ _ inits₁-alg'

  postulate
    pred-inv : (c : CtorTm Ω (ctor Δ B)) (p₀ : _)
             → Base₁-Alg B ω₀ p₀ (CtorTm₀-Alg c ω₀ p₀) Inits₁
             → Params₁-Alg Δ ω₀ p₀ Inits₁
    pred-ix-inv : ∀{t} (c : CtorTm Ω (ctor Δ (ty2 t))) (p₀ : _) (a₀ : _)
                → proj₂ Inits₁ a₀ (CtorTm₀-Alg c ω₀ p₀)
                → a₀ ≡p Tm₀-Alg t ω₀ p₀
{-
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
-}

  -- Init₁-params-inv : (c : CtorTm Ω (ctor Δ B)) (p₀ : _)
  --                  → Base₁-Alg B ω₀ p₀ (CtorTm₀-Alg c ω₀ p₀) Inits₁
  --                  → Params₁-Alg Δ ω₀ p₀ Inits₁
  -- Init₁-params-inv {B = ty1} c p₀ x = {!!}
  -- Init₁-params-inv {B = ty2 x₁} c p₀ x = {!!}

  -- Init₁-ix-inv : ∀{t} (c : CtorTm Ω (ctor Δ (ty2 t))) (p₀ : _) (a₀ : _)
  --              → proj₂ Inits₁ a₀ (CtorTm₀-Alg c ω₀ p₀)
  --              → a₀ ≡p Tm₀-Alg t ω₀ p₀
  -- Init₁-ix-inv c p₀ a₀ x = {!!}
