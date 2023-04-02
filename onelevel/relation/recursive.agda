{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

module relation.recursive where

open import lib
open import IIT.spec
open import erased.algebra
open import erased.section
open import predicate.algebra
open import predicate.recursive
open import IIT.algebra
open import relation.algebra
open import sigma-construction

--------------------------------------------------------------------------------

module _ (Ω : Spec) {F₀} (ω₀ : Spec₀-Alg Ω F₀) (init₀ : is-initial₀ ω₀)
                   {Y : _} (γ : Spec-DAlg Ω (Σ-Spec Ω (Init₁-alg Ω ω₀ init₀)) Y) where

  private

    Ω-P = Inits₁ Ω ω₀ init₀
    A₁ = proj₁ (Inits₁ Ω ω₀ init₀)
    B₁ = proj₂ (Inits₁ Ω ω₀ init₀)
    AB = Σ-Fam F₀ (Inits₁ Ω ω₀ init₀)

    ω₁ = Init₁-alg Ω ω₀ init₀
    σ-alg = Σ-Spec Ω ω₁
    
    rel-tys : DFam₀ F₀
    rel-tys = (λ a₀ → (a₁ : A₁ a₀) → proj₁ Y (a₀ ,p a₁) → Set)
            , (λ b₀ → (a : _) (aᴰ : proj₁ Y a) (b₁ : B₁ (fst a) b₀) → proj₂ Y a aᴰ (b₀ ,p b₁) → Set)

    B-to-Set : (B : Base Γ Δ) (w : Wk Ω Γ) {p : _} {p₁ : Params₁-Alg Δ _ p Ω-P}
               {pd : Params-DAlg Δ _ _ (Σ-Params Δ (Wk₁-Alg w ω₁) p₁)}
               {a : _} → Base₀-DAlg B rel-tys a
             → (a₁ : Base₁-Alg B (Wk₀-Alg w ω₀) p a Ω-P)
             → Base-DAlg B (Wk-DAlg w γ) pd (Σ-Base B (Wk₁-Alg w ω₁) p₁ a₁)
             → Set
    B-to-Set ty1 w a a1 ad = a a1 ad
    B-to-Set (ty2 x) w a a1 ad = a _ _ a1 ad

    T-to-Set : (B : Ty Γ Δ) (w : Wk Ω Γ) {p : _} {p₁ : Params₁-Alg Δ _ p Ω-P}
               {pd : Params-DAlg Δ _ _ (Σ-Params Δ (Wk₁-Alg w ω₁) p₁)}
               {a : _} → Ty₀-DAlg B rel-tys a
             → (a₁ : Ty₁-Alg B (Wk₀-Alg w ω₀) p a Ω-P)
             → Ty-DAlg B (Wk-DAlg w γ) pd (Σ-Ty B (Wk₁-Alg w ω₁) p₁ a₁)
             → Set
    T-to-Set (ext x₁) w x a₁ ad = ⊤
    T-to-Set (base B) = B-to-Set B
    T-to-Set (Π A B) w f f₁ fd = (x : El A) → B-to-Set B w (f x) (f₁ x) (fd x)
    T-to-Set (A [ σ ]) w a a₁ ad = T-to-Set A w a a₁ ad
    T-to-Set (A [ w' ]') w x a₁ ad = T-to-Set A (w ∘w w') x a₁ ad

    P-to-Set : (Δ : Params Γ) (w : Wk Ω Γ) {p₀ : _} {p₁ : _}
      (pᴰ : Params-DAlg Δ _ (Wk-DAlg w γ) (Σ-Params Δ (Wk₁-Alg w ω₁) {p₀} p₁))
      → Params₀-DAlg Δ rel-tys p₀ → Set
    P-to-Set ● w pd p₀ᴰ = ⊤
    P-to-Set (Δ ‣‣ A) w (pd , ad) (p₀ᴰ , a₀ᴰ) =
      P-to-Set Δ w pd p₀ᴰ × T-to-Set A w a₀ᴰ _ ad
    P-to-Set (Δ [ x ]p) w pd p₀ᴰ = P-to-Set Δ (w ∘w x) pd p₀ᴰ

    rel-alg : Spec₀-DAlg Ω ω₀ rel-tys
    rel-alg {ctor Δ ty1} c p₀ᴰ a₁ aᴰ =
      Σ (Params-DAlg Δ _ γ (Σ-Params Δ _ p₁)) λ pd →
        Σ (P-to-Set Δ Id pd p₀ᴰ) λ pr →
          aᴰ ≡ CtorTm-DAlg c γ pd
      where p₁ = pred-inv _ _ init₀ c _ a₁
    rel-alg {ctor Δ (ty2 t)} c p₀ᴰ a aᴰ b₁ bᴰ = {!!}

    sc = init₀ rel-alg

  Init-R : RelTys _ Y
  Init-R = (λ a aᴰ → proj₁ (fst sc) (fst a) (snd a) aᴰ)
         , (λ a aᴰ b bᴰ → proj₂ (fst sc) (fst b) a aᴰ (snd b) bᴰ)

  private
    B-to-Set-≡
      : (B : Base Γ Δ) (w : Wk Ω Γ) {p : _} {p₁ : Params₁-Alg Δ _ p Ω-P}
        {pd : Params-DAlg Δ _ _ (Σ-Params Δ (Wk₁-Alg w ω₁) p₁)}
        {a : _}
      → (a₁ : Base₁-Alg B (Wk₀-Alg w ω₀) p a Ω-P)
      → (ad : Base-DAlg B (Wk-DAlg w γ) pd (Σ-Base B (Wk₁-Alg w ω₁) p₁ a₁))
      → B-to-Set B w (Base₀-Sect B a (fst sc)) a₁ ad ≡ Base-R-Alg B ad Init-R
    B-to-Set-≡ ty1 w a₁ ad = refl
    B-to-Set-≡ (ty2 x) w a₁ ad = refl
    {-# REWRITE B-to-Set-≡ #-}

    T-to-Set-≡
      : (B : Ty Γ Δ) (w : Wk Ω Γ) {p : _} {p₁ : Params₁-Alg Δ _ p Ω-P}
        {pd : Params-DAlg Δ _ _ (Σ-Params Δ (Wk₁-Alg w ω₁) p₁)} {a : _}
      → (a₁ : Ty₁-Alg B (Wk₀-Alg w ω₀) p a Ω-P)
      → (ad : Ty-DAlg B (Wk-DAlg w γ) pd (Σ-Ty B (Wk₁-Alg w ω₁) p₁ a₁))
      → T-to-Set B w (Ty₀-Sect B a (fst sc)) a₁ ad ≡ Ty-R-Alg B ad Init-R
    T-to-Set-≡ (ext x) w a₁ ad = refl
    T-to-Set-≡ (base x) w a₁ ad = refl
    T-to-Set-≡ (Π A B) w {a = a} a₁ ad = refl
    T-to-Set-≡ (B [ x ]) w a₁ ad = T-to-Set-≡ B w a₁ ad
    T-to-Set-≡ (B [ w' ]') w a₁ ad = T-to-Set-≡ B (w ∘w w') a₁ ad
    {-# REWRITE T-to-Set-≡ #-}

    P-to-Set-≡
      : (Δ : Params Γ) (w : Wk Ω Γ) {p₀ : _} {p₁ : _}
        (pᴰ : Params-DAlg Δ _ (Wk-DAlg w γ) (Σ-Params Δ (Wk₁-Alg w ω₁) {p₀} p₁))
      → P-to-Set Δ w pᴰ (Params₀-Sect Δ p₀ (fst sc)) ≡ Params-R-Alg Δ pᴰ Init-R
    P-to-Set-≡ ● w pᴰ = refl
    P-to-Set-≡ (Δ ‣‣ x) w pᴰ = cong (_× Ty-R-Alg x _ _) (P-to-Set-≡ Δ w (proj₁ pᴰ))
    P-to-Set-≡ (Δ [ x ]p) w pᴰ = P-to-Set-≡ Δ (w ∘w x) pᴰ
    {-# REWRITE P-to-Set-≡ #-}

  Init-R-alg : Spec-R-Alg Ω γ Init-R
  Init-R-alg {ctor Δ ty1} c {p} {pd} pr =
    transp (λ x → x) (sym' (cong' (λ f → f _ (CtorTm-DAlg c γ pd)) eq))
      (pd , pr , refl)
    where
      eq = snd sc c (Σ-Params-fst Δ ω₁ p)
  Init-R-alg {ctor Δ (ty2 x)} c = {!!}

  Init-R-param-inv : (c : CtorTm Ω (ctor Δ ty1)) (p : _) (aᴰ : _)
                   → proj₁ Init-R (CtorTm-Alg c σ-alg p) aᴰ
                   → Σ (Params-DAlg Δ σ-alg γ p) λ pd → Params-R-Alg Δ pd Init-R
  Init-R-param-inv {Δ = Δ} c p aᴰ x = proj₁ aux , proj₁ (proj₂ aux)
    where
      eq = snd sc c (Σ-Params-fst Δ ω₁ p)
      eq' = cong' (λ f → f _ aᴰ) eq
      aux = transp (λ x → x) eq' x

  Init-R-param-inv-≡
    : (c : CtorTm Ω (ctor Δ ty1)) (p : _)
      (pd : Params-DAlg Δ _ γ p) (pr : Params-R-Alg Δ pd Init-R)
    → Init-R-param-inv c p (CtorTm-DAlg c γ pd) (CtorTm-R-Alg c Init-R-alg pr)
    ≡ (pd , pr)
  Init-R-param-inv-≡ {Δ = Δ} c p pd pr = refl

  -- {-# REWRITE Init-R-param-inv-≡ #-}

  Init-R-ix-inv : (c : CtorTm Ω (ctor Δ ty1)) (p : _) (aᴰ : _)
                → (r : proj₁ Init-R (CtorTm-Alg c σ-alg p) aᴰ)
                → aᴰ ≡ CtorTm-DAlg c γ (proj₁ (Init-R-param-inv c p aᴰ r))
  Init-R-ix-inv {Δ = Δ} c p aᴰ r =
    proj₂ (proj₂ (transp (λ x → x) (cong' (λ f → f _ aᴰ) aux) r))
    where aux = snd sc c (Σ-Params-fst Δ ω₁ p)
