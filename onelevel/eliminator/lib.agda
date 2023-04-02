{-# OPTIONS --prop --rewriting --show-irrelevant #-}

module eliminator.lib where

open import IIT.spec
open import IIT.algebra
open import IIT.section
open import erased.algebra
open import erased.section
open import predicate.algebra
open import relation.algebra
open import sigma-construction
open import lib

open ≡-Reasoning

module ElimLib (S : Set × Set) (P : BasePreds S) (Y : _) (R : RelTys (Σ-Fam S P) Y) where

  elim-ds : DFam₀ S
  elim-ds =
      (λ c₀ → (c₁ : proj₁ P c₀) → Σ (proj₁ Y (_ ,p c₁)) (proj₁ R _))
    , λ t₀ → (c : _) (cᴰ : proj₁ Y c) (r : proj₁ R _ cᴰ) (t₁ : proj₂ P (fst c) t₀)
      → Σ (proj₂ Y c cᴰ (_ ,p t₁)) (proj₂ R c cᴰ (t₀ ,p t₁))

  exists-base
    : (A : Base Γ Δ)
      {γ₀ : Spec₀-Alg Γ S} (γ₁ : Spec₁-Alg Γ γ₀ P)
      {γd : Spec-DAlg Γ _ Y} (γr : Spec-R-Alg Γ γd R)
      {p₀ : Params₀-Alg Δ S} (p₁ : Params₁-Alg Δ γ₀ p₀ P)
      {pd : Params-DAlg Δ _ γd (Σ-Params Δ γ₁ p₁)} (pr : Params-R-Alg Δ pd R)
      {a₀ : _} (a₁ : Base₁-Alg A γ₀ p₀ a₀ P) (ad₀ : Base₀-DAlg A elim-ds a₀)
    → Σ (Base-DAlg A γd pd (Σ-Base A γ₁ p₁ a₁)) λ td → Base-R-Alg A td R
  exists-base ty1 _ _ _ _ a₁ ad₀ = ad₀ a₁
  exists-base (ty2 x) γ₁ {γd} r p₁ {pd} pr a₁ ad₀ =
    ad₀ (_ ,p Tm₁-Alg x γ₁ p₁) (Tm-DAlg x γd pd) (Tm-R-Alg x r pr) a₁

  exists-ty
    : ∀{Γ Δ} (A : Ty Γ Δ)
      {γ₀ : Spec₀-Alg Γ S} (γ₁ : Spec₁-Alg Γ γ₀ P)
      {γd : Spec-DAlg Γ _ Y} (γr : Spec-R-Alg Γ γd R)
      {p₀ : Params₀-Alg Δ S} (p₁ : Params₁-Alg Δ γ₀ p₀ P)
      {pd : Params-DAlg Δ _ γd (Σ-Params Δ γ₁ p₁)} (pr : Params-R-Alg Δ pd R)
      {a₀ : _} (a₁ : Ty₁-Alg A γ₀ p₀ a₀ P) (ad₀ : Ty₀-DAlg A elim-ds a₀)
    → Σ (Ty-DAlg A γd pd (Σ-Ty A γ₁ p₁ a₁)) λ td → Ty-R-Alg A td R
  exists-ty (ext A) γ₁ γr p₁ pr a₁ _ = _
  exists-ty (base x) = exists-base x
  exists-ty (Π A x) γ₁ r {p₀} p₁ pr a₁ ad₀ =
    (λ n → proj₁ (ih n)) , (λ n → proj₂ (ih n))
    where ih = λ n → exists-base x γ₁ r {p₀ , n} _ (pr , tt) (a₁ n) (ad₀ n)
  exists-ty (A [ x ]) γ₁ r p₁ pr a₁ ad₀ = exists-ty A γ₁ r _ (Sub-R-Alg x r pr) a₁ ad₀
  exists-ty (A [ w ]') γ₁ r p₁ pr a₁ ad₀ = exists-ty A (Wk₁-Alg w γ₁) (Wk-R-Alg w r) p₁ pr a₁ ad₀

  exists-params
    : ∀{Γ} Δ
      {γ₀ : Spec₀-Alg Γ S} (γ₁ : Spec₁-Alg Γ γ₀ P)
      {γd : Spec-DAlg Γ _ Y} (γr : Spec-R-Alg Γ γd R)
      {p₀ : Params₀-Alg Δ S} (p₁ : Params₁-Alg Δ γ₀ p₀ P)
      (pd₀ : Params₀-DAlg Δ elim-ds p₀)
    → Σ (Params-DAlg Δ _ γd (Σ-Params Δ γ₁ p₁)) λ pd → Params-R-Alg Δ pd R
  exists-params ● γ₁ r p₁ _ = _
  exists-params (Δ ‣‣ A) γ₁ r (p₁ ,P a₁) (pd₀ , ad₀) =
    (proj₁ ih , proj₁ aux) , proj₂ ih , proj₂ aux
    where
      ih = exists-params Δ γ₁ r p₁ pd₀
      aux = exists-ty A γ₁ r p₁ (proj₂ ih) a₁ ad₀
  exists-params (Δ [ x ]p) γ₁ r p₀ p₁ =
    exists-params Δ (Wk₁-Alg x γ₁) (Wk-R-Alg x r) p₀ p₁

  extract-params
    : ∀{Γ ∇ Δ σ} (pwk : PWk Δ ∇ σ)
      {γ₀ : Spec₀-Alg Γ S} (γ₁ : Spec₁-Alg Γ γ₀ P)
      {γd : Spec-DAlg Γ _ Y} (γr : Spec-R-Alg Γ γd R)
      {p₀ : _} (p₁ : Params₁-Alg Δ γ₀ p₀ P)
      (pd₀ : Params₀-DAlg Δ elim-ds p₀)
      (pd : Params-DAlg ∇ (Σ-Spec Γ γ₁) γd (Σ-Params ∇ γ₁ (Sub₁-Alg σ γ₁ p₁)))
      (pr : Params-R-Alg ∇ pd R)
    → Σ (Params-DAlg Δ _ γd (Σ-Params Δ γ₁ p₁)) λ pd → Params-R-Alg Δ pd R
  extract-params Id γ₁ γr p₁ _ pd pr = pd , pr
  extract-params (Drop {A = A} pwk) γ₁ γr (p₁ ,P a₁) (pd₀ , ad₀) pd pr =
    (proj₁ ih , proj₁ aux) , proj₂ ih , proj₂ aux
    where
      ih = extract-params pwk γ₁ γr p₁ pd₀ pd pr
      aux = exists-ty A γ₁ γr p₁ (proj₂ ih) a₁ ad₀

  extract-params-pwk-≡
    : ∀{Γ ∇ Δ σ} (pwk : PWk Δ ∇ σ)
      {γ₀ : Spec₀-Alg Γ S} (γ₁ : Spec₁-Alg Γ γ₀ P)
      {γd : Spec-DAlg Γ _ Y} (γr : Spec-R-Alg Γ γd R)
      {p₀ : Params₀-Alg Δ S} (p₁ : Params₁-Alg Δ γ₀ p₀ P)
      (pd₀ : Params₀-DAlg Δ elim-ds p₀)
      (pd : Params-DAlg ∇ (Σ-Spec Γ γ₁) γd (Σ-Params ∇ _ (Sub₁-Alg σ γ₁ p₁)))
      (pr : Params-R-Alg ∇ pd R)
    → Sub-DAlg σ (proj₁ (extract-params pwk γ₁ γr p₁ pd₀ pd pr)) ≡ pd
  extract-params-pwk-≡ Id _ _ p₁ pd₀ pd pr = refl
  extract-params-pwk-≡ (Drop pwk) γ₁ γr p₁ pd₀ pd pr =
    extract-params-pwk-≡ pwk γ₁ γr (fstP p₁) (proj₁ pd₀) pd pr
  {-# REWRITE extract-params-pwk-≡ #-}

  exists-params-Sub-lemma
    : ∀{Γ Δ ∇ σ} (pwk : PWk {Γ} Δ ∇ σ)
      {γ₀ : Spec₀-Alg Γ S} (γ₁ : Spec₁-Alg Γ γ₀ P)
      {γd : Spec-DAlg Γ _ Y} (γr : Spec-R-Alg Γ γd R)
      (γ₀d : Spec₀-DAlg Γ γ₀ elim-ds)
      {p₀ : Params₀-Alg Δ S} (p₁ : Params₁-Alg Δ γ₀ p₀ P)
      (pd₀ : Params₀-DAlg Δ elim-ds p₀)
    → let coll = exists-params Δ γ₁ γr p₁ pd₀
      in exists-params ∇ γ₁ γr (Sub₁-Alg σ γ₁ p₁) (Sub₀-DAlg σ γ₀d pd₀)
       ≡ (Sub-DAlg σ (proj₁ coll) , Sub-R-Alg σ γr (proj₂ coll))
  exists-params-Sub-lemma Id γ₁ γr γ₀d p₁ pd₀ = refl
  exists-params-Sub-lemma (Drop pwk) γ₁ γr γ₀d p₁ pd₀ =
    exists-params-Sub-lemma pwk γ₁ γr γ₀d (fstP p₁) (proj₁ pd₀)

  exists-params-cumul-lemma
    : ∀{Δ ∇ σ} (pwk : PWk Δ ∇ σ)
      {γ₀ : Spec₀-Alg Γ S} (γ₁ : Spec₁-Alg Γ γ₀ P)
      {γd : Spec-DAlg Γ _ Y} (γr : Spec-R-Alg Γ γd R)
      (γ₀d : Spec₀-DAlg Γ γ₀ elim-ds)
      {p₀ : Params₀-Alg Δ S} (p₁ : Params₁-Alg Δ γ₀ p₀ P)
      (pd₀ : _)
    → let coll' = exists-params {Γ} ∇ γ₁ γr (Sub₁-Alg σ γ₁ p₁) (Sub₀-DAlg σ γ₀d pd₀)
    in extract-params pwk γ₁ γr p₁ pd₀ (proj₁ coll') (proj₂ coll')
    ≡ exists-params Δ γ₁ γr p₁ pd₀
  exists-params-cumul-lemma Id γ₁ γr γ₀d p₁ pd₀ = refl
  exists-params-cumul-lemma (Drop pwk) γ₁ γr γ₀d (p₁ ,P a₁) (pd₀ , ad₀)
    rewrite exists-params-cumul-lemma pwk γ₁ γr γ₀d p₁ pd₀ = refl

  module exists-lemmas
    (Ω : Spec) (m : Morph₀ S elim-ds)
    (ω₀ : Spec₀-Alg Ω S) (ω₁ : Spec₁-Alg Ω ω₀ P)
    (ωd : Spec-DAlg Ω (Σ-Spec Ω ω₁) Y) (ωr : Spec-R-Alg Ω ωd R)
    (h1 : ∀{Γ Δ} (w : Wk Ω Γ) (t : CtorTm Γ (ctor Δ ty1)) {p₀ : _} (p₁ : Params₁-Alg Δ (Wk₀-Alg w ω₀) p₀ P)
        → let coll = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m)
          in proj₁ m _ (CtorTm₁-Alg t (Wk₁-Alg w ω₁) p₁) ≡ (_ , CtorTm-R-Alg t (Wk-R-Alg w ωr) (proj₂ coll)))
    (h2 : ∀{Γ Δ t} (w : Wk Ω Γ) (c : CtorTm Γ (ctor Δ (ty2 t))) {p₀ : _} (p₁ : Params₁-Alg Δ (Wk₀-Alg w ω₀) p₀ P)
        → let coll = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m)
          in proj₂ m _ _ _ (Tm-R-Alg t (Wk-R-Alg w ωr) (proj₂ coll)) (CtorTm₁-Alg c (Wk₁-Alg w ω₁) p₁)
           ≡ (_ , CtorTm-R-Alg c (Wk-R-Alg w ωr) (proj₂ coll)))
    where

    exists-Base-commute
      : ∀{Γ Δ} (A : Base Γ Δ) (w : Wk Ω Γ)
        (γ₀d : Spec₀-DAlg Γ (Wk₀-Alg w ω₀) elim-ds)
        {p₀ : Params₀-Alg Δ S} (p₁ : Params₁-Alg Δ (Wk₀-Alg w ω₀) p₀ P)
        (cs : Spec₀-Sect Γ _ γ₀d m)
        (c : CtorTm Γ (ctor Δ A))
      → let coll' = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m)
        in exists-base A (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (proj₂ coll') (CtorTm₁-Alg c (Wk₁-Alg w ω₁) p₁) (CtorTm₀-DAlg c γ₀d (Params₀-Sect Δ p₀ m))
           ≡ (CtorTm-DAlg c (Wk-DAlg w ωd) (proj₁ coll') , CtorTm-R-Alg c (Wk-R-Alg w ωr) (proj₂ coll'))
    exists-Base-commute ty1 w γ₀d {p₀} p₁ cs c =
      trans (cong (λ f → f (CtorTm₁-Alg c (Wk₁-Alg w ω₁) p₁)) eq) (h1 w c p₁)
      where eq = to-≡ (sym' (cs c p₀))
    exists-Base-commute {Δ = Δ} (ty2 x) w γ₀d {p₀} p₁ cs c =
      trans (cong (λ f → f _ _ (Tm-R-Alg x (Wk-R-Alg w ωr) (proj₂ coll)) (CtorTm₁-Alg (c [ w ]ctm) ω₁ p₁)) eq)
            (h2 w c p₁)
      where
        eq = to-≡ (sym' (cs c p₀))
        coll = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m)

    exists-Params-commute
      : ∀{Γ Δ ∇} (σ : Sub Δ ∇) (w : Wk Ω Γ)
        (γ₀d : Spec₀-DAlg Γ (Wk₀-Alg w ω₀) elim-ds)
        {p₀ : Params₀-Alg Δ S} (p₁ : Params₁-Alg Δ (Wk₀-Alg w ω₀) p₀ P)
        (cs : Spec₀-Sect Γ _ γ₀d m)
      → let coll = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m)
        in exists-params ∇ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) (Sub₁-Alg σ (Wk₁-Alg w ω₁) p₁) (Sub₀-DAlg σ γ₀d (Params₀-Sect Δ p₀ m))
         ≡ (Sub-DAlg σ (proj₁ coll) , Sub-R-Alg σ (Wk-R-Alg w ωr) (proj₂ coll))

    exists-Ty-commute
      : ∀{Δ} {A : Ty Γ Δ} (w : Wk Ω Γ)
        (γ₀d : Spec₀-DAlg Γ (Wk₀-Alg w ω₀) elim-ds)
        {p₀ : Params₀-Alg Δ S} (p₁ : Params₁-Alg Δ (Wk₀-Alg w ω₀) p₀ P)
        (cs : Spec₀-Sect Γ _ γ₀d m)
        (t : Tm Γ Δ A)
      → let coll' = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m)
        in exists-ty A (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (proj₂ coll') (Tm₁-Alg t (Wk₁-Alg w ω₁) p₁) (Tm₀-DAlg t γ₀d (Params₀-Sect Δ p₀ m))
         ≡ (Tm-DAlg t (Wk-DAlg w ωd) (proj₁ coll') , Tm-R-Alg t (Wk-R-Alg w ωr) (proj₂ coll'))

    exists-Params-commute Id w γ₀d p₁ cs = refl
    exists-Params-commute (Ext σ t) w γ₀d p₁ cs rewrite exists-Params-commute σ w γ₀d p₁ cs
      = cong (λ z → ((_ , proj₁ z) , (_ , proj₂ z))) ih'
      where ih' = exists-Ty-commute w γ₀d p₁ cs t
    exists-Params-commute Drop w γ₀d p₁ cs = refl
    exists-Params-commute {∇ = ∇} (_∘_ {_} {Δ} {Δ'} σ τ) w γ₀d {p₀} p₁ cs = goal
      where
        aux = exists-Params-commute τ w γ₀d (Sub₁-Alg σ (Wk₁-Alg w ω₁) p₁) cs
        coll = (exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁
                (Params₀-Sect Δ p₀ m))
        coll' = (exists-params Δ' (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr)
                  (Sub₁-Alg σ (Wk₁-Alg w ω₁) p₁)
                  (Params₀-Sect Δ' (Sub₀-Alg σ (Wk₀-Alg w ω₀) p₀) m))
        eq : coll' ≡ ((Sub-DAlg σ (proj₁ coll)) , (Sub-R-Alg σ (Wk-R-Alg w ωr) (proj₂ coll)))
        eq = begin
          _ ≡⟨ cong (exists-params Δ' _ _ _) (to-≡ (Sub₀-Sect σ cs p₀)) ⟩
          _ ≡⟨ exists-Params-commute σ w γ₀d p₁ cs ⟩
          _ ∎
        goal = begin
             _ ≡⟨ cong (λ z → exists-params ∇ _ _ _ (Sub₀-DAlg τ γ₀d z))
                  (sym (to-≡ (Sub₀-Sect σ cs p₀))) ⟩
             _ ≡⟨ aux ⟩
             _ ≡⟨ cong (λ z → (Sub-DAlg τ (proj₁ z) , Sub-R-Alg τ _ (proj₂ z))) eq ⟩
             _ ∎
     
    exists-Params-commute (σ [ w' ]ws) w γ₀d p₁ cs =
      exists-Params-commute σ (w ∘w w') (Wk₀-DAlg w' γ₀d) p₁ (Wk₀-Sect w' cs)

    open ≅-Reasoning

    exists-Ty-commute w γ₀d p₁ cs vz = refl
    exists-Ty-commute w γ₀d p₁ cs vz1 = refl
    exists-Ty-commute w γ₀d p₁ cs (vs t) = exists-Ty-commute w γ₀d (fstP p₁) cs t
    exists-Ty-commute w γ₀d p₁ cs (ext A x) = refl
    exists-Ty-commute {Δ = Δ} w γ₀d {p₀} p₁ cs (ctor {Δ = Δ'} {A = A} x σ) = admit≡
    -- although we do have a proof below, it takes quite a bit to typecheck,
    -- so we leave it available commented
{-
      homo-≅ goal
      where
        w1 = Wk₁-Alg w ω₁
        wr = Wk-R-Alg w ωr
        coll = exists-params Δ w1 wr p₁ (Params₀-Sect Δ p₀ m)
        coll' = exists-params Δ' w1 wr (Sub₁-Alg σ w1 p₁)
                  (Params₀-Sect Δ' (Sub₀-Alg σ (Wk₀-Alg w ω₀) p₀) m)
        eq = exists-Params-commute σ w γ₀d p₁ cs
        eq' : coll' ≡ (Sub-DAlg σ (proj₁ coll) , Sub-R-Alg σ wr (proj₂ coll))
        eq' = trans (cong (exists-params Δ' _ _ _) (to-≡ (Sub₀-Sect σ cs p₀))) eq
        c1 = CtorTm₁-Alg x w1 (Sub₁-Alg σ w1 p₁)
        goal : exists-base A w1 wr _
                (Sub-R-Alg σ wr (proj₂ coll))
                c1
                (CtorTm₀-DAlg x γ₀d (Sub₀-DAlg σ γ₀d (Params₀-Sect Δ p₀ m)))
                ≅
                ( CtorTm-DAlg x (Wk-DAlg w ωd) (Sub-DAlg σ (proj₁ coll))
                , CtorTm-R-Alg x wr (Sub-R-Alg σ wr (proj₂ coll)))
        goal = begin≅
               exists-base A w1 wr _
                (Sub-R-Alg σ wr (proj₂ coll))
                c1
                (CtorTm₀-DAlg x γ₀d (Sub₀-DAlg σ γ₀d (Params₀-Sect Δ p₀ m)))
                 ≅⟨ cong-≅ (λ z → exists-base A w1 wr _ {proj₁ z} (proj₂ z) c1 _) (sym eq') ⟩
               exists-base A w1 wr _
                (proj₂ coll')
                (CtorTm₁-Alg x w1 (Sub₁-Alg σ w1 p₁))
                (CtorTm₀-DAlg x γ₀d (Sub₀-DAlg σ γ₀d (Params₀-Sect Δ p₀ m)))
                 ≅⟨ ≡-to-≅ (cong (exists-base A w1 wr _ _ _) (cong (CtorTm₀-DAlg x γ₀d)
                      (to-≡ (sym' (Sub₀-Sect σ cs p₀))))) ⟩
               exists-base A w1 wr _
                (proj₂ coll')
                (CtorTm₁-Alg x w1 (Sub₁-Alg σ w1 p₁))
                (CtorTm₀-DAlg x γ₀d _)
                 ≅⟨ ≡-to-≅ (exists-Base-commute A w γ₀d (Sub₁-Alg σ (Wk₁-Alg w ω₁) p₁) cs x) ⟩
                ( CtorTm-DAlg x (Wk-DAlg w ωd) (proj₁ coll')
                , CtorTm-R-Alg x (Wk-R-Alg w ωr) (proj₂ coll'))
                 ≅⟨ cong-≅ (λ z → CtorTm-DAlg x _ (proj₁ z) , CtorTm-R-Alg x _ (proj₂ z)) eq' ⟩
               _
                 ∎≅
-}
    exists-Ty-commute w γ₀d {p₀ , n} p₁ cs (app {Δ = Δ} {B = B} t) =
      cong (λ fg → (proj₁ fg n , proj₂ fg n)) ih
      where
        ih = exists-Ty-commute w γ₀d (fstP p₁) cs t
    exists-Ty-commute w γ₀d {p₀} p₁ cs (lam {Δ = Δ} {B = B} t) =
      helper (λ n → exists-Ty-commute w γ₀d (p₁ ,P ttp) cs t)

    exists-Ty-commute w γ₀d {p₀} p₁ cs (_[_]tm {∇ = Δ} {Δ'} {A = A} t σ) = admit≡
    -- although we do have a proof below, it takes quite a bit to typecheck,
    -- so we leave it available commented
    {-
      homo-≅ goal≅
      where
        w1 = (Wk₁-Alg w ω₁)
        wr = (Wk-R-Alg w ωr)
        tm = (Tm₁-Alg t w1 (Sub₁-Alg σ w1 p₁))
        coll' = (exists-params Δ' w1 wr (Sub₁-Alg σ w1 p₁)
                  (Params₀-Sect Δ' (Sub₀-Alg σ (Wk₀-Alg w ω₀) p₀) m))
        ih : exists-ty A w1 wr _ (proj₂ coll') tm
               (Tm₀-DAlg t γ₀d (Params₀-Sect Δ' (Sub₀-Alg σ (Wk₀-Alg w ω₀) p₀) m))
           ≡ ( Tm-DAlg t (Wk-DAlg w ωd) (proj₁ coll')
             , Tm-R-Alg t wr (proj₂ coll'))
        ih = exists-Ty-commute w γ₀d (Sub₁-Alg σ w1 p₁) cs t
        coll = (exists-params Δ w1 wr p₁ (Params₀-Sect Δ p₀ m))
        eq : coll' ≡ (_ , Sub-R-Alg σ wr (proj₂ coll))
        eq = trans (cong (exists-params Δ' _ _ _) (to-≡ (Sub₀-Sect σ cs p₀)))
                   (exists-Params-commute σ w γ₀d p₁ cs)
        goal≅ : exists-ty A w1 wr _ (Sub-R-Alg σ wr (proj₂ coll)) tm
                 (Tm₀-DAlg t γ₀d (Sub₀-DAlg σ γ₀d (Params₀-Sect Δ p₀ m)))
             ≅ ( Tm-DAlg t (Wk-DAlg w ωd) (Sub-DAlg σ (proj₁ coll))
               , Tm-R-Alg t wr (Sub-R-Alg σ wr (proj₂ coll)))
        goal≅ = begin≅
             _
               ≅⟨ cong-≅ (λ z → exists-ty A w1 wr _ {proj₁ z} (proj₂ z) tm _) (sym eq) ⟩
             exists-ty A w1 wr _ (proj₂ coll') tm
                 (Tm₀-DAlg t γ₀d (Sub₀-DAlg σ γ₀d (Params₀-Sect Δ p₀ m)))
               ≅⟨ ≡-to-≅ (cong (exists-ty A w1 wr _ (proj₂ coll') tm)
                   (cong (Tm₀-DAlg t γ₀d) (to-≡ (sym' (Sub₀-Sect σ cs p₀))))) ⟩
             exists-ty A w1 wr _ (proj₂ coll') tm _
               ≅⟨ ≡-to-≅ ih ⟩
             ( Tm-DAlg t (Wk-DAlg w ωd) (proj₁ coll')
             , Tm-R-Alg t wr (proj₂ coll'))
               ≅⟨ cong-≅ (λ z → Tm-DAlg t _ (proj₁ z) , Tm-R-Alg t wr (proj₂ z)) eq ⟩
             ( Tm-DAlg t (Wk-DAlg w ωd) (Sub-DAlg σ (proj₁ coll))
             , Tm-R-Alg t wr (Sub-R-Alg σ wr (proj₂ coll)))
               ∎≅
      -}
    exists-Ty-commute w γ₀d p₁ cs (t [ w' ]tm') = admit≡ -- same as the non-specialized case
    exists-Ty-commute w γ₀d p₁ cs (t [ w₁ ]tm'-1) = admit≡ -- same as the non-specialized case
    exists-Ty-commute w γ₀d p₁ cs (ctor-1 x σ) = admit≡ -- same as the non-specialized case
    exists-Ty-commute w γ₀d p₁ cs (app-U t x) = refl

