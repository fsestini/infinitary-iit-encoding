{-# OPTIONS --prop --rewriting --show-irrelevant #-}

module eliminator.eliminator-het where

open import IIT.spec
open import IIT.algebra
open import IIT.section
open import erased.algebra
open import erased.section
open import predicate.algebra
open import predicate.inversions
open import relation.algebra
open import relation.inversions
open import sigma-construction
open import lib

open import eliminator.lib

{-# REWRITE [∘]p-≡ [∘]b'-≡ #-}

open ≡-Reasoning

module _
  (Ω : Spec)
  (lin : LinearSpec Ω)

  (F₀ : Fam₀)
  (ω₀ : Spec₀-Alg Ω F₀)
  (init₀ : is-initial₀ ω₀)

  (P : BasePreds F₀)
  (ω₁ : Spec₁-Alg Ω ω₀ P)
  (pinv : HasPredicateInversions Ω P ω₀)
  
  (Y : DFam (Σ-Fam _ P))
  (ωd : Spec-DAlg Ω (Σ-Spec Ω ω₁) Y)

  (R : RelTys _ Y)
  where

  open HasPredicateInversions pinv

  S = F₀

  C₁ = proj₁ P
  T₁ = proj₂ P
  A₁ = proj₁ P
  B₁ = proj₂ P

  R-C = proj₁ R
  R-T = proj₂ R

  σ-alg = Σ-Spec Ω ω₁

  -- Assume a relation algebra with inversions
  --
  -- For some reason, putting these as module parameters instead of postulates
  -- crashes Agda, so here we are.
  postulate
    ωr : Spec-R-Alg Ω ωd R
    Init-R-param-inv : (c : CtorTm Ω (ctor Δ ty1)) (p : _) (aᴰ : _)
                   → proj₁ R (CtorTm-Alg c σ-alg p) aᴰ
                   → Σ (Params-DAlg Δ σ-alg ωd p) λ pd → Params-R-Alg Δ pd R

    Init-R-param-inv-≡
      : (c : CtorTm Ω (ctor Δ ty1)) (p : _)
        (pd : Params-DAlg Δ _ ωd p) (pr : Params-R-Alg Δ pd R)
      → Init-R-param-inv c p (CtorTm-DAlg c ωd pd) (CtorTm-R-Alg c ωr pr)
      ≡ (pd , pr)
  
    Init-R-ix-inv : (c : CtorTm Ω (ctor Δ ty1)) (p : _) (aᴰ : _)
                  → (r : proj₁ R (CtorTm-Alg c σ-alg p) aᴰ)
                  → aᴰ ≡ CtorTm-DAlg c ωd (proj₁ (Init-R-param-inv c p aᴰ r))
    {-# REWRITE Init-R-param-inv-≡ #-}

  open ElimLib S P Y R

  exists-B-lin
    : ∀{Δ ∇ σ} (pwk : PWk {Ω} Δ ∇ σ)
      (c' : CtorTm Ω (ctor ∇ ty1))
      (c : CtorTm Ω (ctor Δ (ty2 (ctor-1 c' σ))))
    → Ctor₀-DAlg (ctor Δ (ty2 (ctor-1 c' σ))) elim-ds (CtorTm₀-Alg c ω₀)
  exists-B-lin {Δ} {σ = σ} pwk c' c {p₀} p₀ᴰ a aᴰ r-a b₁ =
    transp T (sym' e) h _ aᴰ r-a b₁
    where
      e : fst a ≡p CtorTm₀-Alg c' ω₀ (Sub₀-Alg σ ω₀ p₀)
      e = pred-ix-inv c p₀ _ b₁
      T : proj₁ F₀ → Set
      T a₀ = (a₁ : _) (aᴰ : proj₁ Y (a₀ ,p a₁)) (r : proj₁ R _ aᴰ) (b₁ : proj₂ P a₀ _)
           → Σ (proj₂ Y _ aᴰ (_ ,p b₁)) (proj₂ R _ aᴰ (_ ,p b₁))
      h : T (CtorTm₀-Alg c' ω₀ (Sub₀-Alg σ ω₀ p₀))
      h a₁ aᴰ r-a b₁ = transp T' (from-≡ (sym e')) aux
        where
          p₁ = pred-inv c p₀ b₁
          pm = Init-R-param-inv c' (Sub-Alg σ (Σ-Params Δ ω₁ p₁)) aᴰ r-a
          coll = extract-params pwk ω₁ ωr p₁ p₀ᴰ _ (proj₂ pm)
          e' = Init-R-ix-inv c' (Sub-Alg σ (Σ-Params Δ ω₁ p₁)) aᴰ r-a
          T' = λ aᴰ → Σ (proj₂ Y _ aᴰ (_ ,p b₁)) (proj₂ R _ aᴰ (_ ,p b₁))
          aux = _ , CtorTm-R-Alg c ωr (proj₂ coll)

  exists-B-lin-lemma
    : ∀{Δ ∇ σ} (pwk : PWk {Ω} Δ ∇ σ)
      (c' : CtorTm Ω (ctor ∇ ty1))
      (c : CtorTm Ω (ctor Δ (ty2 (ctor-1 c' σ))))
      {p₀ : _} (p₁ : Params₁-Alg Δ ω₀ p₀ P) (p₀ᴰ : _) (ω₀ᴰ : Spec₀-DAlg Ω ω₀ elim-ds)
     → let coll = exists-params Δ ω₁ ωr p₁ p₀ᴰ
       in
          exists-B-lin pwk c' c p₀ᴰ _ _
            (CtorTm-R-Alg c' ωr (Sub-R-Alg σ ωr (proj₂ coll)))
            (CtorTm₁-Alg c ω₁ p₁)
        ≡ (_ , CtorTm-R-Alg c ωr (proj₂ coll))
  exists-B-lin-lemma {Δ = Δ} {∇ = ∇} {σ = σ} pwk c' c {p₀} p₁ p₀ᴰ ω₀ᴰ =
    homo-≅ asd
    where
      coll' = exists-params Δ ω₁ ωr p₁ p₀ᴰ
      coll = extract-params pwk ω₁ ωr p₁ p₀ᴰ _ (Sub-R-Alg σ ωr (proj₂ coll'))
      coll-≡ : coll ≡ coll'
      coll-≡ = trans
        (cong (λ z → extract-params pwk ω₁ ωr p₁ p₀ᴰ (proj₁ z) (proj₂ z))
              (sym (exists-params-Sub-lemma pwk ω₁ ωr ω₀ᴰ p₁ p₀ᴰ)))
        (exists-params-cumul-lemma pwk ω₁ ωr ω₀ᴰ p₁ p₀ᴰ)
      asd = cong-≅ {B = λ z → Σ _ (proj₂ R _ _ _)}
                   (λ z → CtorTm-DAlg c ωd (proj₁ z) , CtorTm-R-Alg c ωr (proj₂ z))
                   {coll} {coll'} coll-≡

  exists-B-var
    : (c : CtorTm Ω (ctor (Δ ‣‣ _) (ty2 vz1)))
    → Ctor₀-DAlg (ctor (Δ ‣‣ _) (ty2 vz1)) elim-ds (CtorTm₀-Alg c ω₀)
  exists-B-var {Δ = Δ} c {p₀ , a₀} p₀ᴰ a aᴰ r-a b₁ =
    transp T (Σp-≡p (sym' e)) have aᴰ r-a b₁
    where
      e : fst a ≡p a₀
      e = pred-ix-inv c _ _ b₁
      a₁' = transp-P A₁ e (snd a)
      p₁ = pred-inv c _ (transp-P (λ z → B₁ z _) e b₁)
      coll = exists-params Δ ω₁ ωr (fstP p₁) (proj₁ p₀ᴰ)
      T : _ → Set
      T a = (aᴰ : proj₁ Y a) (r-a : proj₁ R a aᴰ) (b₁ : _)
          → Σ (proj₂ Y a aᴰ (CtorTm₀-Alg c ω₀ (p₀ , a₀) ,p b₁))
              (proj₂ R a aᴰ (CtorTm₀-Alg c ω₀ (p₀ , a₀) ,p b₁))
      have : T (a₀ ,p a₁')
      have aᴰ ra _ = _ , CtorTm-R-Alg c ωr (proj₂ coll , ra)

  ds-alg-ty2 : ∀{Δ x} → LinearCtor (ctor Δ (ty2 x))
             → (c : CtorTm Ω (ctor Δ (ty2 x))) {p : Params₀-Alg Δ F₀}
             → Params₀-DAlg Δ elim-ds p
             → Base₀-DAlg (ty2 x) elim-ds (CtorTm₀-Alg c ω₀ p)
  ds-alg-ty2 (l-ctor2 c' pwk) c = exists-B-lin pwk c' c
  ds-alg-ty2 l-ctor2-var c = exists-B-var c

  ds-alg : Spec₀-DAlg Ω ω₀ elim-ds
  ds-alg {ctor Δ ty1} c {p₀} p c₁ =
    CtorTm-DAlg c ωd (proj₁ coll) , CtorTm-R-Alg c ωr (proj₂ coll)
    where coll = exists-params Δ ω₁ ωr (pred-inv c p₀ c₁) p
  ds-alg {ctor Δ (ty2 _)} c = ds-alg-ty2 (lctr lin c) c

  init0 = init₀ ds-alg
  m0 = fst init0

  h1 : ∀{Γ Δ} (w : Wk Ω Γ) (t : CtorTm Γ (ctor Δ ty1))
       {p₀ : _} (p₁ : Params₁-Alg Δ (Wk₀-Alg w ω₀) p₀ P)
     → let coll = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m0)
       in proj₁ m0 _ (CtorTm₁-Alg t (Wk₁-Alg w ω₁) p₁) ≡ (_ , CtorTm-R-Alg t (Wk-R-Alg w ωr) (proj₂ coll))
  h1 w c {p₀} p₁ =
    cong (λ f → f (CtorTm₁-Alg c (Wk₁-Alg w ω₁) p₁)) (to-≡ (snd init0 (c [ w ]ctm) p₀))

  h2'' : ∀{Δ t}(c : CtorTm Ω (ctor Δ (ty2 t))) {p₀ : _} (p₁ : Params₁-Alg Δ ω₀ p₀ P) (l : LinearCtor (ctor Δ (ty2 t)))
       → let coll = exists-params Δ ω₁ ωr p₁ (Params₀-Sect Δ p₀ m0)
         in ds-alg-ty2 l c (Params₀-Sect Δ p₀ m0) _ _ (Tm-R-Alg t ωr (proj₂ coll)) (CtorTm₁-Alg c ω₁ p₁)
           ≡ (_ , CtorTm-R-Alg c ωr (proj₂ coll))
  h2'' {Δ} c {p₀} p₁ (l-ctor2 {σ = σ} c' pwk) = exists-B-lin-lemma pwk c' c p₁ (Params₀-Sect Δ p₀ m0) ds-alg
  h2'' c {p₀} p₁ l-ctor2-var = refl

  h2' : ∀{t}(c : CtorTm Ω (ctor Δ (ty2 t))) {p₀ : _} (p₁ : Params₁-Alg Δ ω₀ p₀ P)
     → let coll = exists-params Δ ω₁ ωr p₁ (Params₀-Sect Δ p₀ m0)
       in proj₂ m0 _ _ _ (Tm-R-Alg t ωr (proj₂ coll)) (CtorTm₁-Alg c ω₁ p₁)
        ≡ (_ , CtorTm-R-Alg c ωr (proj₂ coll))
  h2' c {p₀} p₁ =
    trans (cong (λ f → f _ _ _ (CtorTm₁-Alg c ω₁ p₁)) (to-≡ (snd init0 c p₀)))
          (h2'' c p₁ (lctr lin c))

  h2 : ∀{Γ Δ t} (w : Wk Ω Γ) (c : CtorTm Γ (ctor Δ (ty2 t))) {p₀ : _} (p₁ : Params₁-Alg Δ (Wk₀-Alg w ω₀) p₀ P)
     → let coll = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m0)
       in proj₂ m0 _ _ _ (Tm-R-Alg t (Wk-R-Alg w ωr) (proj₂ coll)) (CtorTm₁-Alg c (Wk₁-Alg w ω₁) p₁)
        ≡ (_ , CtorTm-R-Alg c (Wk-R-Alg w ωr) (proj₂ coll))
  h2 w c p₁ = h2' (c [ w ]ctm) p₁
      
  open exists-lemmas Ω m0 ω₀ ω₁ ωd ωr h1 h2

  exists-1 : (c₀ : proj₁ F₀) (c₁ : _) → Σ (proj₁ Y (_ ,p c₁)) (proj₁ R _)
  exists-1 = proj₁ m0

  exists-2 : (c : _) (cᴰ : proj₁ Y c) (r : R-C _ cᴰ)
             (t₀ : proj₂ F₀) (t₁ : _)
           → Σ (proj₂ Y c cᴰ (_ ,p t₁)) (R-T c cᴰ (t₀ ,p t₁))
  exists-2 c cᴰ r t₀ t₁ = proj₂ m0 _ c cᴰ r t₁

  morph : Morphᴰ _ Y
  morph = (λ c → proj₁ (exists-1 (fst c) (snd c)))
        , (λ t → proj₁ (exists-2 _ _ (proj₂ (exists-1 _ _)) _ (snd t)))

  exists-1-≡
    : ∀{Γ Δ} (w : Wk Ω Γ) (t : Tm Γ Δ (base ty1))
    → (p₀ : _) (p₁ : _)
    → let coll = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m0)
      in exists-1 _ (Tm₁-Alg t (Wk₁-Alg w ω₁) p₁) ≡ (_ , Tm-R-Alg t (Wk-R-Alg w ωr) (proj₂ coll))
  exists-1-≡ w t p₀ p₁ =
    trans (to-≡ (cong' (λ f → f _) (Tm₀-Sect t s₀ p₀))) (exists-Ty-commute w _ p₁ s₀ t)
    where
      s₀ = Wk₀-Sect w (snd init0)
  
  exists-params-≡
    : ∀{Γ} (w : Wk Ω Γ) Δ
      {p₀ : _} (p₁ : Params₁-Alg Δ _ p₀ P) (cs : _)
    → proj₁ (exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m0))
    ≡ Params-Sect Δ (Σ-Params Δ (Wk₁-Alg w ω₁) p₁) morph cs

  exists-base-≡
    : ∀{Γ Δ} (w : Wk Ω Γ) (A : Base Γ Δ)
      {p₀ : _} (p₁ : Params₁-Alg Δ _ p₀ P) (cs : Spec-Sect Γ _ (Wk-DAlg w ωd) morph)
      {a₀ : _} (a₁ : _)
    → let coll = exists-params Δ _ (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m0)
      in proj₁ (exists-base A (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (proj₂ coll) a₁ (Base₀-Sect A a₀ m0))
       ≅ Base-Sect A (Σ-Base A (Wk₁-Alg w ω₁) p₁ a₁) morph cs

  exists-ty-≡
    : ∀{Γ Δ} (w : Wk Ω Γ) (A : Ty Γ Δ)
      {p₀ : _} (p₁ : Params₁-Alg Δ _ p₀ P) (cs : _)
      {a₀ : _} (a₁ : _)
    → let coll = exists-params Δ _ (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m0)
      in proj₁ (exists-ty A _ (Wk-R-Alg w ωr) p₁ (proj₂ coll) a₁ (Ty₀-Sect A a₀ m0))
       ≅ Ty-Sect A (Σ-Ty A (Wk₁-Alg w ω₁) p₁ a₁) morph cs

  exists-params-≡ w ● p₁ cs = refl
  exists-params-≡ w (Δ ‣‣ x) (p₁ ,P a₁) cs =
    Σ-≡ (exists-params-≡ w Δ p₁ cs) (≅-to-subst T _ (exists-ty-≡ w x p₁ cs a₁))
    where T = λ z → Ty-DAlg x (Wk-DAlg w ωd) z (Σ-Ty x (Wk₁-Alg w ω₁) p₁ a₁)
  exists-params-≡ w (Δ [ x ]p) p₁ cs =
    exists-params-≡ (w ∘w x) Δ p₁ (Wk-Sect x _ cs)

  exists-base-≡ {Δ = Δ} w ty1 p₁ cs {a₀} a₁ = refl≅
  exists-base-≡ {Δ = Δ} w (ty2 x) {p₀} p₁ cs {a₀} a₁ = transp-absorb-≅' T (from-≡ q) goal'
    where
      T = λ z → proj₂ Y _ z _
      q = Tm-Sect x morph cs
      eq = exists-1-≡ w x p₀ p₁
      goal' = cong-≅ (λ z → proj₁ (exists-2 _ (proj₁ z) (proj₂ z) a₀ a₁)) (sym eq)

  exists-ty-≡ w (ext _) p₁ cs a₁ = refl≅
  exists-ty-≡ w (base x) = exists-base-≡ w x
  exists-ty-≡ {Δ = Δ} w ab@(Π A B) {p₀} p₁ cs {a₀} a₁ =
    subst-to-≅ T pf (trans (fun-subst {_} {El A} _ pf f)
      (funext (λ x → let aux = exists-base-≡ w B (p₁ ,P ttp) cs (a₁ x)
                     in ≅-to-subst (λ z → TT z x) pf aux)))
    where
      w1 = Wk₁-Alg w ω₁
      wd = Wk-DAlg w ωd
      wr = Wk-R-Alg w ωr
      TT = λ x n → Base-DAlg B wd (x , tt) (Σ-Base B w1 (p₁ ,P ttp) (a₁ n))
      T = λ x → (n : _) → TT x n
      pf = exists-params-≡ w Δ p₁ cs
      f = (proj₁ (exists-ty (Π A B) w1 wr p₁
        (proj₂ (exists-params Δ w1 wr p₁
        (Params₀-Sect Δ p₀ m0))) a₁ (λ n → Base₀-Sect B (a₀ n) m0)))

  exists-ty-≡ {Δ = Δ} w (_[_] {Δ = ∇} A σ) {p₀} p₁ cs {a₀} a₁ =
    transp-absorb-≅' goalT2 (from-≡ goalP2)
      (trans-≅ (cong-≅ f eq) (exists-ty-≡ w A (Sub₁-Alg σ w1 p₁) cs a₁))
    where
      wr = Wk-R-Alg w ωr
      w1 = Wk₁-Alg w ω₁
      wd = Wk-DAlg w ωd
      goalT2 = (λ z → Ty-DAlg A wd z (Σ-Ty A w1 (Sub₁-Alg σ w1 p₁) a₁))
      goalP2 = Sub-Sect σ (Σ-Params Δ w1 p₁) morph cs
      ex-∇ = exists-params ∇ w1 wr (Sub₁-Alg σ w1 p₁) (Params₀-Sect ∇ (Sub₀-Alg σ (Wk₀-Alg w ω₀) p₀) m0)
      ex-Δ = exists-params Δ w1 wr p₁ (Params₀-Sect Δ p₀ m0)
      s0 = Wk₀-Sect w (snd init0)
      eq = sym (trans (cong (exists-params ∇ w1 wr (Sub₁-Alg σ w1 p₁)) (to-≡ (Sub₀-Sect σ s0 p₀)))
               (exists-Params-commute σ w (Wk₀-DAlg w ds-alg) p₁ s0))
      f = λ z → proj₁ (exists-ty A w1 wr (Sub₁-Alg σ w1 p₁) (proj₂ z) a₁ (Ty₀-Sect A a₀ m0))
  exists-ty-≡ w (A [ w' ]') p₁ cs a₁ = exists-ty-≡ (w ∘w w') A p₁ (Wk-Sect w' morph cs) a₁

  section-ctor' : ∀{Γ Δ} (w : Wk Ω Γ) (A : Base Γ Δ)
                  (c : CtorTm Ω (ctor (Δ [ w ]p) (A [ w ]b')))
                  {cs : _} {p : _} (p₁ : Params₁-Alg Δ _ p _)
                → let p = Σ-Params Δ (Wk₁-Alg w ω₁) p₁
                  in Base-Sect A (CtorTm-Alg c σ-alg p) morph cs
                ≡p CtorTm-DAlg c ωd (Params-Sect Δ p morph cs)
  section-ctor' {Γ = Γ} {Δ} w ty1 c {cs} {p₀} p₁ = goal
    where
      coll = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p₀ m0)
      e = exists-params-≡ w Δ p₁ cs
      p = Σ-Params Δ (Wk₁-Alg w ω₁) p₁
      goal = from-≡ (begin
        proj₁ morph (CtorTm-Alg c σ-alg p)
          ≡⟨ cong (λ f → proj₁ (f _)) (to-≡ (snd init0 c p₀)) ⟩
        CtorTm-DAlg c ωd (proj₁ coll)
          ≡⟨ cong (CtorTm-DAlg c ωd) e ⟩
        CtorTm-DAlg c ωd (Params-Sect Δ (Σ-Params Δ (Wk₁-Alg w ω₁) p₁) morph cs)
          ∎)
  section-ctor' {Δ = Δ} w (ty2 x) c {cs = cs} {p} p₁ = goal
    where
      e-1 = exists-1 _ (Tm₁-Alg x (Wk₁-Alg w ω₁) p₁)
      coll = exists-params Δ (Wk₁-Alg w ω₁) (Wk-R-Alg w ωr) p₁ (Params₀-Sect Δ p m0)
      eq : e-1
         ≡ (Tm-DAlg x (Wk-DAlg w ωd) (proj₁ coll)
         , Tm-R-Alg x (Wk-R-Alg w ωr) (proj₂ coll))
      eq = exists-1-≡ w x p p₁
      cp1 = CtorTm₁-Alg c ω₁ p₁
      aux' : exists-2 _ (proj₁ e-1) (proj₂ e-1) (CtorTm₀-Alg c ω₀ p) cp1
           ≅ 
             exists-2 _
              (Tm-DAlg x (Wk-DAlg w ωd) (proj₁ coll))
              (Tm-R-Alg x (Wk-R-Alg w ωr) (proj₂ coll))
              (CtorTm₀-Alg c ω₀ p) cp1
      aux' = cong-≅ (λ z → exists-2 _ (proj₁ z) (proj₂ z) _ cp1) eq
      aux : exists-2 _
              (Tm-DAlg x (Wk-DAlg w ωd) (proj₁ coll))
              (Tm-R-Alg x (Wk-R-Alg w ωr) (proj₂ coll))
              (CtorTm₀-Alg c ω₀ p) _
          ≡ (CtorTm-DAlg c ωd (proj₁ coll) , CtorTm-R-Alg c ωr (proj₂ coll))
      aux = begin
        _ ≡⟨ to-≡ (cong' (λ f → f _ _ _ _) (snd init0 c p)) ⟩
        _ ≡⟨ h2'' c p₁ (lctr lin c) ⟩
        _ ∎
      w0 = Wk₀-Alg w ω₀
      w1 = Wk₁-Alg w ω₁
      T-1 = λ z → proj₂ Y (Tm₀-Alg x w0 p ,p _) z (CtorTm₀-Alg c ω₀ p ,p cp1)
      T-2 = λ z → R-T (Tm₀-Alg x w0 p ,p Tm₁-Alg x w1 p₁) z (CtorTm₀-Alg c ω₀ p ,p cp1)
      eqeq : proj₁ e-1 ≡ Tm-DAlg x (Wk-DAlg w ωd) (proj₁ coll)
      eqeq = cong proj₁ eq
      aux'' : _≅_ {_} {Σ (T-1 (proj₁ e-1))
                         (T-2 (proj₁ e-1))}
                      {Σ (T-1 (Tm-DAlg x (Wk-DAlg w ωd) (proj₁ coll)))
                         (T-2 (Tm-DAlg x (Wk-DAlg w ωd) (proj₁ coll)))}
              (exists-2 _ (proj₁ e-1) (proj₂ e-1) (CtorTm₀-Alg c ω₀ p) _)
              (CtorTm-DAlg c ωd (proj₁ coll) , CtorTm-R-Alg c ωr (proj₂ coll))
      aux'' = trans-≅ aux' (≡-to-≅ aux)
      goal' : proj₁ (exists-2 _ (proj₁ e-1) (proj₂ e-1) (CtorTm₀-Alg c ω₀ p) _)
            ≅ CtorTm-DAlg c ωd (Params-Sect Δ (Σ-Params Δ (Wk₁-Alg w ω₁) p₁) morph cs)
      goal' = trans-≅ (cong-proj₁-≅ eqeq {T-1} {T-2} aux'') (cong-≅ (CtorTm-DAlg c ωd)
               (exists-params-≡ w Δ p₁ cs))
      goal :
          transp
             (λ z →
                proj₂ Y _ z (CtorTm₀-Alg c ω₀ p ,p _))
             (from-≡ (Tm-Sect x morph cs))
             (proj₁ (exists-2 (Tm-Alg x (Wk-Alg w σ-alg) (Σ-Params Δ _ p₁)) _ (proj₂ e-1) (CtorTm₀-Alg c ω₀ p) _))
             ≡p
             CtorTm-DAlg c ωd (Params-Sect Δ (Σ-Params Δ (Wk₁-Alg w ω₁) p₁) morph cs)
      goal = from-≡ (homo-≅ (transp-absorb-≅
        (λ z → proj₂ Y _ z (CtorTm₀-Alg c ω₀ p ,p _)) (from-≡ (Tm-Sect x morph cs)) goal'))

  section-ctor''
    : ∀{Γ Δ B} →
      let C : Ctor Γ
          C = ctor Δ B
      in (w : Wk Ω Γ) (c : CtorTm Ω (C [ w ]c)) (cs : Spec-Sect Γ _ (Wk-DAlg w ωd) morph)
    → Ctor-Sect C (Σ-Ctor C (Wk₁-Alg w ω₁) (CtorTm₁-Alg c ω₁)) (CtorTm-DAlg c ωd) morph cs
  section-ctor'' {Δ = Δ} w c cs p =
    section-ctor' w _ c {cs} (Σ-Params-snd Δ (Wk₁-Alg w ω₁) p)

  is-section : ∀{Γ}(w : Wk Ω Γ) → Spec-Sect Γ (Σ-Spec Γ (Wk₁-Alg w ω₁)) (Wk-DAlg w ωd) morph
  is-section {Γ = init} w = ttp
  is-section {Γ ‣ C@(ctor Δ B)} w =
    ih ,P section-ctor'' {Γ} {Δ} {B} (w ∘w Drop) (v0c [ w ]ctm) ih
    where
      ih = is-section {Γ} (w ∘w Drop)

