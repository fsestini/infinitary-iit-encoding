{-# OPTIONS --prop --rewriting #-}

module relation.initial where

open import lib hiding (fst ; snd ; fstP ; sndP)
open import IIT.spec
open import erased.algebra
open import erased.section
-- open import erased.initial
open import predicate.algebra
open import predicate.initial
open import IIT.algebra
open import relation.algebra
open import sigma-construction
open import hoas-postulated as H

module InitRelTools
  (F₀) (F₁) (Y : DFam (Σ-Fam F₀ F₁))
  where

  rfam : DFam₀ F₀
  rfam = (λ a₀ → Pips (proj₁ F₁ a₀) (λ a₁ → El (proj₁ Y (pairp a₀ a₁)) => U))
       , (λ b₀ → Pi _ λ a → Pips (proj₂ F₁ (fstp a) b₀) λ b₁ → Pi (El (proj₁ Y a)) λ aᴰ → El (proj₂ Y a aᴰ (pairp b₀ b₁)) => U)

  m₀-to-rels : Morph₀ F₀ rfam → RelTys (Σ-Fam F₀ F₁) Y
  m₀-to-rels m₀ =
    (λ a x → Init-R-A (fstp a) (sndp a) x) ,
    (λ a aᴰ b x → Init-R-B a aᴰ (fstp b) (sndp b) x)
    where
      Init-R-A : ∀ a₀ a₁ → STerm (proj₁ Y (pairp a₀ a₁)) → SType
      Init-R-A a₀ a₁ aᴰ = proj₁ m₀ $ a₀ $ps a₁ $ aᴰ
  
      Init-R-B : ∀ a aᴰ b₀ b₁ → STerm (proj₂ Y a aᴰ (pairp b₀ b₁)) → SType
      Init-R-B a aᴰ b₀ b₁ bᴰ = proj₂ m₀ $ b₀ $ a $ps _ $ aᴰ $ bᴰ

  B-to-U : (B : Base Γ Δ)
           {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
           {γᴰ : Spec-DAlg Γ (Σ-Spec Γ γ₀ γ₁) Y}
           {p₀ : _} {p₁ : PTerm (Params₁-Alg Δ γ₀ p₀ F₁)}
           {a₀ : _} (a₁ : PTerm (Base₁-Alg B γ₀ p₀ a₀ F₁))
           {pᴰ : STerm (Params-DAlg Δ γᴰ (Σ-Params Δ γ₁ p₀ p₁))}
         → STerm (Base-DAlg B γᴰ pᴰ (Σ-Base B γ₁ p₁ a₀ a₁))
         → Term (Base₀-DAlg B a₀ rfam) → Term U
  B-to-U ty1 a₁ aᴰ R-A = R-A $ps a₁ $ aᴰ
  B-to-U {Γ = Γ} {Δ} (ty2 t) {γ₀} {γ₁} {γᴰ} {p₀} {p₁} {b₀} b₁ {pᴰ} bᴰ R-B =
    R-B $ a $ps b₁-need $ aᴰ $ bᴰ
    where
      a = Tm-Alg t (Σ-Spec Γ γ₀ γ₁) (Σ-Params Δ γ₁ p₀ p₁)
      aᴰ = Tm-DAlg t γᴰ pᴰ
      e = cong fstp (Σ-Tm' t {γ₁ = γ₁} p₀ p₁)
      b₁-need = transp-P (λ z → PTerm (proj₂ F₁ z b₀)) (from-≡ (sym e)) b₁

  T-to-U : (B : Ty Γ Δ)
           {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
           {γᴰ : Spec-DAlg Γ (Σ-Spec Γ γ₀ γ₁) Y} {p₀ : _} {p₁ : _} {a₀ : _}
         → (a₁ : PTerm (Ty₁-Alg B γ₀ p₀ a₀ F₁))
           {pᴰ : STerm (Params-DAlg Δ γᴰ (Σ-Params Δ γ₁ p₀ p₁))}
         → STerm (Ty-DAlg B γᴰ pᴰ (Σ-Ty B γ₁ p₁ a₀ a₁))
         → Term (Ty₀-DAlg B a₀ rfam)
         → Term U
  T-to-U (ext x) a₁ aᴰ ad₀ = 𝟙U
  T-to-U (base x) = B-to-U x
  T-to-U (Π A B) f₁ fᴰ fd₀ = PiU A (λ a → B-to-U B (f₁ $p a) (fᴰ $ a) (fd₀ $ a))
  T-to-U (B [ σ ]) a₁ aᴰ ad₀ = T-to-U B a₁ aᴰ ad₀
  T-to-U (B [ w ]') a₁ aᴰ ad₀ = T-to-U B a₁ aᴰ ad₀

  P-to-U : (Δ : Params Γ)
           {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
           {γᴰ : Spec-DAlg Γ (Σ-Spec Γ γ₀ γ₁) Y} {p₀ : _} {p₁ : _} 
         → STerm (Params-DAlg Δ γᴰ (Σ-Params Δ γ₁ p₀ p₁))
         → Term (Params₀-DAlg Δ p₀ rfam)
         → Term U
  P-to-U ● pᴰ pd₀ = 𝟙U
  P-to-U (Δ ‣‣ A) pᴰ pd₀ =
    SigmaU (P-to-U Δ (fst pᴰ) (fst pd₀)) λ _ → T-to-U A _ (snd pᴰ) (snd pd₀)
  P-to-U (Δ [ x ]p) pᴰ pd₀ = P-to-U Δ pᴰ pd₀

  to-B-R : (w : Wk Ω Γ) (A : Base Γ Δ) {m₀ : _}
           {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
           {γᴰ : Spec-DAlg Γ (Σ-Spec Γ γ₀ γ₁) Y}
           {p₀ : _} {p₁ : _} {pd : STerm (Params-DAlg Δ γᴰ (Σ-Params Δ γ₁ p₀ p₁))}
           {a₀ : _} {a₁ : _} (ad : STerm (Base-DAlg A γᴰ pd (Σ-Base A γ₁ p₁ a₀ a₁)))
         → B-to-U A {p₀ = p₀} a₁ ad (Base₀-Sect A a₀ m₀) ≡ Base-R-Alg A _ ad (m₀-to-rels m₀)
  to-B-R w ty1 x = refl
  to-B-R w (ty2 x₁) x = refl

  to-T-R : (w : Wk Ω Γ) (A : Ty Γ Δ) {m₀ : _}
           {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
           {γᴰ : Spec-DAlg Γ (Σ-Spec Γ γ₀ γ₁) Y}
           {p₀ : _} {p₁ : _} {pd : STerm (Params-DAlg Δ γᴰ (Σ-Params Δ γ₁ p₀ p₁))}
           {a₀ : _} {a₁ : _} (ad : STerm (Ty-DAlg A γᴰ pd (Σ-Ty A γ₁ p₁ a₀ a₁)))
         → T-to-U A {p₀ = p₀} a₁ ad (Ty₀-Sect A a₀ m₀) ≡ Ty-R-Alg A _ ad (m₀-to-rels m₀)
  to-T-R w (ext x) ad = refl
  to-T-R w (base x) ad = to-B-R w x ad
  to-T-R w (Π A B) fd = cong (PiU A) (funext (λ a → to-B-R w B (fd $ a)))
  to-T-R w (A [ x ]) ad = to-T-R w A ad
  to-T-R w (A [ w' ]') ad = to-T-R (w ∘w w') A ad
  
  to-P-R : (w : Wk Ω Γ) (Δ : Params Γ) {m₀ : _}
           {γ₀ : Spec₀-Alg Γ F₀} {γ₁ : Spec₁-Alg Γ γ₀ F₁}
           {γᴰ : Spec-DAlg Γ (Σ-Spec Γ γ₀ γ₁) Y}
           {p₀ : _} {p₁ : _} (pd : STerm (Params-DAlg Δ γᴰ (Σ-Params Δ γ₁ p₀ p₁)))
         → P-to-U Δ pd (Params₀-Sect Δ p₀ m₀) ≡ Params-R-Alg Δ _ pd (m₀-to-rels m₀)
  to-P-R w ● pd = refl
  to-P-R w (Δ ‣‣ A) pd =
    trans (cong (λ z → SigmaU z (λ _ → T-to-U A _ _ _)) (to-P-R w Δ (fst pd)))
          (cong (SigmaU _) (funext (λ _ → to-T-R w A (snd pd))))
  to-P-R w (Δ [ w' ]p) pd = to-P-R (w ∘w w') Δ pd
  {-# REWRITE to-P-R #-}

module InitialRel {F₀}
  (Ω) (ω₀ : Spec₀-Alg Ω F₀) (init₀ : is-initial₀ ω₀)
  (Y)
  where

  open InitPred Ω ω₀ init₀
  open InitRelTools F₀ preds Y

  private
    F₁ = preds
    ΣF = Σ-Fam F₀ F₁
    ω₁ : Spec₁-Alg Ω ω₀ preds
    ω₁ = init-is-pred-alg

  module _ (ωᴰ : Spec-DAlg Ω (Σ-Spec Ω ω₀ ω₁) Y) where

    r-dalg : Spec₀-DAlg Ω ω₀ rfam
    r-dalg {ctor Δ ty1} c = lam λ p₀ → lam λ pd₀ → lamps λ a₁ → lam λ aᴰ →
      let p₁ = pred-inv c p₀ a₁
          Δᴰ-ty = Params-DAlg Δ ωᴰ (Σ-Params Δ ω₁ p₀ p₁)
      in SigmaU Δᴰ-ty λ pᴰ → SigmaU (P-to-U Δ pᴰ pd₀) λ _ →
         LiftP (H.Id (proj₁ Y _) aᴰ (CtorTm-DAlg c ωᴰ $ _ $ pᴰ))
    r-dalg {ctor Δ (ty2 t)} c =
      lam λ p₀ → lam λ pd₀ → lam λ a → lamps λ b₁ →
        let
            e = pred-ix-inv c p₀ (fstp a) b₁
            T : STerm (proj₁ F₀) → Type
            T a₀ = Pips _ λ a₁ → Pips _ λ p → Pi (El (proj₁ Y (pairp a₀ a₁))) λ aᴰ
              → El (proj₂ Y _ aᴰ (pairp (CtorTm₀-Alg c ω₀ $ p₀) p)) => U
            aux : Term (T (Tm₀-Alg t ω₀ p₀))
            aux = lamps λ a₁ → lamps λ b₁ → lam λ aᴰ → lam λ bᴰ → 
              let p₁ = pred-inv c p₀ b₁
                  Δᴰ-ty = Params-DAlg Δ ωᴰ (Σ-Params Δ ω₁ p₀ p₁)
              in SigmaU Δᴰ-ty λ pᴰ → SigmaU (P-to-U Δ {p₁ = p₁} pᴰ pd₀) λ _ →
                   LiftP (SigmaP (H.Id (proj₁ Y _) aᴰ (Tm-DAlg t ωᴰ pᴰ)) λ e →
                          H.Id (proj₂ Y _ _ _)
                               (Transp (λ z → El (proj₂ Y _ z _)) e bᴰ)
                               (CtorTm-DAlg c ωᴰ $ _ $ pᴰ))
        in Transp T (Sym e) aux $ps sndp a $ps b₁

    the-init = init₀ r-dalg
    m₀ = lib.fst the-init

    Init-R-A : ∀ a₀ a₁ → STerm (proj₁ Y (pairp a₀ a₁)) → SType
    Init-R-A a₀ a₁ aᴰ = proj₁ (lib.fst the-init) $ a₀ $ps a₁ $ aᴰ

    Init-R-B : ∀ a aᴰ b₀ b₁ → STerm (proj₂ Y a aᴰ (pairp b₀ b₁)) → SType
    Init-R-B a aᴰ b₀ b₁ bᴰ = proj₂ (lib.fst the-init) $ b₀ $ a $ps _ $ aᴰ $ bᴰ

    init-rels : RelTys ΣF Y
    init-rels = m₀-to-rels m₀

    private

      Init-R-A-≡ : (c : CtorTm Ω (ctor Δ ty1)) (p₀ : _) (x : _) (y : _)
                 → Init-R-A (CtorTm₀-Alg c ω₀ $ p₀) x y ≡ (r-dalg c $ p₀ $ Params₀-Sect Δ p₀ m₀ $ps x $ y)
      Init-R-A-≡ c p₀ x y rewrite to-≡ (lib.snd the-init c p₀) = refl

      Init-R-B-≡ : ∀{t} (c : CtorTm Ω (ctor Δ (ty2 t))) (p₀ : _) (a : _) (aᴰ : _) (z : _) (w : _)
                 → Init-R-B a aᴰ (CtorTm₀-Alg c ω₀ $ p₀) z w
                 ≡ (r-dalg c $ p₀ $ Params₀-Sect Δ p₀ m₀ $ a $ps z $ aᴰ $ w)
      Init-R-B-≡ c p₀ a aᴰ _ _ rewrite to-≡ (lib.snd the-init c p₀) = refl

      init-rel-alg-aux : ∀{Δ} (t : Tm Ω Δ (base ty1)) (c : CtorTm Ω (ctor Δ (ty2 t)))
               (p₀ : STerm (Params₀-Alg Δ F₀)) (p₁ : PTerm (Params₁-Alg Δ ω₀ p₀ F₁))
               (pᴰ : STerm (Params-DAlg Δ ωᴰ (Σ-Params Δ ω₁ p₀ p₁))) (pr : STerm (Params-R-Alg Δ _ pᴰ init-rels))
             → STerm (Init-R-B _ (Tm-DAlg t ωᴰ pᴰ) (CtorTm₀-Alg c ω₀ $ p₀) _ (CtorTm-DAlg c ωᴰ $ _ $ pᴰ))
      init-rel-alg-aux {Δ = Δ} t c p₀ p₁ pᴰ pr =
        subst (λ x → STerm x) (sym (Init-R-B-≡ c p₀ _ _ _ _)) aux
        where
          aux : STerm (r-dalg c $ p₀ $ Params₀-Sect Δ _ m₀ $ _ $ps _ $ Tm-DAlg t ωᴰ pᴰ $ (CtorTm-DAlg c ωᴰ $ _ $ pᴰ))
          aux = pair pᴰ (pair pr (liftP (pairP (Refl _) (Refl _))))

    init-rel-alg : Spec-R-Alg Ω _ ωᴰ init-rels
    init-rel-alg {ctor Δ ty1} c = lam λ p → lam λ pᴰ → lam λ pr →
      let p₀ = Σ-Params-fst Δ ω₁ p
          true-goal : STerm (r-dalg c $ p₀ $ Params₀-Sect Δ _ m₀ $ps _ $ (CtorTm-DAlg c ωᴰ $ p $ pᴰ))
          true-goal = pair pᴰ (pair pr (liftP (Refl _)))
          goal : STerm (Init-R-A (CtorTm₀-Alg c ω₀ $ p₀) _ (CtorTm-DAlg c ωᴰ $ p $ pᴰ))
          goal = subst' STerm (sym (Init-R-A-≡ c p₀ _ _)) true-goal
      in goal
    init-rel-alg {ctor Δ (ty2 t)} c = lam λ p → lam λ pᴰ → lam λ pr →
        let p₀ = Σ-Params-fst Δ ω₁ p
            p₁ = Σ-Params-snd Δ ω₁ p
        in init-rel-alg-aux t c p₀ p₁ pᴰ pr

    R-A-inv-Params
      : (c : CtorTm Ω (ctor Δ ty1)) {p₀ : _} (p₁ : _) {aᴰ : _} 
      → STerm (Init-R-A (CtorTm₀-Alg c ω₀ $ p₀) (CtorTm₁-Alg c ω₁ $p p₀ $P p₁) aᴰ)
      → STerm (SigmaU (Params-DAlg Δ ωᴰ (Σ-Params Δ ω₁ p₀ p₁))
                      (λ pᴰ → Params-R-Alg Δ (Σ-Params Δ ω₁ p₀ p₁) pᴰ init-rels))
    R-A-inv-Params {Δ = Δ} c {p₀} p₁ {aᴰ} r-a =
      pair (fst aux) (fst (snd aux))
      where aux = subst' STerm (Init-R-A-≡ c p₀ _ aᴰ) r-a

    R-A-inv-Params-≡
      : ∀{Δ}(c : CtorTm Ω (ctor Δ ty1)) {p₀ : _} (p₁ : _)
        (pᴰ : STerm (Params-DAlg Δ ωᴰ (Σ-Params Δ ω₁ p₀ p₁)))
        (pr : STerm (Params-R-Alg Δ (Σ-Params Δ ω₁ p₀ p₁) pᴰ init-rels))
      → R-A-inv-Params c p₁ (CtorTm-R-Alg c init-rel-alg $ Σ-Params Δ ω₁ p₀ p₁ $ pᴰ $ pr)
      ≡ pair pᴰ pr
    R-A-inv-Params-≡ {Δ} c {p₀} p₁ pᴰ pr = refl

    R-A-constraint
      : (c : CtorTm Ω (ctor Δ ty1)) (p₀ : _) (p₁ : _) (aᴰ : _)
      → (r : STerm (Init-R-A _ (CtorTm₁-Alg c ω₁ $p p₀ $P p₁) aᴰ))
      → PTerm (H.Id (proj₁ Y _) aᴰ (CtorTm-DAlg c ωᴰ $ _ $ fst (R-A-inv-Params c p₁ r)))
    R-A-constraint c p₀ p₁ aᴰ r-a = unliftP (snd (snd aux))
      where aux = subst' STerm (Init-R-A-≡ c p₀ _ aᴰ) r-a
