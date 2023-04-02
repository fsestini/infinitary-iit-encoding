{-# OPTIONS --prop --rewriting #-}

module IIT.spec where

open import lib

postulate
  U : Set
  El : U → Set

data Spec : Set
data Params : Spec → Set
data Ty : (Γ : Spec) → Params Γ → Set
data Base : (Γ : Spec) → Params Γ → Set
data Ctor : Spec -> Set
data Sub : ∀{Γ} → Params Γ -> Params Γ -> Set
data Wk : Spec -> Spec -> Set
data Tm : (Γ : Spec) (Δ : Params Γ) → Ty Γ Δ → Set
data CtorTm : (Γ : Spec) → Ctor Γ → Set

data Spec where
  init : Spec
  _‣_  : (Γ : Spec) -> Ctor Γ -> Spec
infixl 5 _‣_

data Wk where
  Id : ∀{Γ} -> Wk Γ Γ
  Drop : ∀{Γ A} → Wk (Γ ‣ A) Γ
  _∘w_ : ∀{Γ Ω θ} -> Wk Γ Ω → Wk Ω θ → Wk Γ θ

data Params where
  ● : {Γ : Spec} → Params Γ
  _‣‣_ : {Γ : Spec} → (Δ : Params Γ) → Ty Γ Δ → Params Γ
  _[_]p : {Γ Δ : Spec} -> Params Δ -> Wk Γ Δ -> Params Γ

data Ty where
  ext : ∀{Γ Δ} → U → Ty Γ Δ
  base : ∀{Γ Δ} → Base Γ Δ → Ty Γ Δ
  Π   : ∀{Γ Δ} → (A : U) → Base Γ (Δ ‣‣ ext A) → Ty Γ Δ
  _[_] : ∀{Γ ∇ Δ} → Ty Γ Δ → Sub ∇ Δ → Ty Γ ∇
  _[_]' : ∀{Ω Γ Δ} → Ty Γ Δ → (w : Wk Ω Γ) → Ty Ω (Δ [ w ]p)

data Base where
  ty1 : ∀{Γ Δ} → Base Γ Δ
  ty2 : ∀{Γ Δ} → Tm Γ Δ (base ty1) → Base Γ Δ

data Ctor where
  ctor : ∀{Γ} (Δ : Params Γ) → Base Γ Δ → Ctor Γ

data Sub where
  Id   : ∀{Γ Δ} → Sub {Γ} Δ Δ
  Ext : ∀{Γ} {Δ ∇ : Params Γ} {A : _} → (σ : Sub Δ ∇) → Tm Γ Δ (A [ σ ]) → Sub Δ (∇ ‣‣ A)
  Drop : ∀{Γ Δ A} → Sub {Γ} (Δ ‣‣ A) Δ
  _∘_ : ∀{Ω} {Γ Δ ∇ : Params Ω} → Sub Γ Δ → Sub Δ ∇ → Sub Γ ∇
  _[_]ws : ∀{Γ Ω ∇ Δ} → Sub ∇ Δ → (w : Wk Γ Ω) →  Sub (∇ [ w ]p) (Δ [ w ]p)

data Tm where
  vz : ∀{Γ Δ A} → Tm Γ (Δ ‣‣ A) (A [ Drop ])
  vz1 : ∀{Γ Δ} → Tm Γ (Δ ‣‣ base ty1) (base ty1)
  vs : ∀{Γ Δ A B} → Tm Γ Δ A → Tm Γ (Δ ‣‣ B) (A [ Drop ])
  ext : ∀{Γ Δ} (A : U) → El A → Tm Γ Δ (ext A)
  ctor : ∀{Γ Δ ∇ A} → CtorTm Γ (ctor Δ A) → (σ : Sub ∇ Δ) → Tm Γ ∇ ((base A) [ σ ])
  app : ∀{Γ Δ A B} → Tm Γ Δ (Π A B) → Tm Γ (Δ ‣‣ ext A) (base B)
  app-U : ∀{Γ Δ A B} → Tm Γ Δ (ext A) → (El A → El B) → Tm Γ Δ (ext B)
  lam  : ∀{Γ Δ A B} → Tm Γ (Δ ‣‣ ext A) (base B) → Tm Γ Δ (Π A B)
  _[_]tm : ∀{Γ ∇ Δ A} → Tm Γ Δ A → (σ : Sub ∇ Δ) → Tm Γ ∇ (A [ σ ])
  _[_]tm' : ∀{Ω Γ Δ A} (t : Tm Γ Δ A) (w : Wk Ω Γ) → Tm Ω (Δ [ w ]p) (A [ w ]')
  _[_]tm'-1 : ∀{Ω Γ Δ} (t : Tm Γ Δ (base ty1)) (w : Wk Ω Γ) → Tm Ω (Δ [ w ]p) (base ty1)
  ctor-1 : ∀{Γ Δ ∇} → CtorTm Γ (ctor Δ ty1) → (σ : Sub ∇ Δ) → Tm Γ ∇ (base ty1)

_[_]b' : ∀{Ω Γ Δ} → Base Γ Δ → (w : Wk Ω Γ) → Base Ω (Δ [ w ]p)

_[_]c : ∀{Γ Ω} → Ctor Γ → Wk Ω Γ → Ctor Ω
ctor Δ A [ w ]c = ctor (Δ [ w ]p) (A [ w ]b')

data CtorTm where
  v0c : ∀{Γ A} → CtorTm (Γ ‣ A) (A [ Drop ]c)
  dropc : ∀{Γ A B} → CtorTm Γ A → CtorTm (Γ ‣ B) (A [ Drop ]c)
  _[_]ctm : ∀{Ω Γ A} → CtorTm Γ A → (w : Wk Ω Γ) → CtorTm Ω (A [ w ]c)

ty1 [ w ]b' = ty1
ty2 x [ w ]b' = ty2 (x [ w ]tm'-1)

variable
  Γ Ω : Spec
  Δ ∇ : Params Γ
  A : Ty Γ Δ
  B : Base Γ Δ
  C : Ctor Γ

_[_]b : ∀{Γ Δ ∇} → Base Γ Δ → Sub ∇ Δ → Base Γ ∇

postulate
  base[] : {σ : Sub {Γ} Δ ∇} → base B [ σ ] ≡ base (B [ σ ]b)
  base[]' : {w : Wk Ω Γ} → base B [ w ]' ≡ base (B [ w ]b')
  ext[] : {A : U} {σ : Sub {Γ} Δ ∇} → ext A [ σ ] ≡ ext A

ext[]' : ∀{A θ} {σ : Sub {Γ} Δ ∇} {τ : Sub {Γ} Δ θ} → ext A [ σ ] ≡ (ext A [ τ ])
ext[]' = trans ext[] (sym ext[])

ty1 [ σ ]b = ty1
ty2 x [ σ ]b = ty2 (subst (Tm _ _) base[] (x [ σ ]tm))

transp-ctortm : ∀{Γ Δ Δ'} {B : Base Γ Δ} {B' : Base Γ Δ'}
            (p : Δ ≡p Δ') (q : transp (Base _) p B ≡p B')
          → CtorTm Γ (ctor Δ B) → CtorTm Γ (ctor Δ' B')
transp-ctortm p q x with to-≡ p | to-≡ q
... | refl | refl = x

postulate
  Id∘w : ∀{Ω Γ} {w : Wk Ω Γ} → Id ∘w w ≡ w
  w∘Id : ∀{Ω Γ} {w : Wk Ω Γ} → w ∘w Id ≡ w
  assoc-∘w : ∀{Ω Γ θ ∇} (w : Wk Ω Γ) (w' : Wk Γ θ) (w'' : Wk θ ∇)
           → (w ∘w w') ∘w w'' ≡ (w ∘w (w' ∘w w''))
  [Id]p-≡ : ∀{Γ} {Δ : Params Γ} → Δ [ Id ]p ≡ Δ
  [Id]tm'-1-≡ : (t : Tm Γ Δ (base ty1))
              → t [ Id ]tm'-1 ≡ subst' (λ z → Tm Γ z (base ty1)) (sym [Id]p-≡) t
  [∘]tm'-1 : ∀{Ω θ Γ Δ} {w : Wk Γ Ω} {w' : Wk θ Γ} (t : Tm _ Δ (base ty1))
           → (t [ w ]tm'-1 [ w' ]tm'-1) ≅ (t [ w' ∘w w ]tm'-1)
  [∘]p-≡ : ∀{Ω θ Γ Δ} {w : Wk Γ Ω} {w' : Wk θ Γ}
         → Δ [ w ]p [ w' ]p ≡ Δ [ w' ∘w w ]p
  ●[x]p : ∀{Ω Γ}{w : Wk Ω Γ} → ● [ w ]p ≡p ●
  ‣‣[]p : (w : Wk Ω Γ) → (Δ ‣‣ A) [ w ]p ≡ ((Δ [ w ]p) ‣‣ (A [ w ]'))
  Id[]ws : ∀{Ω Γ Δ}{w : Wk Ω Γ} → Id {Δ = Δ} [ w ]ws ≡ Id
  Drop[]ws-≅ : ∀{Ω Γ Δ A}{w : Wk Ω Γ}
             → (Drop {Γ} {Δ} {A} [ w ]ws) ≅ Sub.Drop {Ω} {Δ [ w ]p} {A [ w ]'} 
  ∘[]ws : ∀{Ω Γ Δ ∇ Δ'} {w : Wk Ω Γ} {σ : Sub Δ ∇} {σ' : Sub ∇ Δ'}
        → (σ ∘ σ') [ w ]ws ≡ ((σ [ w ]ws) ∘ (σ' [ w ]ws))

  [Id]c-≡ : (C : Ctor Γ) → C [ Id ]c ≡ C

  [∘]c : ∀{Γ Ω ∇}(w : Wk Γ Ω) (w' : Wk Ω ∇) (C : Ctor ∇)
       → C [ w' ]c [ w ]c ≡ C [ w ∘w w' ]c

  vz1[]tm'-1-≅ : ∀{Δ} (w : Wk Ω Γ) → (vz1 {Γ} {Δ} [ w ]tm'-1) ≅ vz1 {Ω} {Δ [ w ]p}

  ctor-1[]tm'-1 : ∀{Γ Δ ∇} (w : Wk Ω Γ)(c : CtorTm Γ (ctor Δ ty1)) (σ : Sub ∇ Δ)
            → (ctor-1 c σ [ w ]tm'-1) ≡ ctor-1 (c [ w ]ctm) (σ [ w ]ws)

{-# REWRITE [Id]c-≡ #-}
{-# REWRITE [∘]c #-}

[∘]b'-≅ : ∀{Ω θ Γ Δ} {w : Wk Γ Ω} {w' : Wk θ Γ} (A : Base _ Δ)
     → (A [ w ]b' [ w' ]b') ≅ (A [ w' ∘w w ]b')
[∘]b'-≅ ty1 = cong-≅ (λ z → ty1 {_} {z}) [∘]p-≡
[∘]b'-≅ (ty2 x) = cong-≅ (λ z → ty2 {_} {proj₁ z} (proj₂ z))
                    (Σ-≡ [∘]p-≡ (≅-to-subst _ _ ([∘]tm'-1 x))) 

[∘]b'-≡ : ∀{Ω θ Γ Δ} {w : Wk Γ Ω} {w' : Wk θ Γ} (A : Base _ Δ)
     → A [ w ]b' [ w' ]b' ≡ subst' (Base _) (sym [∘]p-≡) (A [ w' ∘w w ]b')
[∘]b'-≡ A = ≅-to-transp' (Base _) _ ([∘]b'-≅ A)

postulate
  [Id]ctm-≡ : ∀{Γ C} {c : CtorTm Γ C} → c [ Id ]ctm ≡ c
  [∘]ctm-≡ : ∀{Γ Ω ∇} (w : Wk Γ Ω) (w' : Wk Ω ∇) (C : Ctor ∇) (c : CtorTm ∇ C)
           → c [ w' ]ctm [ w ]ctm ≡ c [ w ∘w w' ]ctm
  [Drop]ctm-≡ : ∀{C'} (c : CtorTm Γ C) → c [ Drop {Γ} {C'} ]ctm ≡ dropc c

{-# REWRITE [Id]ctm-≡ [∘]ctm-≡ [Drop]ctm-≡ #-}

--------------------------------------------------------------------------------
-- Linear specifications

data PWk : {Γ : Spec} (Δ ∇ : Params Γ) → Sub Δ ∇ → Set where
  Id : ∀{Γ Δ} → PWk {Γ} Δ Δ Id
  Drop : ∀{Γ Δ ∇ A σ} → PWk {Γ} Δ ∇ σ → PWk {Γ} (Δ ‣‣ A) ∇ (Drop ∘ σ) -- (DDrop σ)

PWk-wk : ∀{σ} (w : Wk Ω Γ) (pwk : PWk Δ ∇ σ) → PWk (Δ [ w ]p) (∇ [ w ]p) (σ [ w ]ws)
PWk-wk w Id = subst (PWk _ _) (sym Id[]ws) Id
PWk-wk w (Drop {∇ = ∇} {A = A} {σ} pwk) =
  subst (λ z → PWk (proj₁ z) (∇ [ w ]p) (proj₂ z))
    (Σ-≡ pf (≅-to-subst T pf (sym-≅ (trans-≅
      (≡-to-≅ (∘[]ws {w = w} {Drop} {σ}))
       (cong-≅' (λ x y → _∘_ {_} {x} y (σ [ w ]ws)) (sym pf) Drop[]ws-≅)))))
    (PWk.Drop {A = A [ w ]'} (PWk-wk w pwk))
  where
    T = λ v → Sub v (∇ [ w ]p)
    pf = sym (‣‣[]p w)

data LinearSpec : Spec → Set
data LinearCtor {Γ} : Ctor Γ → Set

data LinearSpec where
  l-● : LinearSpec init
  l-‣ : ∀{Γ A} → LinearSpec Γ → LinearCtor A → LinearSpec (Γ ‣ A)

data LinearCtor {Γ} where
  l-ctor1 : ∀{Δ} → LinearCtor (ctor Δ ty1)
  l-ctor2 : ∀{Δ ∇ σ} (c : CtorTm Γ (ctor ∇ ty1)) (pwk : PWk _ _ σ)
          → LinearCtor (ctor Δ (ty2 (ctor-1 c σ)))
  l-ctor2-var : ∀{Δ} → LinearCtor (ctor (Δ ‣‣ base ty1) (ty2 vz1)) -- (vz {Γ} {Δ} {base ty1})))

lctr-wk : (w : Wk Ω Γ) → LinearCtor C → LinearCtor (C [ w ]c)
lctr-wk w l-ctor1 = l-ctor1
lctr-wk w (l-ctor2 c pwk) =
  subst (λ z → LinearCtor (ctor _ z))
    (cong ty2 (sym (ctor-1[]tm'-1 w c _)))
    (l-ctor2 (c [ w ]ctm) (PWk-wk w pwk))
lctr-wk w l-ctor2-var =
  subst (λ z → LinearCtor (ctor (proj₁ z) (proj₂ z)))
    (Σ-≡ pf (≅-to-subst (Base _) pf (cong-≅ (λ z → ty2 {_} {proj₁ z} (proj₂ z))
        (Σ-≡ pf (≅-to-subst (λ v → Tm _ v (base ty1)) pf
          (sym-≅ (vz1[]tm'-1-≅ w))))))) l-ctor2-var
  where pf = sym (trans (‣‣[]p w) (cong ((_ [ w ]p) ‣‣_) base[]'))

lspec-wk : (w : Wk Ω Γ) → LinearSpec Ω → LinearSpec Γ
lspec-wk Id sp = sp
lspec-wk Drop (l-‣ sp x) = sp
lspec-wk (w ∘w w') sp = lspec-wk w' (lspec-wk w sp)

lctr : ∀{Ω A} → LinearSpec Ω → CtorTm Ω A → LinearCtor A
lctr (l-‣ sp x) v0c = lctr-wk Drop x
lctr (l-‣ sp x) (dropc c) = lctr-wk Drop (lctr sp c)
lctr sp (c [ w ]ctm) = lctr-wk w (lctr (lspec-wk w sp) c)

