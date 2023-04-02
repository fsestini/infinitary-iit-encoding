{-# OPTIONS --prop --rewriting --allow-unsolved-metas #-}

module IIT.spec where

open import lib
open import hoas-postulated hiding (Id)

data Spec : Set
data Params : Spec → Set
data Ty : (Γ : Spec) → Params Γ → Set
data Base : (Γ : Spec) → Params Γ → Set
record Ctor (Γ : Spec) : Set
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
  ext : ∀{Γ Δ} → Term U → Ty Γ Δ
  base : ∀{Γ Δ} → Base Γ Δ → Ty Γ Δ
  Π   : ∀{Γ Δ} → (A : Term U) → Base Γ (Δ ‣‣ ext A) → Ty Γ Δ
  _[_] : ∀{Γ ∇ Δ} → Ty Γ Δ → Sub ∇ Δ → Ty Γ ∇
  _[_]' : ∀{Ω Γ Δ} → Ty Γ Δ → (w : Wk Ω Γ) → Ty Ω (Δ [ w ]p)

data Base where
  ty1 : ∀{Γ Δ} → Base Γ Δ
  ty2 : ∀{Γ Δ} → Tm Γ Δ (base ty1) → Base Γ Δ

record Ctor Γ where
  inductive
  pattern
  constructor ctor
  field
    ctor-Params : Params Γ
    ctor-Base : Base Γ ctor-Params
open Ctor public

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
  ext : ∀{Γ Δ} (A : Term U) → Term (El A) → Tm Γ Δ (ext A)
  ctor : ∀{Γ Δ ∇ A} → CtorTm Γ (ctor Δ A) → (σ : Sub ∇ Δ) → Tm Γ ∇ ((base A) [ σ ])
  App : ∀{Γ Δ A B} → Tm Γ Δ (Π A B) → Tm Γ (Δ ‣‣ ext A) (base B)
  App-U : ∀{Γ Δ A B} → Tm Γ Δ (ext A) → (Term (El (A =>U B))) → Tm Γ Δ (ext B)
  Lam  : ∀{Γ Δ A B} → Tm Γ (Δ ‣‣ ext A) (base B) → Tm Γ Δ (Π A B)
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
  ext[] : ∀{A} {σ : Sub {Γ} Δ ∇} → ext A [ σ ] ≡ ext A

ext[]' : ∀{A θ} {σ : Sub {Γ} Δ ∇} {τ : Sub {Γ} Δ θ} → ext A [ σ ] ≡ (ext A [ τ ])
ext[]' = trans ext[] (sym ext[])

postulate
  Π[] : ∀{A B} {σ : Sub {Γ} Δ ∇} → Π A B [ σ ] ≡ Π A (B [ Ext (Drop ∘ σ) (subst (Tm _ _) ext[]' vz) ]b)

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
  [Id]p : ∀{Γ} {Δ : Params Γ} → Δ [ Id ]p ≡ Δ
  [Id]tm'-1 : (t : Tm Γ Δ (base ty1))
            → t [ Id ]tm'-1 ≡ subst' (λ z → Tm Γ z (base ty1)) (sym [Id]p) t
  [∘]p : ∀{Ω θ Γ Δ} {w : Wk Γ Ω} {w' : Wk θ Γ}
       → Δ [ w ]p [ w' ]p ≡p Δ [ w' ∘w w ]p
  ●[x]p : ∀{Ω Γ}{w : Wk Ω Γ} → ● [ w ]p ≡p ●
  Id[]ws : ∀{Ω Γ Δ}{w : Wk Ω Γ} → Id {Δ = Δ} [ w ]ws ≡ Id

  [Id]C : C [ Id ]c ≡ C
  [∘]c : ∀{Γ Ω ∇}(w : Wk Γ Ω) (w' : Wk Ω ∇) (C : Ctor ∇)
       → C [ w' ]c [ w ]c ≡ C [ w ∘w w' ]c

postulate
  [Id]ctm-≡ : ∀{Γ C} {c : CtorTm Γ C} → c [ Wk.Id ]ctm ≡ subst' (CtorTm _) (sym [Id]C) c
  [∘]ctm-≡ : ∀{Γ Ω ∇} (w : Wk Γ Ω) (w' : Wk Ω ∇) (C : Ctor ∇) (c : CtorTm ∇ C)
           → c [ w' ]ctm [ w ]ctm ≡ subst' (CtorTm _) (sym ([∘]c _ _ _)) (c [ w ∘w w' ]ctm)
  [Drop]ctm-≡ : ∀{C'} (c : CtorTm Γ C) → c [ Drop {Γ} {C'} ]ctm ≡ dropc c

  [Id]b' : ∀{Γ Δ} (B : Base Γ Δ) → B [ Id ]b' ≡ subst' (Base Γ) (sym [Id]p) B

  [∘]b' : ∀{Ω θ Γ Δ} {w : Wk Γ Ω} {w' : Wk θ Γ} (A : Base _ Δ)
       → A [ w ]b' [ w' ]b' ≡p transp (Base _) (sym' [∘]p) (A [ w' ∘w w ]b')

[Id]p-≡ : ∀{Γ} {Δ : Params Γ} → Δ [ Id ]p ≡ Δ
[Id]p-≡ = [Id]p

[∘]p-≡ : ∀{Ω θ Γ Δ} {w : Wk Γ Ω} {w' : Wk θ Γ}
       → Δ [ w ]p [ w' ]p ≡ Δ [ w' ∘w w ]p
[∘]p-≡ = to-≡ [∘]p

[∘]b'-≡ : ∀{Ω θ Γ Δ} {w : Wk Γ Ω} {w' : Wk θ Γ} {A : Base _ Δ}
        → A [ w ]b' [ w' ]b' ≡ transp (Base _) (sym' [∘]p) (A [ w' ∘w w ]b')
[∘]b'-≡ = to-≡ ([∘]b' _)
