{-# OPTIONS --prop --rewriting #-}

module hoas.internal where

open import lib renaming (ΣP to lib-ΣP)

data 𝕌 : Set
data U : Set
data P : Set
El : 𝕌 → Set
ElU : U → Set
ElP : P → Prop

data U where
  ΠU : (A : U) → (ElU A → U) → U
  ΠPU : (A : P) → (ElP A → U) → U
  ΣU : (A : U) → (ElU A → U) → U
  ΣpU : (A : U) → (ElU A → P) → U
  LiftP : P → U
  𝟙U : U
  𝟘U : U

data 𝕌 where
  Π : (A : 𝕌) → (El A → 𝕌) → 𝕌
  -- Πp : (A : P) → (ElP A → 𝕌) → 𝕌
  Σ𝕌 : (A : 𝕌) → (El A → 𝕌) → 𝕌
  -- Σp𝕌 : (A : 𝕌) → (El A → P) → 𝕌
  Ucode : 𝕌
  𝟙𝕌 : 𝕌
  𝟘𝕌 : 𝕌
  -- 𝟚𝕌 : 𝕌

data P where
  IdP : (A : U) → ElU A → ElU A → P
  Πp : (A : U) → (ElU A → P) → P
  ΠP : (A : P) → (ElP A → P) → P
  ΣP : (A : P) → (ElP A → P) → P
  ⊤P : P

El (Π A B) = (a : El A) → El (B a)
-- El (Πp A B) = (a : ElP A) → El (B a)
El (Σ𝕌 A B) = Σ (El A) λ x → El (B x)
-- El (Σp𝕌 A B) = Σp (El A) λ x → ElP (B x)
-- El (LiftP P) = Lift (ElP P)
El Ucode = U
El 𝟙𝕌 = 𝟙
El 𝟘𝕌 = 𝟘

ElU 𝟙U = 𝟙
ElU 𝟘U = 𝟘
ElU (ΠU A B) = (a : ElU A) → ElU (B a)
ElU (ΠPU A B) = (a : ElP A) → ElU (B a)
ElU (ΣU A B) = Σ (ElU A) (λ x → ElU (B x))
ElU (ΣpU A B) = Σp (ElU A) (λ x → ElP (B x))
ElU (LiftP x) = Lift (ElP x)
-- ElU 𝟚U = 𝟚

ElP (IdP A x y) = x ≡p y
ElP (Πp A P) = (a : ElU A) → ElP (P a)
ElP (ΠP A B) = (a : ElP A) → ElP (B a)
ElP (ΣP A B) = lib-ΣP (ElP A) λ a → ElP (B a)
ElP ⊤P = ⊤p

liftP : P → 𝕌
liftP (IdP A x x₁) = {!!}
liftP (Πp A x) = {!!}
liftP (ΠP a b) = Π (liftP a) λ x → liftP (b {!x!})
liftP (ΣP x x₁) = {!!}
liftP ⊤P = 𝟙𝕌

liftU : U → 𝕌
liftU (ΠU a b) = {!!}
liftU (ΠPU a b) = {!!}
liftU (ΣU a b) = {!!}
liftU (ΣpU a b) = {!!}
liftU (LiftP x) = {!!}
liftU 𝟙U = {!!}
liftU 𝟘U = {!!}

record Tm (T : 𝕌) : Set where
  constructor mkTm
  field
    ∣_∣Tm : El T

record TmU (T : U) : Set where
  constructor mkTm
  field
    ∣_∣TmU : ElU T
