{-# OPTIONS --prop --rewriting #-}

open import Data.Product using (_×_ ; Σ ; _,_ ; proj₁ ; proj₂) public
open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂) public
open import Agda.Primitive using (Level ; lsuc ; lzero ; _⊔_) public
open import Data.Empty public
open import Data.Sum public
open import Data.Nat using (ℕ) public

variable i j k l : Level

record _∼_ (A B : Set i) : Set i where
  field
    map1 : A → B
    map2 : B → A
open _∼_ public

record _∼p_ (A B : Prop i) : Prop i where
  field
    map1p : A → B
    map2p : B → A
open _∼p_ public

record 𝟙 : Set i where
  constructor tt

elim⊥ : {A : Set i} → ⊥ → A
elim⊥ ()

𝟘 = ⊥

data 𝟚 {i} : Set i where
  left : 𝟚
  right : 𝟚

case-𝟚 : (T : 𝟚 {lzero} → Set) → T left → T right → (x : 𝟚) → T x
case-𝟚 T h1 h2 left = h1
case-𝟚 T h1 h2 right = h2

_+_ : Set → Set → Set
A + B = Σ 𝟚 λ { left → A ; right → B }

module _ {A B : Set} where

  injl : A → A + B
  injl x = left , x

  injr : B → A + B
  injr x = right , x

  case+ : (T : A + B → Set)
        → ((x : A) → T (injl x))
        → ((x : B) → T (injr x))
        → (x : A + B) → T x
  case+ T h1 h2 (b , x) = case-𝟚 (λ b → ∀ x → T (b , x)) h1 h2 b x

-- module FixKit (F : Set × Set → Set × Set) where

--   data Fix1 : Set
--   data Fix2 : Set

--   {-# NO_POSITIVITY_CHECK #-}
--   data Fix1 where
--     fix1 : proj₁ (F (Fix1 , Fix2)) → Fix1

--   {-# NO_POSITIVITY_CHECK #-}
--   data Fix2 where
--     fix2 : proj₂ (F (Fix1 , Fix2)) → Fix2

--   unfix1 : Fix1 → proj₁ (F (Fix1 , Fix2))
--   unfix1 (fix1 x) = x

--   module FixElim
--     (T1 : Fix1 → Set)
--     (T2 : Fix2 → Set)
--     where

--     F' : Fix1 → Set
--     F' x = ?

--   module FixElim
--     (T1 : Fix1 → Set)
--     (T2 : Fix2 → Set)
--     (h1 : ∀ x y → proj₁ (F (T1 x , T2 y)) → T1 x)
--     (h2 : {!!})
--     where

--     elim1 : (x : Fix1) → T1 x
--     elim1 (fix1 x) = h1 (fix1 x) {!!} {!!}

--     elim2 : (x : Fix2) → T2 x

-- module _ where

--   F : Set × Set → Set × Set
--   F (C , T) = (𝟙 ⊎ (C × T)) , (C ⊎ (C × (ℕ → T)))

--   open FixKit F

-- module ContainerKit (S : 𝟚 {lzero} → Set) (P : (i : 𝟚) → S i → 𝟚 → Set) where

--   Cont : (𝟚 → Set) → (𝟚 → Set)
--   Cont F b = Σ (S b) λ s → (j : _) → P _ s j → F j

--   data Fix : 𝟚 → Set where
--     fix : (i : 𝟚) → Cont Fix i → Fix i

--   Fix1 : Set
--   Fix2 : Set

--   Fix1 = Fix left
--   Fix2 = Fix right

-- module _ where

--   S : 𝟚 → Set
--   S left = {!!}
--   S right = {!!}

--   open ContainerKit {!!} {!!}

data ∥_∥ (A : Set i) : Prop i where
  ∣_∣ : A -> ∥ A ∥

withTrunc : (S : Set i) (P : ∥ S ∥ → Prop j)
          → (t : ∥ S ∥) → ((x : S) → P ∣ x ∣) → P t
withTrunc S P ∣ x ∣ f = f x

postulate
  _≡p_ : {A : Set i} (x y : A) → Prop i
  reflp : {A : Set i} {x : A} → x ≡p x
  transp : {A : Set i} (B : A → Set j) {x y : A} -> x ≡p y → B x → B y
  transp-refl : {A : Set i} (B : A → Set j) {x : A} (p : x ≡p x) (d : B x)
              → transp B p d ≡ d
infix 4 _≡p_

{-# BUILTIN REWRITE _≡_ #-}
{-# REWRITE transp-refl #-}

to-≡ : {A : Set i} {x y : A} → x ≡p y → x ≡ y
to-≡ p = transp (λ y → _ ≡ y) p refl

from-≡ : {A : Set i} {x y : A} → x ≡ y → x ≡p y
from-≡ refl = reflp

module _ {A : Set i} (B : A → Set j) {x : A} {b : B x} where
  
  subst-refl : (p : x ≡ x) → subst B p b ≡ b
  subst-refl refl = refl

record Lift (A : Prop i) : Set i where
  constructor lift
  field
    unlift : A
open Lift public

transp-P : {A : Set i} (B : A → Prop j) {x y : A} -> x ≡p y → B x → B y
transp-P B p x = unlift (transp (λ x → Lift (B x)) p (lift x))

sym' : {A : Set i} {x y : A} → x ≡p y → y ≡p x
sym' p = transp-P (_≡p _) p reflp

trans' : {A : Set i} {x y z : A} → x ≡p y → y ≡p z → x ≡p z
trans' p q = transp-P (_ ≡p_) q p

cong' : {A : Set i} {B : Set j} (f : A → B) {x y : A} → x ≡p y → f x ≡p f y
cong' f p = transp-P (λ y → f _ ≡p f y) p reflp

transp-∘ : {A : Set i} (B : A → Set j) {x y z : _}
           (p : y ≡p z) (q : x ≡p y) (u : _)
         → transp B p (transp B q u) ≡ transp B (trans' q p) u
transp-∘ B p q u with to-≡ p
... | refl = refl
{-# REWRITE transp-∘ #-}

withProp : {P : Prop i} {Q : Prop j} -> P -> (P -> Q) -> Q
withProp x f = f x

withSet : {P : Set i} {Q : Set j} -> P -> (P -> Q) -> Q
withSet x f = f x

record ⊤ {i} : Set i where
  constructor tt
open ⊤ public

record ⊤p {i} : Prop i where
  constructor ttp
open ⊤p public

module _ {A : Set i} {x : A} (C : {y : A} (p : x ≡ y) → Set j) (d : C refl)
  where

  J : {y : A} (p : x ≡ y) → C p
  J refl = d

module _ {A : Set i} {x : A} (C : {y : A} (p : x ≡p y) → Set j) (d : C reflp)
  where

  Jp : {y : A} (p : x ≡p y) → C p
  Jp p = J (λ p → C (from-≡ p)) d (to-≡ p)

Fam : Set (lsuc i)
Fam {i = i} = Σ (Set i) λ A → A -> Set i

substP : {A : Set i} (P : A → Prop j) {x y : A} → x ≡ y → P x → P y
substP _ refl x = x

record LiftSet {i} (A : Set) : Set i where
  constructor liftSet
  field
    unliftSet : A
open LiftSet public

lift-unlift : {A : Set} {x : LiftSet {i} A} → liftSet (unliftSet x) ≡ x
lift-unlift = refl

record Σp {i j} (P : Set i) (Q : P -> Prop j) : Set (i ⊔ j) where
  constructor _,p_
  field
    fst : P
    snd : Q fst
open Σp public
  
record ΣP {i j} (P : Prop i) (Q : P -> Prop j) : Prop (i ⊔ j) where
  constructor _,P_
  field
    fstP : P
    sndP : Q fstP
open ΣP public

_×p_ : ∀{i j} → (P : Prop i) (Q : Prop j) → Prop (i ⊔ j)
P ×p Q = ΣP P λ _ → Q

sym-cancel : {A : Set i} (B : A → Set j) {x y : _} (p : x ≡ y) {z : _}
           → subst B p (subst B (sym p) z) ≡ z
sym-cancel _ refl = refl

record Iso (A : Set i) (B : Set j) : Set (i ⊔ j) where
  field
    iso1 : A → B
    iso2 : B → A
    iso-eq1 : (x : _) → iso2 (iso1 x) ≡p x
    iso-eq2 : (x : _) → iso1 (iso2 x) ≡p x
open Iso public

_≃_ = Iso

≃-refl : {A : Set i} → A ≃ A
≃-refl = record { iso1 = λ x → x ; iso2 = λ x → x
                ; iso-eq1 = λ x → reflp ; iso-eq2 = λ x → reflp }

tr1 : {A B : Set i} → A ≡ B → A → B
tr1 p = subst (λ x → x) p

tr2 : {A B : Set i} → A ≡ B → B → A
tr2 p = subst (λ x → x) (sym p)

tr1' : {A B : Set i} → A ≡p B → A → B
tr1' p = transp (λ x → x) p

tr2' : {A B : Set i} → A ≡p B → B → A
tr2' p = transp (λ x → x) (sym' p)

subst-sym : {A : Set i} (B : A → Set j) {x x' : A} (p : x ≡ x') (b : _)
          → subst B p (subst B (sym p) b) ≡ b
subst-sym B refl b = refl

subst-const : (A : Set i) (B : Set j) {x x' : A} (p : x ≡ x') (b : B)
            → subst (λ _ → B) p b ≡ b
subst-const A B refl b = refl

transp-const : (A : Set i) (B : Set j) {x x' : A} (p : x ≡p x') (b : B)
            → transp (λ _ → B) p b ≡ b
transp-const A B p b with to-≡ p
... | refl = refl
{-# REWRITE transp-const #-}

Σ-≡ : {A : Set i} {B : A -> Set j} {a a' : A} {b : B a} {b' : B a'}
     → (p : a ≡ a')
     → subst B p b ≡ b'
     → (a , b) ≡ (a' , b')
Σ-≡ refl refl = refl

×-≡ : {A : Set i} {B : Set j} {a a' : A} {b b' : B}
     → a ≡ a' → b ≡ b'
     → (a , b) ≡ (a' , b')
×-≡ refl refl = refl

uncurry : {A : Set i} {B : Set j} {C : Set k}
        → (A → B → C) → A × B → C
uncurry f x = f (proj₁ x) (proj₂ x)

Σ-≡p : {A : Set i} {B : A -> Set j} {a a' : A} (p : a ≡p a')
       {b : B a} {b' : B a'}
     → transp B p b ≡p b'
     → (a , b) ≡p (a' , b')
Σ-≡p p with to-≡ p
... | refl = cong' (_ ,_)

Σp-≡ : {A : Set i} {B : A -> Prop j} {a a' : A} {b : B a} {b' : B a'}
     → a ≡ a'
     → (a ,p b) ≡ (a' ,p b')
Σp-≡ refl = refl

Σp-≡p : {A : Set i} {B : A -> Prop j} {a a' : A} {b : B a} {b' : B a'}
      → a ≡p a'
      → (a ,p b) ≡p (a' ,p b')
Σp-≡p p = from-≡ (Σp-≡ (to-≡ p))

module _ {A : Set i} (B : A → Set j) {x y : A} (p : x ≡p y) (b : B x) where

  transp-to-subst : (p' : x ≡ y) → transp B p b ≡ subst B p' b
  transp-to-subst refl = refl

module _ {X : Set j}{A : Set i} {B : X -> A -> Prop k}
         {a : A} {x : X} {b : B x a}
  where

  Σp-subst : {y : X} (p : x ≡p y) {b' : _}
           → transp (λ x → Σp A (B x)) p (a ,p b) ≡ (a ,p b')
  Σp-subst p =
    Jp (λ {y} p → {b' : _} → transp (λ x → Σp A (B x)) p (a ,p b) ≡ (a ,p b')) refl p

-- shift-subst
--   : 

data _≅_ {A : Set i} : {B : Set i} → A → B → Set i where
  refl≅ : {a : A} → a ≅ a

module _
  {A : Set i} (B : A → Set j)
  where

  subst-to-≅ :  {x y : A} (p : x ≡ y) {b : B x} {b' : B y}
             → subst B p b ≡ b' → b ≅ b'
  subst-to-≅ refl refl = refl≅

  transp-to-≅ :  {x y : A} (p : x ≡p y) {b : B x} {b' : B y}
             → transp B p b ≡ b' → b ≅ b'
  transp-to-≅ p h with to-≡ p
  transp-to-≅ p refl | refl = refl≅

  ≅-to-subst :  {x y : A} (p : x ≡ y) {b : B x} {b' : B y}
             → b ≅ b' → subst B p b ≡ b'
  ≅-to-subst refl refl≅ = refl

cong-≅ : {A : Set i} {B : A → Set j}
         (f : (a : A) → B a) {x x' : A}
       → (p : x ≡ x') → f x ≅ f x'
cong-≅ f refl = refl≅

sym-≅ : {A B : Set i} {x : A} {y : B} → x ≅ y → y ≅ x
sym-≅ refl≅ = refl≅

trans-≅ : {A B C : Set i} {x : A} {y : B} {z : C} → x ≅ y → y ≅ z → x ≅ z
trans-≅ refl≅ p = p

ss-to-≅ : {A A' : Set} (B : A → Set) (f : A' → A)
        → let B' : A' → Set
              B' x' = B (f x')
        in {x : A} {x' y' : A'} (p : x ≡ f x') (q : y' ≡ x')
           {b : B x} {b' : B (f y')}
        → subst B p b ≡ subst B' q b' --  b'
        → b ≅ b'
ss-to-≅ B f refl refl refl = refl≅

-- tt-to-≅ : {A A' : Set} (B : A → Set) (f : A' → A)
--         → let B' : A' → Set
--               B' x' = B (f x')
--         in {x : A} {x' y' : A'} (p : x ≡p f x') (q : y' ≡p x')
--            {b : B x} {b' : B (f y')}
--         → transp B p b ≡ transp B' q b' --  b'
--         → b ≅ b'
-- tt-to-≅ B f p q h = {!ss-to-≅ B f ? ? ?!}


postulate
  funext
    : {A : Set i} {B : A → Set j} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x)
    → f ≡ g
  funextp
    : {A : Set i} {B : A → Set j} {f g : (x : A) → B x}
    → ((x : A) → f x ≡p g x)
    → f ≡p g

subst' : {A : Set i} (B : A → Set j) {x y : A} -> x ≡ y → B x → B y
subst' B p x = transp B (from-≡ p) x

postulate
  ≡-TODO : {A : Set} {x y : A} → x ≡ y
