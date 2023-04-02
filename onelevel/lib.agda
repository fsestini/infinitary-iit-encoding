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
  true : 𝟚
  false : 𝟚

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

subst' : {A : Set i} (B : A → Set j) {x y : A} -> x ≡ y → B x → B y
subst' B p = transp B (from-≡ p)

cong-transp : {A : Set i} (B : A → Set j) (f : (x : A) → B x)
            → {x y : A} (p : y ≡p x) → f x ≡ transp B p (f y)
cong-transp B f p with to-≡ p
... | refl = refl

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

transp-∘ : {A : Set i} (B : A → Set j) {x y z : _}
           (p : y ≡p z) (q : x ≡p y) (u : _)
         → transp B p (transp B q u) ≡ transp B (trans' q p) u
transp-∘ B p q u with to-≡ p
... | refl = refl
{-# REWRITE transp-∘ #-}

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

Σ-≡ : {A : Set i} {B : A -> Set j} {a a' : A} {b : B a} {b' : B a'}
     → (p : a ≡ a')
     → subst B p b ≡ b'
     → (a , b) ≡ (a' , b')
Σ-≡ refl refl = refl

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

homo-≅ : {A : Set i} {x y : A} → x ≅ y → x ≡ y
homo-≅ refl≅ = refl

≡-to-≅ : {A : Set i} {x y : A} → x ≡ y → x ≅ y
≡-to-≅ refl = refl≅

module _
  {A : Set i} (B : A → Set j)
  where

  subst-to-≅ :  {x y : A} (p : x ≡ y) {b : B x} {b' : B y}
             → subst B p b ≡ b' → b ≅ b'
  subst-to-≅ refl refl = refl≅

  ≅-to-subst :  {x y : A} (p : x ≡ y) {b : B x} {b' : B y}
             → b ≅ b' → subst B p b ≡ b'
  ≅-to-subst refl refl≅ = refl

  ≅-to-transp : {x y : A} (p : x ≡p y) {b : B x} {b' : B y}
             → b ≅ b' → transp B p b ≡ b'
  ≅-to-transp p with to-≡ p
  ... | refl = λ { refl≅ → refl }

  ≅-to-transp' : {x y : A} (p : y ≡p x) {b : B x} {b' : B y}
             → b ≅ b' → b ≡ transp B p b'
  ≅-to-transp' p with to-≡ p
  ... | refl = λ { refl≅ → refl }

  transp-absorb-≅
    : {x y : A} (p : x ≡p y) {b : B x} {b' : B y}
    → b ≅ b' → transp B p b ≅ b'
  transp-absorb-≅ p with to-≡ p
  ... | refl = λ x → x

  transp-absorb-≅¹
    : {x y : A} (p : x ≡p y) {b : B x} {b' : B y}
    → transp B p b ≅ b'
    → b ≅ b'
  transp-absorb-≅¹ p with to-≡ p
  ... | refl = λ x → x

  transp-absorb-≅'
    : {C : Set j} {x y : A} (p : y ≡p x) {b : C} {b' : B y}
    → b ≅ b' → b ≅ transp B p b'
  transp-absorb-≅' p with to-≡ p
  ... | refl = λ x → x

module _
  {A A' : Set i} (B : A → Set j) (B' : A' → Set j)
  where
  
  tr-tr-≅
    : {x y : A} (p : x ≡p y) {b : B x}
      {x' y' : A'} (p' : x' ≡p y') {b' : B' x'}
    → b ≅ b'
    → transp B p b ≅ transp B' p' b'
  tr-tr-≅ p p' q with to-≡ p | to-≡ p'
  ... | refl | refl = q

  tr-tr-≅¹
    : {x y : A} (p : x ≡p y) {b : B x}
      {x' y' : A'} (p' : x' ≡p y') {b' : B' x'}
    → transp B p b ≅ transp B' p' b'
    → b ≅ b'
  tr-tr-≅¹ p p' q with to-≡ p | to-≡ p'
  ... | refl | refl = q


cong-≅ : {A : Set i} {B : A → Set j}
         (f : (a : A) → B a) {x x' : A}
       → (p : x ≡ x') → f x ≅ f x'
cong-≅ f refl = refl≅

cong-proj₁-≅ : {X : Set i} {x y : X} → x ≡ y
             → {A : X → Set j} {B : (x : X) → A x → Set k}
               {p : Σ (A x) (B x)} {p' : Σ (A y) (B y)}
             → p ≅ p'
             → proj₁ p ≅ proj₁ p'
cong-proj₁-≅ refl refl≅ = refl≅

cong-≅' : {A : Set i} {B : A → Set j} {C : (a : A) → B a → Set k}
          (f : (a : A) → (b : B a) → C a b) {x x' : A} (p : x ≡ x')
          {b : B x} {b' : B x'} (q : b ≅ b')
         → f x b ≅ f x' b'
cong-≅' f refl q = cong-≅ (f _) (homo-≅ q)

sym-≅ : {A B : Set i} {x : A} {y : B} → x ≅ y → y ≅ x
sym-≅ refl≅ = refl≅

trans-≅ : {A B C : Set i} {x : A} {y : B} {z : C} → x ≅ y → y ≅ z → x ≅ z
trans-≅ refl≅ p = p

postulate
  funext
    : {A : Set i} {B : A → Set j} {f g : (x : A) → B x}
    → ((x : A) → f x ≡ g x)
    → f ≡ g
  funextp
    : {A : Set i} {B : A → Set j} {f g : (x : A) → B x}
    → ((x : A) → f x ≡p g x)
    → f ≡p g

Σ-≅ : {A : Set i} {B : A → Set j} {x x' : A} {y : B x} {y' : B x'}
    → x ≅ x'
    → y ≅ y'
    → (x , y) ≡ (x' , y')
Σ-≅ refl≅ refl≅ = refl

fun-subst : {X : Set i} {A : Set k} (B : X → A → Set j) {x x' : X} (p : x ≡ x') (f : _)
          → subst (λ x → (n : A) → B x n) p f
          ≡ λ n → subst (λ x → B x n) p (f n)
fun-subst B refl f = refl

cong-proj₂ : {A : Set i} {B : A → Set j} {p q : Σ A B}
           → (e : p ≡ q) → subst B (cong proj₁ e) (proj₂ p) ≡ proj₂ q
cong-proj₂ refl = refl

helper : ∀{i j k} {N : Set k} {A : N → Set i} {B : (n : N) → A n → Set j}
              {f : (n : N) → A n} {g : (n : N) → B n (f n)}
              {f' : (n : N) → A n} {g' : (n : N) → B n (f' n)}
            → ((n : N) → _≡_ {A = Σ (A n) (B n)} (f n , g n) (f' n , g' n))
            → _≡_ {A = Σ ((n : N) → A n) λ f → (n : N) → B n (f n)}
                  ((λ n → f n) , (λ n → g n))
                  (f' , g')
helper {N = N} {B = B} {f} {g} h =
  Σ-≡ (funext (λ x → cong proj₁ (h x)))
      (trans (fun-subst {A = N} (λ f n → B n (f n)) {f} _ g)
        (funext (λ x →
            ≅-to-subst (λ x₁ → B x (x₁ x)) (funext (λ x₁ → cong proj₁ (h x₁)))
              (subst-to-≅ (B x) (cong proj₁ (h x)) (cong-proj₂ (h x)))
          )))

fun-transp : {X A : Set} (B : X → A → Set) {x x' : X} (p : x ≡p x') (f : _)
          → transp (λ x → (n : A) → B x n) p f
          ≡ λ n → transp (λ x → B x n) p (f n)
fun-transp B p with to-≡ p
... | refl = λ f → refl

module ≅-Reasoning {a} where 

  infix  3 _∎≅
  infixr 2 _≅⟨⟩_ step-≅ step-≅˘
  infix  1 begin≅_

  begin≅_ : {A B : Set a} {x : A} {y : B} → x ≅ y → x ≅ y
  begin≅_ x≅y = x≅y

  _≅⟨⟩_ : {A B : Set a} (x : A) {y : B} → x ≅ y → x ≅ y
  _ ≅⟨⟩ x≅y = x≅y

  step-≅ : {A B C : Set a} (x : A) {y : B} {z : C} → y ≅ z → x ≅ y → x ≅ z
  step-≅ _ y≅z x≅y = trans-≅ x≅y y≅z

  step-≅˘ : {A B C : Set a} (x : A) {y : B} {z : C} → y ≅ z → y ≅ x → x ≅ z
  step-≅˘ _ y≅z y≅x = trans-≅ (sym-≅ y≅x) y≅z

  _∎≅ : {A : Set a} (x : A) → x ≅ x
  _∎≅ _ = refl≅

  syntax step-≅  x y≅z x≅y = x ≅⟨  x≅y ⟩ y≅z
  syntax step-≅˘ x y≅z y≅x = x ≅˘⟨ y≅x ⟩ y≅z

postulate
  admit≡ : {A : Set i} {x y : A} → x ≡ y


module _
  {A : Set} {B : A → Set} {C : A → Set} {D : (a : A) → B a → C a → Set}
  {a : A} {b : B a} {c : C a} {d : D a b c}
  where
  
  ΣΣ-≡ : {b' : B a} {d' : D a b' c}
       → _≡_ {A = Σ (B a) λ b → D a b _} (b , d) (b' , d')
       → _≡_ {A = Σ (Σ A B) (λ x → Σ (C (proj₁ x)) (D (proj₁ x) (proj₂ x)))} ((a , b) , (c , d)) ((a , b') , (c , d'))
  ΣΣ-≡ refl = refl
