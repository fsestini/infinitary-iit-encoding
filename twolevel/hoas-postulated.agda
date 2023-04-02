{-# OPTIONS --prop --rewriting #-}

module hoas-postulated where

open import lib hiding (fst ; snd ; fstP ; sndP)

postulate
  Type : Set
  Term : Type → Set
  U : Type
  El : Term U → Type
  P : Type
  ElP : Term P → Type
  PTerm : Term P → Prop

SType = Term U
SProp = Term P

STerm : SType → Set
STerm X = Term (El X)

postulate
  Pi : (A : Type) (B : Term A → Type) → Type
  PiU : (A : Term U) (B : Term (El A) → Term U) → Term U
  PipU : (A : Term P) (B : PTerm A → Term U) → Term U
  Pips : (A : Term P) (B : PTerm A → Type) → Type
  PiP : (A : Term P) (B : PTerm A → Term P) → Term P
  Pip : (A : Term U) (B : Term (El A) → Term P) → Term P
  Sigma : (A : Type) (B : Term A → Type) → Type
  SigmaU : (A : SType) (B : STerm A → SType) → SType
  Sigmap : (A : Term U) (B : Term (El A) → Term P) → Term U
  SigmaP : (A : Term P) (B : PTerm A → Term P) → Term P
  𝟙U : SType
  𝟘U : SType
  starU : STerm 𝟙U
  Unit : Type
  star : Term Unit
  Top : Term P
  truth : PTerm Top
  exfalso : (A : Type) → STerm 𝟘U → Term A

  LiftP : Term P → Term U
  liftP : ∀{p} → PTerm p → STerm (LiftP p)
  unliftP : ∀{p} → STerm (LiftP p) → PTerm p

  liftP-unliftP-≡ : ∀ P (p : STerm (LiftP P)) → liftP (unliftP p) ≡ p

  El-Σ : ∀{A B} → El (SigmaU A B) ≡ Sigma (El A) λ x → El (B x)
  El-Π : ∀{A B} → El (PiU A B) ≡ Pi (El A) λ x → El (B x)
  El-𝟙 : El 𝟙U ≡ Unit
  Unit-η : (t : Term Unit) → t ≡ star

{-# REWRITE El-Σ El-Π El-𝟙 #-}

_=>U_ : (A B : Term U) → Term U
A =>U B = PiU A (λ _ → B)

PairU : (A B : SType) → SType
PairU A B = SigmaU A (λ _ → B)

_=>P_ : (A B : Term P) → Term P
A =>P B = PiP A (λ _ → B)

module _ {A : Type} {B : Term A → Type} where

  postulate
    lam : ((a : Term A) → Term (B a)) → Term (Pi A B)
    pair : (a : Term A) (b : Term (B a)) → Term (Sigma A B)
    app : Term (Pi A B) → (a : Term A) → Term (B a)
    fst : Term (Sigma A B) → Term A
    snd : (p : Term (Sigma A B)) → Term (B (fst p))

  postulate
    β-≡ : (f : (a : Term A) → Term (B a)) (a : Term A)
        → app (lam f) a ≡ f a
    η-≡ : (f : Term (Pi A B)) → lam (app f) ≡ f

    Σ-β-≡-fst : (a : Term A) (b : Term (B a)) → fst (pair a b) ≡ a
    Σ-η-≡ : (p : _) → pair (fst p) (snd p) ≡ p

  {-# REWRITE β-≡ η-≡ Σ-β-≡-fst Σ-η-≡ #-}

  postulate
    Σ-β-≡-snd : (a : Term A) (b : Term (B a)) → snd (pair a b) ≡ b

  {-# REWRITE Σ-β-≡-snd #-}

  Pi-funext : {f g : Term (Pi A B)}
            → ((a : Term A) → app f a ≡ app g a)
            → f ≡ g
  Pi-funext {f} {g} h = goal
    where
      goal : lam (app f) ≡ lam (app g)
      goal = cong lam (funext (λ a → h a))

  infixl -1 _$_
  _$_ : Term (Pi A B) → (x : Term A) → Term (B x)
  f $ x = app f x

postulate
  Σ-η-*-≡ : ∀{A} (p : Term (Sigma A λ _ → Unit)) → pair (fst p) star ≡ p

{-# REWRITE Σ-η-*-≡ #-}

pair-≡ : ∀{A} {B : Term A → Type}{a a' : Term A} {b : Term (B a)} {b' : Term (B a')}
       → (p : a ≡ a')
       → lib.transp (λ x → Term (B x)) (from-≡ p) b ≡ b'
       → (pair a b) ≡ (pair a' b')
pair-≡ refl refl = refl

module _ {A : Term U} {B : Term (El A) → Term P} where

  postulate
    lamp : ((a : Term (El A)) → PTerm (B a)) → PTerm (Pip A B)
    appp : PTerm (Pip A B) → (a : Term (El A)) → PTerm (B a)
    fstp : Term (El (Sigmap A B)) → Term (El A)
    sndp : (p : Term (El (Sigmap A B))) → PTerm (B (fstp p))
    pairp : (a : Term (El A)) (b : PTerm (B a)) → Term (El (Sigmap A B))

    Σp-β-≡-fst : (a : Term (El A)) (b : PTerm (B a)) → fstp (pairp a b) ≡ a
    Σp-η-≡ : (p : _) → pairp (fstp p) (sndp p) ≡ p

  {-# REWRITE Σp-β-≡-fst Σp-η-≡ #-}

  infixl -1 _$p_
  _$p_ : PTerm (Pip A B) → (x : Term (El A)) → PTerm (B x)
  f $p x = appp f x



module _ {A : Term P} {B : PTerm A → Type} where

  postulate
    lamps : ((a : PTerm A) → Term (B a)) → Term (Pips A B)
    appps : Term (Pips A B) → (a : PTerm A) → Term (B a)

    ps-β : ∀ f → appps (lamps f) ≡ f
    ps-η : ∀ f → lamps (appps f) ≡ f

  {-# REWRITE ps-β ps-η #-}

  infixl -1 _$ps_
  _$ps_ : Term (Pips A B) → (x : PTerm A) → Term (B x)
  f $ps x = appps f x

module _ {A : Term P} {B : PTerm A → SType} where

  postulate
    lampu : ((a : PTerm A) → STerm (B a)) → STerm (PipU A B)
    apppu : STerm (PipU A B) → (a : PTerm A) → STerm (B a)

  infixl -1 _$pu_
  _$pu_ : STerm (PipU A B) → (x : PTerm A) → STerm (B x)
  f $pu x = apppu f x

module _ {A : Term P} {B : PTerm A → Term P} where

  postulate
    lamP : ((a : PTerm A) → PTerm (B a)) → PTerm (PiP A B)
    appP : PTerm (PiP A B) → (a : PTerm A) → PTerm (B a)
    fstP : PTerm (SigmaP A B) → PTerm A
    sndP : (p : _) → PTerm (B (fstP p))
    pairP : (a : PTerm A) (b : PTerm (B a)) → PTerm (SigmaP A B)

  infixl -1 _$P_
  _$P_ : PTerm (PiP A B) → (x : PTerm A) → PTerm (B x)
  f $P x = appP f x

_=>_ : (A : Type) (B : Type) → Type
A => B = Pi A (λ _ → B)

Pair : (A : Type) (B : Type) → Type
Pair A B = Sigma A (λ _ → B)

postulate
  Id : (A : Term U) → Term (El A) → Term (El A) → Term P
  Refl : {A : Term U} (x : Term (El A)) → PTerm (Id A x x)

  Transp : ∀ {A} (B : Term (El A) → Type)
            {x y : Term (El A)} → PTerm (Id A x y) → Term (B x) → Term (B y)

  Transp-refl-≡ : ∀ {A} (B : Term (El A) → Type)
                {x : Term (El A)} (b : Term (B x))
              → Transp {A} B (Refl x) b ≡ b
{-# REWRITE Transp-refl-≡ #-}

Refl' : {A : Term U} {x y : Term (El A)} → x ≡ y → PTerm (Id A x y)
Refl' refl = Refl _

TranspP : {A : Term U} (B : Term (El A) → Term P)
          {x y : Term (El A)} → PTerm (Id A x y) → PTerm (B x) → PTerm (B y)
TranspP B e u = unliftP aux
  where
    aux = Transp (λ a → El (LiftP (B a))) e (liftP u)

Sym : {A : Term U} {x y : _} → PTerm (Id A x y) → PTerm (Id A y x)
Sym p = TranspP (λ z → Id _ z _) p (Refl _)

module Singletons (A : SType) (a : STerm A) where

  singl : SType
  singl = SigmaU A (λ x → LiftP (Id A a x))

  point : STerm singl
  point = pair a (liftP (Refl a))

  private
    T : STerm A → Term P
    T x = PiP (Id A a x) λ e → Id singl (pair x (liftP e)) point

    T' : STerm A → Term P
    T' x = PiP (Id A a x) λ e → Id singl point (pair x (liftP e))
--    TranspP T' pf (lamP (λ e → Refl _)) $P pf

  contr : (p : STerm singl) → PTerm (Id singl point p)
  contr p = substP (λ z → PTerm (Id singl point (pair (fst p) z))) eq (Sym aux)
    where
      pf = unliftP (snd p)
      eq : liftP pf ≡ snd p
      eq = liftP-unliftP-≡ _ _
      aux = TranspP T pf (lamP (λ e → Refl _)) $P pf

  contr' : (p : STerm singl) → PTerm (Id singl point p)
  contr' p = substP (λ z → PTerm (Id singl point (pair (fst p) z))) eq aux
    where
      pf = unliftP (snd p)
      eq : liftP pf ≡ snd p
      eq = liftP-unliftP-≡ _ _
      aux = TranspP T' pf (lamP (λ e → Refl _)) $P pf

  -- contr'' : STerm (PiU singl λ p → LiftP (Id singl point p))
  -- contr'' = {!!}


module _ {A : SType} {x : STerm A}
         (C : (y : Term (El A)) → PTerm (Id A x y) → Type)
         (d : Term (C x (Refl _)))
         where

  open Singletons A x

  Id-J : {y : STerm A} (p : PTerm (Id A x y)) → Term (C y p)
  Id-J {y} p = aux
    where aux = Transp {A = singl} (λ q → C (fst q) (unliftP (snd q)))
                       {point} {pair y (liftP p)}
                       (contr (pair y (liftP p))) d

  Id-J-refl : Id-J (Refl x) ≡ d
  Id-J-refl = refl

module _ {A : Term U} {B : Term (El A) → Term P} where

  Id-Sigmap : {a a' : Term (El A)}
            → PTerm (Id A a a')
            → {b : PTerm (B a)} {b' : PTerm (B a')}
            → PTerm (Id (Sigmap A B) (pairp a b) (pairp a' b'))
  Id-Sigmap {a} {a'} p {b} {b'} =
    TranspP T p (lamP (λ _ → lamP (λ _ → Refl _))) $P b $P b'
    where
      T : Term (El A) → Term P
      T a' = PiP (B a) λ b → PiP (B a') λ b'
           → Id (Sigmap A B) (pairp a b) (pairp a' b')
