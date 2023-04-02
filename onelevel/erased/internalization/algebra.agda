{-# OPTIONS --prop --rewriting #-}

module erased.internalization.algebra where

open import lib
open import IIT.spec
open import erased.internalization.code

Spec₀-Alg₀ : Spec₀ -> Set i × Set i -> Set i
Ctor₀-Alg₀ : Ctor₀ -> Set i × Set i -> Set i
Params₀-Alg₀ : Params₀ -> Set i × Set i -> Set i
Ty₀-Alg₀ : Ty₀ -> Set i × Set i -> Set i
Base₀-Alg₀ : Base₀ -> Set i × Set i -> Set i

Spec₀-Alg₀ Γ X = ∀{C} → CtorTm₀ Γ C → Ctor₀-Alg₀ C X

Ctor₀-Alg₀ (Δ , A) x = Params₀-Alg₀ Δ x → Base₀-Alg₀ A x

Params₀-Alg₀ ●₀ x = ⊤
Params₀-Alg₀ (Δ ‣‣₀ A) x = Params₀-Alg₀ Δ x × Ty₀-Alg₀ A x

Ty₀-Alg₀ (ext₀ A) x = LiftSet (El A)
Ty₀-Alg₀ (base₀ b) x = Base₀-Alg₀ b x
Ty₀-Alg₀ (Π₀ A B) x = El A → Base₀-Alg₀ B x

Base₀-Alg₀ ty1₀ = proj₁
Base₀-Alg₀ ty2₀ = proj₂

CtorTm₀-Alg₀ : ∀{Γ C s} → CtorTm₀ Γ C → Spec₀-Alg₀ {i} Γ s → Ctor₀-Alg₀ C s
CtorTm₀-Alg₀ c γ = γ c

--------------------------------------------------------------------------------

DSets : Set i × Set i -> Set _
DSets {i} (A , B) = (A -> Set i) × (B -> Set i)

Spec₀-DAlg₀ : ∀ Γ {s} (γ : Spec₀-Alg₀ {i} Γ s) -> DSets s -> Set i
Ctor₀-DAlg₀ : ∀{s} (A : Ctor₀) -> DSets s -> Ctor₀-Alg₀ {i} A s -> Set i
Ty₀-DAlg₀ : ∀{s} (A : Ty₀) -> DSets s -> Ty₀-Alg₀ {i} A s -> Set i
Base₀-DAlg₀ : ∀{s} (A : Base₀) -> DSets s -> Base₀-Alg₀ {i} A s -> Set i
Params₀-DAlg₀ : ∀{s} (Δ : Params₀) -> DSets s -> Params₀-Alg₀ {i} Δ s -> Set i

Ctor₀-DAlg₀ (Δ , A) x f = {p : _} → Params₀-DAlg₀ Δ x p -> Base₀-DAlg₀ A x (f p)

Spec₀-DAlg₀ Γ γ Y = ∀ {C} (c : CtorTm₀ Γ C) → Ctor₀-DAlg₀ C Y (γ c)

Params₀-DAlg₀ ●₀ x h = ⊤
Params₀-DAlg₀ (Δ ‣‣₀ A) x (h , a) = Params₀-DAlg₀ Δ x h × Ty₀-DAlg₀ A x a

Base₀-DAlg₀ ty1₀ x a = proj₁ x a
Base₀-DAlg₀ ty2₀ x a = proj₂ x a

Ty₀-DAlg₀ (ext₀ A) x y = LiftSet (El A)
Ty₀-DAlg₀ (base₀ b) x y = Base₀-DAlg₀ b x y
Ty₀-DAlg₀ (Π₀ A B) x y = (n : El A) → Base₀-DAlg₀ B x (y n) 

CtorTm₀-DAlg : ∀{Γ C s ds} (c : CtorTm₀ Γ C)
               {γ : Spec₀-Alg₀ {i} Γ s} (δ : Spec₀-DAlg₀ Γ γ ds)
             → Ctor₀-DAlg₀ C ds (CtorTm₀-Alg₀ c γ)
CtorTm₀-DAlg c δ = δ c
