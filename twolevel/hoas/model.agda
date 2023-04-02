{-# OPTIONS --prop --rewriting #-}

module hoas.model where

open import lib -- renaming (ΣP to lib-ΣP)

import hoas.internal as W

Type : Set
Type = W.𝕌

Term : Type → Set
Term = W.Tm

U : Type
U = W.Ucode

El : Term U → Type
El (W.mkTm x) = {!!}
-- W.mkT (W.El ∣ x ∣Tm)
