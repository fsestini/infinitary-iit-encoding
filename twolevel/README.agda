{-# OPTIONS --prop --rewriting #-}

-- Utilities
import lib

-- HOAS definition of target theory model
import hoas-postulated

---- IIT algebras --------------------------------------------------------------

-- Specification datatype for IITs
import IIT.spec

-- IIT algebras and displayed algebras
import IIT.algebra

-- Sections of IIT algebras
import IIT.section

---- Erased algebras -----------------------------------------------------------

-- Algebras and displayed algebras of erased types
import erased.algebra

-- Sections of erased algebras
import erased.section

---- Construction of section-inductive erased types ----------------------------

-- Internalization of erased algebras and specifications in the target theory
import erased.initial.internal-algebra

-- Theorems relating external and internal specifications and algebras
import erased.initial.erasure

-- Definition of erased types and proof of section induction
-- WARNING: this module relies a LOT on rewriting, and takes a long time to
--          typecheck. we thus leave it commented by default.
-- import erased.initial.embedded

-- Convenience redefinitions of erased algebras and sections targeting small
-- types
import erased.initial.algebra-small
import erased.initial.section-small

---- Predicate and relation algebras -------------------------------------------

-- Algebras of well-formedness predicates
import predicate.algebra

-- Construction of predicate types with inversions by induction on erased
-- algebras
import predicate.initial

-- Algebras of eliminator relations
import relation.algebra

-- Construction of relation types with inversions by induction on erased
-- algebras
import relation.initial

-- Σ-construction
import sigma-construction
