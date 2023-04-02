{-# OPTIONS --prop --rewriting #-}

-- Library functions, basic type formers, equality, etc.
import lib

-- Specification datatype
import IIT.spec

-- Algebras and displayed algebras of IITs
import IIT.algebra

-- Sections of IIT algebras
import IIT.section

-- Algebras and displayed algebras of erased types
import erased.algebra

-- Sections of erased algebras
import erased.section

-- Algebras of well-formedness predicates
import predicate.algebra

-- Inversion principles for well-formedness predicates
import predicate.inversions

-- Σ-construction
import sigma-construction

-- Algebras of eliminator relations
import relation.algebra

-- Utility functions for defining the eliminators
import eliminator.lib

-- Definition of the eliminators and proof that they form a IIT section
import eliminator.eliminator
