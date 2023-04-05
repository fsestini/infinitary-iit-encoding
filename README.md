# infinitary-iit-encoding

Agda formalization of a method to reduce (linear) infinitary inductive-inductive
types to inductive families. Despite the infinitary nature of the target class
of IITs, the method does not require principles like function/propositional
extensionality or equality reflection in the type theory where the encoding
takes place.

This code formalizes the second half of my PhD thesis (link coming soon), which
contains the theoretical background, detailed explanation, and pen-and-paper
counterpart to the proofs presented here. While the Agda code is
mostly complete w.r.t. the proofs on paper, there are still a few portions
that need to be added or reworked.

### Metatheory and target theory

The reduction is established as a metatheorem about intensional type theory, and
therefore takes place over two type-theoretic languages: the *target theory*
(i.e. the theory *about which* we are proving our metatheorems) and the ambient
*metatheory* (i.e. the overall language that we use to state and prove those
metatheorems).

Mechanized metatheory across two different languages can be challenging
(although Agda's rewriting facility helps quite a bit with that).  We thus
distribute the formalization in two variants: 

* a `onelevel` variant where the metatheory and target theory are collapsed into
one language, represented by Agda itself;
* a `twolevel` variant, where we use postulates and rewriting rules to construct
  a shallow HOAS embedding of the target theory into Agda, which now acts purely
  as the metatheory.

The two formalizations are mostly feature-equivalent, with the `twolevel`
variant acting as an additional "sanity-check" for the `onelevel`.

### Tooling

The project has been typechecked with Agda version 2.6.2, and a checkout of the
Agda standard library at commit `393c57a63b10400cfc93482c9ea21d529229ef2e`.
