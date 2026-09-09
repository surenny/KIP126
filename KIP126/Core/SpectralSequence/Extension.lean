import KIP126.Core.SpectralSequence.FilteredComplex
import KIP126.Core.Algebra.Completion.Basic

/-!
# Bounded extension spectral sequences

This module records the bounded two-term filtered-complex data used by an
extension spectral sequence.  The construction follows ESS-compile's
`Truncation.lean` (commit `11b9ad8`) and KIP-infra's `BoundedExtension.lean`
(commit `65de864`), translated to the canonical KIP126 `FilteredComplex` API.
The corresponding Blueprint source is
`blueprint/src/chapters/extension_spectral_sequences.tex`, node
`def:filtered-two-term-complex`; endpoint and convergence witnesses are kept
in the existing endpoint module rather than duplicated here.
-/

namespace KIP126.Core.SpectralSequence.BoundedExtension

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [CategoryTheory.Category.{v} C] [Abelian C]

/-- Data for a bounded two-term extension at one graded stem.

The filtered complex is the canonical computational object.  The `two_term`
field records that no other chain degree contributes; endpoint and convergence
witnesses are supplied by the existing endpoint/convergence APIs when a
downstream construction needs them. -/
structure TwoTermData where
  complex : FilteredComplex C
  two_term : ∀ k : ℤ, k ≠ 1 → k ≠ 0 → CategoryTheory.Limits.IsZero (complex.complex.X k)

end KIP126.Core.SpectralSequence.BoundedExtension
