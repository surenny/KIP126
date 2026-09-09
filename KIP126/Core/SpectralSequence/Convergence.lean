import KIP126.Core.SpectralSequence.SpectralObjectAdapter
import KIP126.Core.Algebra.Completion.Basic
import Mathlib.Algebra.Homology.SpectralObject.FirstPage

/-!
# Endpoint data and spectral sequences of filtered complexes

Mathlib constructs a spectral sequence from an abelian spectral object indexed
by `EInt`.  A decreasing filtration, by contrast, is naturally indexed by
`OrderDual ℤ`.  This module makes the missing endpoint data explicit instead
of silently identifying an integer filtration level with either endpoint.

The construction below is deliberately conditional on an `EndpointExtension`:
the finite part is required to agree naturally with the filtered-complex
diagram, while the two endpoint objects and their maps are supplied by the
caller.  This is the appropriate trust boundary for convergence: completeness,
separatedness, and any comparison with an abutment are mathematical witnesses
to be provided by a concrete Adams or extension construction, not global
axioms and not consequences of an arbitrary filtration.
-/

namespace KIP126.Core.SpectralSequence

open CategoryTheory CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Embed the decreasing filtration index category in `EInt`.  The sign
reversal makes an arrow `s ⟶ t` (which means `t ≤ s` for the decreasing
filtration) into the ordinary `EInt` arrow `-s ⟶ -t`. -/
noncomputable def decreasingFiltrationEmbedding : OrderDual ℤ ⥤ EInt where
  obj s := ((-OrderDual.ofDual s : ℤ) : EInt)
  map f := homOfLE (by
    simp only [WithBotTop.coe_le_coe]
    exact neg_le_neg f.le)
  map_id s := by
    apply Subsingleton.elim
  map_comp f g := by
    apply Subsingleton.elim

/-- The endpoint extension required to turn a filtered-complex diagram into
an `EInt`-indexed diagram.  `finiteIso` is natural, so it also records the
compatibility of all finite filtration-inclusion maps, not merely an
objectwise identification. -/
structure EndpointExtension (FC : FilteredComplex C) where
  /-- The filtered diagram with explicit lower and upper endpoint objects. -/
  diagram : EInt ⥤ CochainComplex C ℤ
  /-- Its finite restriction agrees with the compiled decreasing-filtration
diagram. -/
  finiteIso : FC.filteredCochainDiagram ≅
    decreasingFiltrationEmbedding ⋙ diagram

namespace EndpointExtension

variable {FC : FilteredComplex C}
variable (P : EndpointExtension FC)

/-- The finite part of an endpoint extension, indexed with the same variance
as the decreasing filtration diagram. -/
noncomputable abbrev finiteDiagram : OrderDual ℤ ⥤ CochainComplex C ℤ :=
  decreasingFiltrationEmbedding ⋙ P.diagram

/-- The cone from the lower endpoint to the finite filtration diagram.  When
it is limiting, the lower endpoint represents the intersection/limit rather
than an arbitrarily chosen extra object. -/
noncomputable def bottomCone : Cone P.finiteDiagram where
  pt := P.diagram.obj ⊥
  π :=
    { app := fun _ => P.diagram.map (homOfLE (by simp))
      naturality := by
        intro s t f
        have h :
          P.diagram.map
              (homOfLE
                (show (⊥ : EInt) ≤ decreasingFiltrationEmbedding.obj t by simp)) =
            P.diagram.map
                (homOfLE
                  (show (⊥ : EInt) ≤ decreasingFiltrationEmbedding.obj s by simp)) ≫
              P.diagram.map (decreasingFiltrationEmbedding.map f) := by
          rw [← P.diagram.map_comp]
          congr 1
        have h' :
            𝟙 (P.diagram.obj ⊥) ≫
                P.diagram.map
                  (homOfLE
                    (show (⊥ : EInt) ≤ decreasingFiltrationEmbedding.obj t by simp)) =
              P.diagram.map
                  (homOfLE
                    (show (⊥ : EInt) ≤ decreasingFiltrationEmbedding.obj s by simp)) ≫
                P.diagram.map (decreasingFiltrationEmbedding.map f) := by
          simpa using h
        simpa only [finiteDiagram, Functor.comp, Functor.const] using h' }

/-- The cocone from the finite filtration diagram to the upper endpoint.  A
colimiting instance expresses exhaustiveness at the diagram level. -/
noncomputable def topCocone : Cocone P.finiteDiagram where
  pt := P.diagram.obj ⊤
  ι :=
    { app := fun _ => P.diagram.map (homOfLE (by simp))
      naturality := by
        intro s t f
        have h :
          P.diagram.map (decreasingFiltrationEmbedding.map f) ≫
              P.diagram.map
                (homOfLE
                  (show decreasingFiltrationEmbedding.obj t ≤ (⊤ : EInt) by simp)) =
            P.diagram.map
              (homOfLE
                (show decreasingFiltrationEmbedding.obj s ≤ (⊤ : EInt) by simp)) := by
          rw [← P.diagram.map_comp]
          congr 1
        have h' :
            P.diagram.map (decreasingFiltrationEmbedding.map f) ≫
                P.diagram.map
                  (homOfLE
                    (show decreasingFiltrationEmbedding.obj t ≤ (⊤ : EInt) by simp)) =
              P.diagram.map
                (homOfLE
                  (show decreasingFiltrationEmbedding.obj s ≤ (⊤ : EInt) by simp)) ≫
                𝟙 (P.diagram.obj ⊤) := by
          simpa using h
        simpa only [finiteDiagram, Functor.comp, Functor.const] using h' }

/-- Endpoint semantics for an `EndpointExtension`.  These are witnesses, not
properties inferred from arbitrary filtration data: the lower endpoint is a
limit, the upper endpoint is a colimit, and the two endpoint objects carry
their intended zero and abutment comparisons. -/
structure BoundaryWitness where
  /-- The lower endpoint is the limit of the finite restriction. -/
  bottomIsLimit : IsLimit P.bottomCone
  /-- The lower endpoint is zero after the limiting comparison. -/
  botIsZero : IsZero (P.diagram.obj ⊥)
  /-- The upper endpoint is the colimit of the finite restriction. -/
  topIsColimit : IsColimit P.topCocone
  /-- The intended abutment complex. -/
  top : CochainComplex C ℤ
  /-- The upper endpoint identifies with the intended abutment, without
equating it definitionally to any finite filtration level. -/
  topIso : P.diagram.obj ⊤ ≅ top

/-- A map of endpoint extensions lying over a filtered-complex morphism.
The compatibility square is stated after restricting the endpoint diagrams to
the finite filtration range; it therefore prevents endpoint-level functoriality
from losing the already-established finite filtration map.  This structure
deliberately concerns the raw endpoint diagrams only: preservation of chosen
`BoundaryWitness` or page/abutment comparison data is extra data for a
concrete convergence construction. -/
structure Hom {FC GD : FilteredComplex C}
    (P : EndpointExtension FC) (Q : EndpointExtension GD) (f : FC ⟶ GD) where
  /-- A natural transformation between the endpoint-extended diagrams. -/
  map : P.diagram ⟶ Q.diagram
  /-- On finite filtration levels, `map` agrees with the supplied filtered
complex morphism through the two extension identifications. -/
  finite_comm :
    P.finiteIso.hom ≫ Functor.whiskerLeft decreasingFiltrationEmbedding map =
      f.filteredCochainDiagramNatTrans ≫ Q.finiteIso.hom

/-- The identity map of an endpoint extension. -/
noncomputable def Hom.id {FC : FilteredComplex C}
    (P : EndpointExtension FC) : Hom P P (FilteredComplex.Morphism.id FC) where
  map := 𝟙 P.diagram
  finite_comm := by
    rw [show (FilteredComplex.Morphism.id FC).filteredCochainDiagramNatTrans =
        𝟙 FC.filteredCochainDiagram from
      (FilteredComplex.filteredCochainDiagramFunctor (C := C)).map_id FC]
    simp

/-- Compose maps of endpoint extensions.  The finite compatibility squares
compose because the filtered-diagram adapter is itself functorial. -/
noncomputable def Hom.comp
    {FC GD GE : FilteredComplex C}
    {P : EndpointExtension FC} {Q : EndpointExtension GD} {R : EndpointExtension GE}
    {f : FC ⟶ GD} {g : GD ⟶ GE}
    (h : Hom P Q f) (k : Hom Q R g) :
    Hom P R (FilteredComplex.Morphism.comp f g) where
  map := h.map ≫ k.map
  finite_comm := by
    rw [Functor.whiskerLeft_comp]
    rw [← Category.assoc, h.finite_comm, Category.assoc, k.finite_comm,
      ← Category.assoc]
    congr 1
    exact ((FilteredComplex.filteredCochainDiagramFunctor (C := C)).map_comp f g).symm

/-- Transport the lower endpoint cone across `finiteIso`, so its universal
property is stated directly on the filtered-complex diagram. -/
noncomputable def finiteBottomCone : Cone FC.filteredCochainDiagram :=
  (Cone.postcompose P.finiteIso.inv).obj P.bottomCone

/-- Transport the upper endpoint cocone across `finiteIso`, so its universal
property is stated directly on the filtered-complex diagram. -/
noncomputable def finiteTopCocone : Cocone FC.filteredCochainDiagram :=
  (Cocone.precompose P.finiteIso.hom).obj P.topCocone

/-- The lower endpoint remains limiting after identifying the finite
restriction with the original filtered-complex diagram. -/
noncomputable def finiteBottomIsLimit (W : P.BoundaryWitness) :
    IsLimit P.finiteBottomCone :=
  (IsLimit.postcomposeInvEquiv P.finiteIso P.bottomCone).symm W.bottomIsLimit

/-- The upper endpoint remains colimiting after identifying the finite
restriction with the original filtered-complex diagram. -/
noncomputable def finiteTopIsColimit (W : P.BoundaryWitness) :
    IsColimit P.finiteTopCocone :=
  (IsColimit.precomposeHomEquiv P.finiteIso P.topCocone).symm W.topIsColimit

/-- Apply the mapping-cone construction to the endpoint-extended diagram. -/
noncomputable def triangulatedSpectralObject :
    Triangulated.SpectralObject
      (HomotopyCategory C (ComplexShape.up ℤ)) EInt :=
  cochainDiagramTriangulatedSpectralObject P.diagram

/-- Apply a homological functor to the endpoint-extended spectral object. -/
noncomputable def abelianSpectralObject
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    Abelian.SpectralObject A EInt :=
  cochainDiagramHomologicalImage P.diagram A F

/-- The graded object obtained by applying each shifted component of a
homological functor to the upper endpoint.  A page/abutment comparison records
an explicit isomorphism to this object, so its named abutment is not detached
from the endpoint diagram. -/
noncomputable def endpointAbutment
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    CategoryTheory.GradedObject ℤ A :=
  fun n => (F.shift n).obj
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (P.diagram.obj ⊤))

/-- A map of endpoint extensions induces a map of the corresponding
triangulated spectral objects. -/
noncomputable def Hom.triangulatedSpectralObjectHom
    {FC GD : FilteredComplex C}
    {P : EndpointExtension FC} {Q : EndpointExtension GD} {f : FC ⟶ GD}
    (h : Hom P Q f) :
    P.triangulatedSpectralObject ⟶ Q.triangulatedSpectralObject :=
  cochainDiagramTriangulatedSpectralObjectHom h.map

/-- Applying a homological functor to a map of endpoint extensions gives a
map of abelian spectral objects.  Mathlib does not presently package this as
a morphism of its `E₂CohomologicalSpectralSequence` structure, so this is the
functoriality boundary exposed by this module. -/
noncomputable def Hom.abelianSpectralObjectHom
    {FC GD : FilteredComplex C}
    {P : EndpointExtension FC} {Q : EndpointExtension GD} {f : FC ⟶ GD}
    (h : Hom P Q f)
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    P.abelianSpectralObject A F ⟶ Q.abelianSpectralObject A F :=
  cochainDiagramHomologicalImageHom P.diagram Q.diagram h.map A F

/-- The canonical `E₂` cohomological spectral sequence supplied by Mathlib.
No project-local spectral-sequence record is introduced. -/
noncomputable def spectralSequence
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] :
    CategoryTheory.E₂CohomologicalSpectralSequence A :=
  (P.abelianSpectralObject A F).E₂SpectralSequence

/-- The first-page computation is Mathlib's exact-couple presentation for
the endpoint-extended spectral object. -/
noncomputable def firstPageXIso
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological]
    (p q : ℤ) :
    ((P.spectralSequence A F).page 2).X (p, q) ≅
      ((P.abelianSpectralObject A F).H (p + q)).obj
        (CategoryTheory.ComposableArrows.mk₁
          (homOfLE
            (Abelian.SpectralObject.coreE₂Cohomological.le₁₂ (p, q)))) :=
  (P.abelianSpectralObject A F).spectralSequenceFirstPageXIso
    Abelian.SpectralObject.coreE₂Cohomological (p, q)
    (q : EInt) ((q + 1 : ℤ) : EInt) rfl rfl (p + q) rfl

end EndpointExtension

/-- Explicit input for comparing pointwise selected pages of an endpoint-extended
spectral sequence with the associated graded of a complete, degreewise bounded
endpoint abutment filtration.  The record is deliberately narrower than a
strong convergence theorem: it stores one selected page for each bidegree, but
does not claim the additional page-passage coherence needed to construct a
canonical `E∞` object.

Completeness is proved from the canonical tower `Aᵢ / FˢAᵢ`, while the
boundedness field proves degreewise eventual-top and eventual-bottom
consequences.  These are stronger than ordinary exhaustiveness and
separatedness.
All of this remains explicit data for a concrete construction; it is not
inferred from an arbitrary filtered complex. -/
structure PageAbutmentComparisonWitness
    {FC : FilteredComplex C} (P : EndpointExtension FC) (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] where
  /-- The endpoint limit/colimit data for the diagram that produced the
spectral sequence. -/
  boundary : P.BoundaryWitness
  /-- The chosen graded abutment. -/
  abutment : CategoryTheory.GradedObject ℤ A
  /-- The chosen abutment is explicitly the shifted homological image of the
upper endpoint.  This keeps the associated-graded comparison connected to the
same endpoint data that supplied the boundary witnesses. -/
  endpointAbutmentIso : P.endpointAbutment A F ≅ abutment
  /-- Its decreasing filtration.  This is separate data because the filtration
on an abutment need not be definitionally the filtration on a chain complex. -/
  filtration : Algebra.Filtration abutment
  /-- Degreewise boundedness is the regularity hypothesis used here.  Its lower
and upper components imply degreewise eventual-top, eventual-bottom, and
canonical degreewise completion respectively. -/
  bounded : Algebra.Filtration.IsBounded filtration
  /-- Which abutment-filtration degree represents a page bidegree.  Keeping
this translation explicit prevents a hidden sign or page-index convention. -/
  filtrationDegree : ℤ × ℤ → ℤ
  /-- The page selected by the concrete comparison at each bidegree.  It is
intentionally bidegree-dependent; no uniform-page or page-passage coherence is
claimed by this witness. -/
  comparisonPage : ℤ × ℤ → ℤ
  comparisonPage_ge_two : ∀ pq, 2 ≤ comparisonPage pq
  /-- Each pointwise selected page is explicitly identified with the associated
graded piece of the chosen endpoint abutment. -/
  pageComparison : ∀ pq,
    ((P.spectralSequence A F).page (comparisonPage pq)
      (comparisonPage_ge_two pq)).X pq ≅
        filtration.associatedGraded (filtrationDegree pq) (pq.1 + pq.2)

namespace PageAbutmentComparisonWitness

variable {FC : FilteredComplex C} {P : EndpointExtension FC}
variable {A : Type*} [Category A] [Abelian A]
variable {F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A}
variable [F.ShiftSequence ℤ] [F.IsHomological]

/-- The bounded-above component of the regularity data supplies the canonical
degreewise completion witness. -/
noncomputable def completion (W : PageAbutmentComparisonWitness P A F) (n : ℤ) :
    Algebra.Filtration.CompletionWitness W.filtration n :=
  Algebra.Filtration.CompletionWitness.of_isBoundedAbove W.filtration
    W.bounded.toIsBoundedAbove n

/-- The bounded-below part of the witness makes the abutment filtration
degreewise eventually top (the project predicate named `IsExhaustive`). -/
lemma exhaustive (W : PageAbutmentComparisonWitness P A F) :
    W.filtration.IsExhaustive :=
  W.bounded.toIsBoundedBelow.isExhaustive

/-- The bounded-above part of the witness makes the abutment filtration
degreewise eventually bottom, which is stronger than separatedness. -/
lemma eventuallyZero (W : PageAbutmentComparisonWitness P A F) :
    W.filtration.IsEventuallyZero :=
  W.bounded.toIsBoundedAbove.isEventuallyZero

end PageAbutmentComparisonWitness

/-- Coherent strong-convergence data built on a pointwise page/abutment
comparison.  Mathlib deliberately has no distinguished `E∞` page, so the
limiting page is explicit data.  Every sufficiently late page is identified
with that object, the identifications commute with Mathlib's successor-page
isomorphisms, and the limiting page is identified with the associated graded
of the endpoint abutment filtration.

This interface adapts the convergence and detection proof pattern from
`KIP/SpectralSequence/Convergence.lean` at commit
`19a6a56c6c1e590dde850f33a18490b8f35e7d6e` to Mathlib's spectral-sequence
kernel and KIP126's explicit endpoint witnesses. -/
structure StrongConvergenceWitness
    {FC : FilteredComplex C} (P : EndpointExtension FC)
    (A : Type*) [Category A] [Abelian A]
    (F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A)
    [F.ShiftSequence ℤ] [F.IsHomological] where
  /-- The selected-page comparison and bounded endpoint data on which strong
  convergence is built. -/
  comparison : PageAbutmentComparisonWitness P A F
  /-- The coherent limiting page, indexed by spectral-sequence bidegree. -/
  eInfinity : CategoryTheory.GradedObject (ℤ × ℤ) A
  /-- Supplied identifications from stable-page homology to the stable-page
  object at the selected bidegree. -/
  pageHomologyIso : ∀ (pq : ℤ × ℤ) (r : ℤ)
      (hr : comparison.comparisonPage pq ≤ r),
    ((P.spectralSequence A F).page r
      ((comparison.comparisonPage_ge_two pq).trans hr)).homology pq ≅
        ((P.spectralSequence A F).page r
          ((comparison.comparisonPage_ge_two pq).trans hr)).X pq
  /-- Every page after the selected stable bound is identified with `E∞`. -/
  pageIso : ∀ (pq : ℤ × ℤ) (r : ℤ)
      (hr : comparison.comparisonPage pq ≤ r),
    ((P.spectralSequence A F).page r
      ((comparison.comparisonPage_ge_two pq).trans hr)).X pq ≅ eInfinity pq
  /-- The stable-page identifications commute with Mathlib's page passage. -/
  pagePassage_coherent : ∀ (pq : ℤ × ℤ) (r : ℤ)
      (hr : comparison.comparisonPage pq ≤ r),
    (pageHomologyIso pq r hr).inv ≫
        ((P.spectralSequence A F).iso r (r + 1) pq rfl
          ((comparison.comparisonPage_ge_two pq).trans hr)).hom ≫
      (pageIso pq (r + 1) (hr.trans (by omega))).hom =
        (pageIso pq r hr).hom
  /-- The limiting page is the associated graded of the chosen endpoint
  abutment filtration. -/
  eInfinityComparison : ∀ pq,
    eInfinity pq ≅ comparison.filtration.associatedGraded
      (comparison.filtrationDegree pq) (pq.1 + pq.2)
  /-- At the selected page, the coherent comparison recovers the original
  pointwise comparison. -/
  selectedPage_compat : ∀ pq,
    (pageIso pq (comparison.comparisonPage pq) le_rfl).hom ≫
        (eInfinityComparison pq).hom =
      (comparison.pageComparison pq).hom

namespace StrongConvergenceWitness

variable {FC : FilteredComplex C} {P : EndpointExtension FC}
variable {A : Type*} [Category A] [Abelian A]
variable {F : HomotopyCategory C (ComplexShape.up ℤ) ⥤ A}
variable [F.ShiftSequence ℤ] [F.IsHomological]

/-- The comparison from any stable page to the associated graded, factored
through the coherent limiting page. -/
noncomputable def pageComparison (W : StrongConvergenceWitness P A F)
    (pq : ℤ × ℤ) (r : ℤ) (hr : W.comparison.comparisonPage pq ≤ r) :
    ((P.spectralSequence A F).page r
      ((W.comparison.comparisonPage_ge_two pq).trans hr)).X pq ≅
        W.comparison.filtration.associatedGraded
          (W.comparison.filtrationDegree pq) (pq.1 + pq.2) :=
  (W.pageIso pq r hr).trans (W.eInfinityComparison pq)

/-- The stable-page comparisons with the associated graded commute with
Mathlib's successor-page isomorphisms. -/
@[simp]
lemma pagePassage_pageComparison (W : StrongConvergenceWitness P A F)
    (pq : ℤ × ℤ) (r : ℤ) (hr : W.comparison.comparisonPage pq ≤ r) :
    (W.pageHomologyIso pq r hr).inv ≫
        ((P.spectralSequence A F).iso r (r + 1) pq rfl
          ((W.comparison.comparisonPage_ge_two pq).trans hr)).hom ≫
      (W.pageComparison pq (r + 1) (hr.trans (by omega))).hom =
        (W.pageComparison pq r hr).hom := by
  simp only [pageComparison, Iso.trans_hom]
  simpa only [Category.assoc] using congrArg
    (fun q => q ≫ (W.eInfinityComparison pq).hom)
    (W.pagePassage_coherent pq r hr)

/-- The coherent stable-page comparison restricts to the selected pointwise
comparison stored by the underlying witness. -/
@[simp]
lemma pageComparison_selected (W : StrongConvergenceWitness P A F)
    (pq : ℤ × ℤ) :
    W.pageComparison pq (W.comparison.comparisonPage pq) le_rfl =
      W.comparison.pageComparison pq := by
  apply Iso.ext
  exact W.selectedPage_compat pq

/-- A limiting class detects a filtered generalized element when their images
agree in the associated graded piece selected by the bidegree.  Detection is
a relation: changing the filtered lift by the next filtration level does not
change the detected limiting class. -/
def Detects (W : StrongConvergenceWitness P A F)
    {T : A} {pq : ℤ × ℤ}
    (y : T ⟶ W.eInfinity pq)
    (x : T ⟶ Subobject.underlying.obj
      (W.comparison.filtration.F
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2))) : Prop :=
  y ≫ (W.eInfinityComparison pq).hom =
    x ≫ W.comparison.filtration.toAssociatedGraded
      (W.comparison.filtrationDegree pq) (pq.1 + pq.2)

/-- The zero limiting class detects exactly the generalized elements that
lift to the next filtration level. -/
theorem detect_zero (W : StrongConvergenceWitness P A F)
    {T : A} {pq : ℤ × ℤ}
    (x : T ⟶ Subobject.underlying.obj
      (W.comparison.filtration.F
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2))) :
    W.Detects (0 : T ⟶ W.eInfinity pq) x ↔
      ∃ x' : T ⟶ Subobject.underlying.obj
          (W.comparison.filtration.F
            (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2)),
        x' ≫ Subobject.ofLE
          (W.comparison.filtration.F
            (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2))
          (W.comparison.filtration.F
            (W.comparison.filtrationDegree pq) (pq.1 + pq.2))
          (W.comparison.filtration.decreasing
            (W.comparison.filtrationDegree pq) (pq.1 + pq.2)) = x := by
  simpa only [Detects, Limits.zero_comp, eq_comm] using
    W.comparison.filtration.comp_toAssociatedGraded_eq_zero_iff_lifts
      (W.comparison.filtrationDegree pq) (pq.1 + pq.2) x

/-- The conjunction that `y` detects both filtered generalized elements is
equivalent to `y` detecting `x` and the difference `x - x'` lifting through
the next filtration level.  Thus, assuming `y` detects `x`, it also detects
`x'` exactly when that difference lifts. -/
theorem detect_difference (W : StrongConvergenceWitness P A F)
    {T : A} {pq : ℤ × ℤ}
    (y : T ⟶ W.eInfinity pq)
    (x x' : T ⟶ Subobject.underlying.obj
      (W.comparison.filtration.F
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2))) :
    (W.Detects y x ∧ W.Detects y x') ↔
      (W.Detects y x ∧
        ∃ z : T ⟶ Subobject.underlying.obj
            (W.comparison.filtration.F
              (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2)),
          z ≫ Subobject.ofLE
            (W.comparison.filtration.F
              (W.comparison.filtrationDegree pq + 1) (pq.1 + pq.2))
            (W.comparison.filtration.F
              (W.comparison.filtrationDegree pq) (pq.1 + pq.2))
            (W.comparison.filtration.decreasing
              (W.comparison.filtrationDegree pq) (pq.1 + pq.2)) = x - x') := by
  constructor
  · rintro ⟨hx, hx'⟩
    refine ⟨hx, (W.comparison.filtration.comp_toAssociatedGraded_eq_iff_sub_lifts
      (W.comparison.filtrationDegree pq) (pq.1 + pq.2) x x').mp ?_⟩
    rw [Detects] at hx hx'
    exact hx.symm.trans hx'
  · rintro ⟨hx, hlift⟩
    refine ⟨hx, ?_⟩
    rw [Detects] at hx ⊢
    exact hx.trans
      ((W.comparison.filtration.comp_toAssociatedGraded_eq_iff_sub_lifts
        (W.comparison.filtrationDegree pq) (pq.1 + pq.2) x x').mpr hlift)

end StrongConvergenceWitness

end KIP126.Core.SpectralSequence
