import KIP126.Core.SpectralSequence.Basic
import KIP126.Core.SpectralSequence.PageLevel
import KIP126.Core.Algebra.Completion.Basic
import KIP126.Core.Algebra.Coefficients
import KIP126.External.Claims
import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The first classical Adams slice

This file keeps the generic spectral-sequence object at Mathlib's
`CategoryTheory.SpectralSequence`.  The additional structures are only the
small amount of typed Adams data needed by the first `d₂` regression.
-/

namespace KIP126.Classical.Adams

open CategoryTheory
open KIP126.External
open KIP126.Core.Algebra
open KIP126.Core.SpectralSequence

abbrev Bidegree := ℤ × ℤ

/-- The AIM classical Adams differential degree. -/
def classicalAdamsShift (r : ℕ) : Bidegree := (r, (r : ℤ) - 1)

/-- The target bidegree of a page-`r` classical Adams differential. -/
def classicalAdamsTarget (r : ℕ) (b : Bidegree) : Bidegree :=
  b + classicalAdamsShift r

def classicalAdamsPageLevel : PageLevelConvention where
  firstPage := 2
  admissibleFrom := 2
  page := fun r => r
  cycleLevel := fun r => r - 1
  quotientExponent := fun r => r - 1
  page_first := by norm_num
  page_succ := by intro r; norm_num
  cycle_succ := by intro r; omega
  quotient_succ := by intro r; omega
  cycleLevel_eq_quotientExponent := by intro r; rfl

@[simp] theorem classicalAdamsShift_two :
    classicalAdamsShift 2 = (2, 1) := by
  norm_num [classicalAdamsShift]

@[simp] theorem classicalAdamsTarget_two (b : Bidegree) :
    classicalAdamsTarget 2 b = (b.1 + 2, b.2 + 1) := by
  apply Prod.ext <;> simp [classicalAdamsTarget, classicalAdamsShift]

/-- The pagewise complex shape used by the classical Adams sequence. -/
def classicalAdamsShape (r : ℤ) : ComplexShape Bidegree :=
  ComplexShape.up' (r, r - 1)

@[simp] theorem classicalAdamsShape_two_rel (b : Bidegree) :
    (classicalAdamsShape 2).Rel b (classicalAdamsTarget 2 b) := by
  simp [classicalAdamsShape, classicalAdamsTarget, classicalAdamsShift]

/-- A mod-2 classical Adams spectral sequence, with the differential shape
fixed to `(r,r-1)` and displayed from `E₂`. -/
abbrev ClassicalAdamsSpectralSequence :=
  CategoryTheory.SpectralSequence F2ModuleCat classicalAdamsShape 2

/-! ### Stable-homotopy and page interfaces -/

/-- The stable-homotopy operations used by the domain layer.  No homotopy
groups or multiplication are assumed here. -/
structure StableHomotopyContext where
  Spectrum : Type
  sphere : Spectrum
  smash : Spectrum → Spectrum → Spectrum

/-- Explicit convergence data for a chosen Adams sequence. The propositions
are witnesses supplied by a concrete construction, not global assumptions. -/
structure ClassicalAdamsConvergence (E : ClassicalAdamsSpectralSequence) where
  abutment : CategoryTheory.GradedObject Bidegree F2ModuleCat
  filtration : KIP126.Core.Algebra.Filtration abutment
  filtrationDegree : Bidegree → ℤ
  comparisonPage : Bidegree → ℤ
  comparisonPage_ge_two : ∀ b, 2 ≤ comparisonPage b
  pageComparison : ∀ b,
    (E.page (comparisonPage b) (comparisonPage_ge_two b)).X b ≅
      filtration.associatedGraded (filtrationDegree b) b
  complete : ∀ b, KIP126.Core.Algebra.Filtration.CompletionWitness filtration b
  /-- The strong degreewise eventual-top predicate named `IsExhaustive`. -/
  exhaustive : filtration.IsExhaustive
  /-- Degreewise eventual-bottom, stronger than separatedness. -/
  eventuallyZero : filtration.IsEventuallyZero

/-- A chosen classical Adams sequence for one spectrum. -/
structure ClassicalAdamsSS (stable : StableHomotopyContext)
    (X : stable.Spectrum) where
  sequence : ClassicalAdamsSpectralSequence
  convergence : ClassicalAdamsConvergence sequence

/-- The stem represented by an Adams bidegree `(s,t)`. -/
def adamsStem (b : Bidegree) : ℤ := b.2 - b.1

/-- The underlying additive group of one component of a classical Adams page. -/
abbrev UnderlyingAdamsPage (E : ClassicalAdamsSpectralSequence) (r : ℤ)
    (hr : 2 ≤ r) (b : Bidegree) : AddCommGrpCat :=
  (forget₂ F2ModuleCat AddCommGrpCat).obj ((E.page r hr).X b)

/-- The `2`-complete stable homotopy groups attached to every spectrum in a
chosen stable-homotopy context. -/
structure TwoCompleteStableHomotopy (stable : StableHomotopyContext) where
  groups : stable.Spectrum → CategoryTheory.GradedObject ℤ AddCommGrpCat

/-- A decreasing filtration is separated when its only subobject contained
in every filtration level is zero.  Unlike eventual vanishing, this permits
the genuine infinite Adams filtration in stem zero. -/
def IsAdamsFiltrationSeparated
    {G : CategoryTheory.GradedObject ℤ AddCommGrpCat}
    (F : KIP126.Core.Algebra.Filtration G) : Prop :=
  ∀ n (S : Subobject (G n)), (∀ s, S ≤ F.F s n) → S = ⊥

theorem isAdamsFiltrationSeparated_of_eventuallyZero
    {G : CategoryTheory.GradedObject ℤ AddCommGrpCat}
    (F : KIP126.Core.Algebra.Filtration G)
    (hF : F.IsEventuallyZero) :
    IsAdamsFiltrationSeparated F := by
  intro n S hS
  obtain ⟨s, hs⟩ := hF n
  apply le_antisymm
  · have h := hS s
    rw [hs] at h
    exact h
  · exact bot_le

/-- Strong convergence data for the Adams sequence of the specified spectrum.
Every page after `stablePage b` is identified with the associated graded of
the `2`-complete stable homotopy of that same spectrum, and the identifications
commute with Mathlib's page-passage isomorphisms. -/
structure StrongClassicalAdamsConvergence {stable : StableHomotopyContext}
    (π₂ : TwoCompleteStableHomotopy stable) (X : stable.Spectrum)
    (E : ClassicalAdamsSpectralSequence) where
  filtration : KIP126.Core.Algebra.Filtration (π₂.groups X)
  stablePage : Bidegree → ℤ
  stablePage_ge_two : ∀ b, 2 ≤ stablePage b
  pageHomologyIso : ∀ (b : Bidegree) (r : ℤ) (hr : stablePage b ≤ r),
    (E.page r ((stablePage_ge_two b).trans hr)).homology b ≅
      (E.page r ((stablePage_ge_two b).trans hr)).X b
  pageComparison : ∀ (b : Bidegree) (r : ℤ) (hr : stablePage b ≤ r),
    UnderlyingAdamsPage E r ((stablePage_ge_two b).trans hr) b ≅
      filtration.associatedGraded b.1 (adamsStem b)
  pagePassage_coherent : ∀ (b : Bidegree) (r : ℤ) (hr : stablePage b ≤ r),
    (forget₂ F2ModuleCat AddCommGrpCat).map
        (pageHomologyIso b r hr).inv ≫
      (forget₂ F2ModuleCat AddCommGrpCat).map
        (E.iso r (r + 1) b rfl ((stablePage_ge_two b).trans hr)).hom ≫
      (pageComparison b (r + 1) (hr.trans (by omega))).hom =
        (pageComparison b r hr).hom
  complete : ∀ n,
    KIP126.Core.Algebra.Filtration.CompletionWitness filtration n
  /-- The strong degreewise eventual-top predicate named `IsExhaustive`. -/
  exhaustive : filtration.IsExhaustive
  separated : IsAdamsFiltrationSeparated filtration

/-- A classical Adams slice whose strong-convergence data is bound to the
specified spectrum.  The extra convergence field prevents reusing the same
value at an unrelated spectrum even though the legacy page-only slice is
retained for API compatibility. -/
structure SpectrumBoundClassicalAdamsSS {stable : StableHomotopyContext}
    (π₂ : TwoCompleteStableHomotopy stable) (X : stable.Spectrum) where
  pageSlice : ClassicalAdamsSS stable X
  strongConvergence :
    StrongClassicalAdamsConvergence π₂ X pageSlice.sequence

namespace ClassicalAdamsSS

variable {stable : StableHomotopyContext} {X : stable.Spectrum}

/-- The first two displayed pages of a chosen Adams sequence. -/
def E₂ (A : ClassicalAdamsSS stable X) := A.sequence.page 2
def E₃ (A : ClassicalAdamsSS stable X) := A.sequence.page 3

/-- Mathlib's page-passage isomorphism for the `E₂ → E₃` slice. -/
def e₂ToE₃ (A : ClassicalAdamsSS stable X) (b : Bidegree) :
    (A.E₂).homology b ≅ (A.E₃).X b :=
  A.sequence.iso 2 3 b rfl (by norm_num)

/-- The actual page-2 differential component at the Adams target degree. -/
def d₂ (A : ClassicalAdamsSS stable X) (b : Bidegree) :
    (A.E₂).X b ⟶ (A.E₂).X (classicalAdamsTarget 2 b) :=
  (A.E₂).d b (classicalAdamsTarget 2 b)

theorem d₂_shape (_A : ClassicalAdamsSS stable X) (b : Bidegree) :
    (classicalAdamsShape 2).Rel b (classicalAdamsTarget 2 b) :=
  classicalAdamsShape_two_rel b

end ClassicalAdamsSS

/-- A named page-2 class, retaining its representative in the Mathlib page. -/
structure AdamsClass {stable : StableHomotopyContext} {X : stable.Spectrum}
    (A : ClassicalAdamsSS stable X) where
  name : String
  degree : Bidegree
  representative : (A.E₂).X degree

def transportRepresentative {stable : StableHomotopyContext}
    {X : stable.Spectrum} {A : ClassicalAdamsSS stable X}
    (x : AdamsClass A) {degree : Bidegree} (h : x.degree = degree) :
    (A.E₂).X degree :=
  (eqToHom (congrArg (fun b => (A.E₂).X b) h)).hom x.representative

/-- Transport a page element along an equality of Adams bidegrees. -/
def transportPageElement {stable : StableHomotopyContext}
    {X : stable.Spectrum} (A : ClassicalAdamsSS stable X)
    {source target : Bidegree} (h : source = target)
    (x : (A.E₂).X source) : (A.E₂).X target :=
  (eqToHom (congrArg (fun b => (A.E₂).X b) h)).hom x

/-! ### Sphere multiplication versus general external pairings -/

/-- Explicit internal product data for the sphere Adams page only. -/
structure SphereAdamsMultiplication {stable : StableHomotopyContext}
    (A : ClassicalAdamsSS stable stable.sphere) where
  product : AdamsClass A → AdamsClass A → AdamsClass A
  product_degree : ∀ x y, (product x y).degree = x.degree + y.degree

/-- The standard named sphere classes, supplied together with their page
representatives by the caller. -/
structure SphereAdamsPresentation {stable : StableHomotopyContext}
    (A : ClassicalAdamsSS stable stable.sphere) where
  h : ℕ → AdamsClass A
  h_degree : ∀ j, (h j).degree = (1, (2 : ℤ) ^ j)
  multiplication : SphereAdamsMultiplication A

def sphereProduct {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A) (x y : AdamsClass A) : AdamsClass A :=
  P.multiplication.product x y

/-- Algebraic laws for a chosen sphere presentation.  The product on named
classes is required to be represented by a bilinear, unital, associative
product on the actual Mathlib `E₂` page and to satisfy the page-`2` Leibniz
rule.  The named generators and the `h₀h₃²` target are explicitly nonzero. -/
structure SphereAdamsAlgebraPresentation {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A) where
  productMap : ∀ a b : Bidegree,
    (A.E₂).X a →ₗ[F2] (A.E₂).X b →ₗ[F2] (A.E₂).X (a + b)
  product_representation : ∀ x y,
    transportRepresentative (sphereProduct P x y)
        (P.multiplication.product_degree x y) =
      productMap x.degree y.degree x.representative y.representative
  unit : (A.E₂).X (0, 0)
  unit_left : ∀ (b : Bidegree) (x : (A.E₂).X b),
    transportPageElement A (by simp : (0, 0) + b = b)
        (productMap (0, 0) b unit x) = x
  unit_right : ∀ (a : Bidegree) (x : (A.E₂).X a),
    transportPageElement A (by simp : a + (0, 0) = a)
        (productMap a (0, 0) x unit) = x
  product_assoc : ∀ (a b c : Bidegree) (x : (A.E₂).X a)
      (y : (A.E₂).X b) (z : (A.E₂).X c),
    transportPageElement A (add_assoc a b c)
        (productMap (a + b) c (productMap a b x y) z) =
      productMap a (b + c) x (productMap b c y z)
  d₂_leibniz : ∀ (a b : Bidegree) (x : (A.E₂).X a) (y : (A.E₂).X b),
    (A.d₂ (a + b)).hom (productMap a b x y) =
      transportPageElement A
          (by
            apply Prod.ext <;>
              simp [classicalAdamsTarget, classicalAdamsShift, add_assoc,
                add_comm, add_left_comm] :
            classicalAdamsTarget 2 a + b = classicalAdamsTarget 2 (a + b))
          (productMap (classicalAdamsTarget 2 a) b ((A.d₂ a).hom x) y) +
        transportPageElement A
          (by
            apply Prod.ext <;>
              simp [classicalAdamsTarget, classicalAdamsShift, add_assoc] :
            a + classicalAdamsTarget 2 b = classicalAdamsTarget 2 (a + b))
          (productMap a (classicalAdamsTarget 2 b) x ((A.d₂ b).hom y))
  h_nonzero : ∀ j, (P.h j).representative ≠ 0
  h₀h₃Squared_nonzero :
    (sphereProduct P (P.h 0) (sphereProduct P (P.h 3) (P.h 3))).representative ≠ 0

/-- An external page pairing for arbitrary spectra.  Its target is the chosen
smash spectrum, not either input, so it does not assert an internal product. -/
structure ExternalAdamsPairing {stable : StableHomotopyContext}
    {X Y : stable.Spectrum} (AX : ClassicalAdamsSS stable X)
    (AY : ClassicalAdamsSS stable Y)
    (AZ : ClassicalAdamsSS stable (stable.smash X Y)) where
  pair : AdamsClass AX → AdamsClass AY → AdamsClass AZ
  pair_degree : ∀ x y, (pair x y).degree = x.degree + y.degree

/-- Bilinearity and Leibniz compatibility for an external Adams pairing. -/
structure ExternalAdamsPairingLaws {stable : StableHomotopyContext}
    {X Y : stable.Spectrum} {AX : ClassicalAdamsSS stable X}
    {AY : ClassicalAdamsSS stable Y}
    {AZ : ClassicalAdamsSS stable (stable.smash X Y)}
    (pairing : ExternalAdamsPairing AX AY AZ) where
  pairMap : ∀ a b : Bidegree,
    (AX.E₂).X a →ₗ[F2] (AY.E₂).X b →ₗ[F2] (AZ.E₂).X (a + b)
  pair_representation : ∀ x y,
    transportRepresentative (pairing.pair x y) (pairing.pair_degree x y) =
      pairMap x.degree y.degree x.representative y.representative
  d₂_leibniz : ∀ (a b : Bidegree) (x : (AX.E₂).X a) (y : (AY.E₂).X b),
    (AZ.d₂ (a + b)).hom (pairMap a b x y) =
      transportPageElement AZ
          (by
            apply Prod.ext <;>
              simp [classicalAdamsTarget, classicalAdamsShift, add_assoc,
                add_comm, add_left_comm] :
            classicalAdamsTarget 2 a + b = classicalAdamsTarget 2 (a + b))
          (pairMap (classicalAdamsTarget 2 a) b ((AX.d₂ a).hom x) y) +
        transportPageElement AZ
          (by
            apply Prod.ext <;>
              simp [classicalAdamsTarget, classicalAdamsShift, add_assoc] :
            a + classicalAdamsTarget 2 b = classicalAdamsTarget 2 (a + b))
          (pairMap a (classicalAdamsTarget 2 b) x ((AY.d₂ b).hom y))

/-- The sphere page acts on the page of an arbitrary spectrum.  This is kept
separate from `SphereAdamsMultiplication`, so a general Adams sequence gains no
internal multiplication by mere parametrisation. -/
structure SphereAdamsModule {stable : StableHomotopyContext}
    {X : stable.Spectrum} (sphere : ClassicalAdamsSS stable stable.sphere)
    (target : ClassicalAdamsSS stable X) where
  action : AdamsClass sphere → AdamsClass target → AdamsClass target
  action_degree : ∀ x y, (action x y).degree = x.degree + y.degree

/-- A lawful module action of the sphere Adams algebra on a target Adams
page.  Its action is bilinear on representatives, unital, and associative
with the sphere product. -/
structure SphereAdamsModuleLaws {stable : StableHomotopyContext}
    {X : stable.Spectrum} {sphere : ClassicalAdamsSS stable stable.sphere}
    {target : ClassicalAdamsSS stable X}
    {P : SphereAdamsPresentation sphere}
    (algebra : SphereAdamsAlgebraPresentation P)
    (module : SphereAdamsModule sphere target) where
  actionMap : ∀ a b : Bidegree,
    (sphere.E₂).X a →ₗ[F2] (target.E₂).X b →ₗ[F2]
      (target.E₂).X (a + b)
  action_representation : ∀ x y,
    transportRepresentative (module.action x y) (module.action_degree x y) =
      actionMap x.degree y.degree x.representative y.representative
  unit_action : ∀ (b : Bidegree) (x : (target.E₂).X b),
    transportPageElement target (by simp : (0, 0) + b = b)
        (actionMap (0, 0) b algebra.unit x) = x
  action_assoc : ∀ (a b c : Bidegree) (x : (sphere.E₂).X a)
      (y : (sphere.E₂).X b) (z : (target.E₂).X c),
    transportPageElement target (add_assoc a b c)
        (actionMap (a + b) c (algebra.productMap a b x y) z) =
      actionMap a (b + c) x (actionMap b c y z)

/-- The sphere's internal multiplication is the external sphere pairing after
an explicit identification of the smash-square page with the sphere page. -/
structure SphereAdamsExternalCompatibility {stable : StableHomotopyContext}
    {sphere : ClassicalAdamsSS stable stable.sphere}
    {smashSphere : ClassicalAdamsSS stable
      (stable.smash stable.sphere stable.sphere)}
    {P : SphereAdamsPresentation sphere}
    (algebra : SphereAdamsAlgebraPresentation P)
    (pairing : ExternalAdamsPairing sphere sphere smashSphere)
    (pairingLaws : ExternalAdamsPairingLaws pairing) where
  smashToSphere : ∀ b : Bidegree,
    (smashSphere.E₂).X b ≅ (sphere.E₂).X b
  product_eq_external : ∀ (a b : Bidegree) (x : (sphere.E₂).X a)
      (y : (sphere.E₂).X b),
    algebra.productMap a b x y =
      (smashToSphere (a + b)).hom (pairingLaws.pairMap a b x y)

/-! ### The h₄ regression relation -/

/-- A page-2 differential relation whose map is the actual Mathlib page
differential component. -/
structure AdamsD₂Statement {stable : StableHomotopyContext}
    {X : stable.Spectrum} (A : ClassicalAdamsSS stable X) where
  source : AdamsClass A
  target : AdamsClass A
  target_degree : target.degree = classicalAdamsTarget 2 source.degree
  representative_relation :
    (A.d₂ source.degree).hom source.representative =
      transportRepresentative target
        (degree := classicalAdamsTarget 2 source.degree) target_degree

variable {stable : StableHomotopyContext}
  {A : ClassicalAdamsSS stable stable.sphere}

def h₄D₂ (P : SphereAdamsPresentation A) : Prop :=
  ∃ statement : AdamsD₂Statement A,
    statement.source = P.h 4 ∧
      statement.target = sphereProduct P (P.h 0)
        (sphereProduct P (P.h 3) (P.h 3))

structure H₄D₂BoundData {π₂ : TwoCompleteStableHomotopy stable}
    (system : SpectrumBoundClassicalAdamsSS π₂ stable.sphere)
    (P : SphereAdamsPresentation system.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P) where
  strongConvergence : StrongClassicalAdamsConvergence π₂ stable.sphere
    system.pageSlice.sequence
  strongConvergence_eq : strongConvergence = system.strongConvergence
  lawfulAlgebra : SphereAdamsAlgebraPresentation P
  lawfulAlgebra_eq : lawfulAlgebra = algebra
  statement : ∃ statement : AdamsD₂Statement system.pageSlice,
      statement.source = P.h 4 ∧
        statement.target = sphereProduct P (P.h 0)
          (sphereProduct P (P.h 3) (P.h 3)) ∧
        statement.source.degree = (1, 16) ∧
        statement.target.degree = (3, 17)

def H₄D₂Bound {π₂ : TwoCompleteStableHomotopy stable}
    (system : SpectrumBoundClassicalAdamsSS π₂ stable.sphere)
    (P : SphereAdamsPresentation system.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P) : Prop :=
  Nonempty (H₄D₂BoundData system P algebra)

end KIP126.Classical.Adams

namespace KIP126.Classical

/-- The source-backed one-line input used by this slice. Its h₄ instance is
the `j=4` specialization of the located classical one-line calculation. -/
def adamsOneLineDifferentials {stable : Adams.StableHomotopyContext}
    {A : Adams.ClassicalAdamsSS stable stable.sphere}
    (P : Adams.SphereAdamsPresentation A) : Prop :=
  Adams.h₄D₂ P

theorem adamsOneLineDifferentials_h₄ {stable : Adams.StableHomotopyContext}
    {A : Adams.ClassicalAdamsSS stable stable.sphere}
    (P : Adams.SphereAdamsPresentation A) :
    adamsOneLineDifferentials P ↔ Adams.h₄D₂ P := Iff.rfl

theorem adamsOneLineDifferentials_h₄_degrees
    {stable : Adams.StableHomotopyContext}
    {A : Adams.ClassicalAdamsSS stable stable.sphere}
    (P : Adams.SphereAdamsPresentation A)
    (proof : adamsOneLineDifferentials P) :
    ∃ statement : Adams.AdamsD₂Statement A,
      statement.source = P.h 4 ∧
        statement.target = Adams.sphereProduct P (P.h 0)
          (Adams.sphereProduct P (P.h 3) (P.h 3)) ∧
        statement.source.degree = (1, 16) ∧
        statement.target.degree = (3, 17) := by
  obtain ⟨statement, hSource, hTarget⟩ := proof
  refine ⟨statement, hSource, hTarget, ?_, ?_⟩
  · rw [hSource, P.h_degree]
    norm_num
  · rw [statement.target_degree, hSource, P.h_degree]
    norm_num [Adams.classicalAdamsTarget, Adams.classicalAdamsShift]

end KIP126.Classical

namespace KIP126.Classical.Adams

private def adamsOneLineResult {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A)
    (proof : KIP126.Classical.adamsOneLineDifferentials P) :
  KIP126.External.ExternalResult (KIP126.Classical.adamsOneLineDifferentials P) :=
  { proof := proof
    ref := (KIP126.External.externalClaimLedger.lookup
      .adamsOneLine).ref }

def cataloguedAdamsOneLine (P : SphereAdamsPresentation A)
    (proof : KIP126.Classical.adamsOneLineDifferentials P) :
    KIP126.External.CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P) :=
  { root := .adamsOneLine
    value := adamsOneLineResult P proof
    ref_eq := by rfl
    class_supported := by trivial }

/-- Consume a located one-line result.  Unlike `cataloguedAdamsOneLine`, this
direction starts from a catalogue value and extracts its supplied theorem. -/
theorem cataloguedAdamsOneLine_proof (P : SphereAdamsPresentation A)
    (input : KIP126.External.CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P)) :
    KIP126.Classical.adamsOneLineDifferentials P :=
  input.value.proof

/-- The h₄ degree calculation obtained by consuming the located external
result rather than asking the caller for an unlabelled proof. -/
theorem cataloguedAdamsOneLine_h₄_degrees (P : SphereAdamsPresentation A)
    (input : KIP126.External.CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P)) :
    ∃ statement : AdamsD₂Statement A,
      statement.source = P.h 4 ∧
        statement.target = sphereProduct P (P.h 0)
          (sphereProduct P (P.h 3) (P.h 3)) ∧
        statement.source.degree = (1, 16) ∧
        statement.target.degree = (3, 17) :=
  KIP126.Classical.adamsOneLineDifferentials_h₄_degrees P
    (cataloguedAdamsOneLine_proof P input)

structure AdamsOneLineCatalogue {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A) where
  value : KIP126.External.ExternalResult
    (KIP126.Classical.adamsOneLineDifferentials P)
  ref_eq : value.ref =
    (KIP126.External.externalClaimLedger.lookup .adamsOneLine).ref

def cataloguedAdamsOneLineCanonical
    {stable : StableHomotopyContext}
    {A : ClassicalAdamsSS stable stable.sphere}
    (P : SphereAdamsPresentation A)
    (proof : KIP126.Classical.adamsOneLineDifferentials P) :
    AdamsOneLineCatalogue P :=
  { value := adamsOneLineResult P proof
    ref_eq := rfl }

theorem cataloguedAdamsOneLine_h₄_degrees_bound
    {stable : StableHomotopyContext}
    {π₂ : TwoCompleteStableHomotopy stable}
    (system : SpectrumBoundClassicalAdamsSS π₂ stable.sphere)
    (P : SphereAdamsPresentation system.pageSlice)
    (algebra : SphereAdamsAlgebraPresentation P)
    (input : AdamsOneLineCatalogue P) :
    H₄D₂Bound system P algebra := by
  have canonicalInput : KIP126.External.CataloguedExternalResult
      (KIP126.Classical.adamsOneLineDifferentials P) :=
    cataloguedAdamsOneLine P input.value.proof
  exact ⟨⟨system.strongConvergence, rfl, algebra, rfl,
    KIP126.Classical.adamsOneLineDifferentials_h₄_degrees P
      (cataloguedAdamsOneLine_proof P canonicalInput)⟩⟩

end KIP126.Classical.Adams
