import KIP126.Core.Algebra.Graded
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Filtered graded objects

This file supplies the part of the shared Core that is not already a Mathlib
object: decreasing filtrations by subobjects of a graded object, their
associated graded pieces, and filtration-preserving maps.  Filtrations and
filtered maps work in an arbitrary category; quotient-based associated graded
pieces work in an abelian category.  Neither layer assumes a field or an
elementwise presentation.
-/

namespace KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C]

/-- A decreasing filtration of a graded object.  `F s i` denotes the
subobject $F^s A_i$, and `decreasing` says $F^{s+1} A_i \le F^s A_i$. -/
structure Filtration {ι : Type w} (A : CategoryTheory.GradedObject ι C) where
  /-- The filtration subobject at a filtration level and grading index. -/
  F : ℤ → (i : ι) → Subobject (A i)
  /-- The filtration is decreasing. -/
  decreasing : ∀ (s : ℤ) (i : ι), F (s + 1) i ≤ F s i

namespace Filtration

variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

/-! ### Maps between arbitrary filtration levels

The successor inequality in `Filtration.decreasing` is the compact datum from
which all of the maps in the filtration diagram are obtained.  Keeping this
construction here (rather than re-proving it in the filtered-complex layer)
also fixes the variance convention once and for all: for `t ≤ s`, the
decreasing filtration has an inclusion `F s ↪ F t`.
-/

/-- Monotonicity of a decreasing filtration at arbitrary integer levels. -/
lemma le_of_le (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.F s i ≤ F.F t i := by
  induction s, h using Int.leInduction with
  | base => exact le_rfl
  | succ s _ ih =>
      exact (F.decreasing s i).trans ih

/-- The canonical inclusion `Fˢ Aᵢ ⟶ Fᵗ Aᵢ` when `t ≤ s`. -/
noncomputable def inclusion (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    Subobject.underlying.obj (F.F s i) ⟶ Subobject.underlying.obj (F.F t i) :=
  Subobject.ofLE (F.F s i) (F.F t i) (F.le_of_le h i)

@[simp]
lemma inclusion_arrow (F : Filtration A) {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.inclusion h i ≫ (F.F t i).arrow = (F.F s i).arrow :=
  Subobject.ofLE_arrow _

@[simp]
lemma inclusion_refl (F : Filtration A) (s : ℤ) (i : ι) :
    F.inclusion (le_rfl : s ≤ s) i = 𝟙 _ := by
  simp [inclusion]

@[reassoc (attr := simp)]
lemma inclusion_comp (F : Filtration A) {r s t : ℤ}
    (hrs : r ≤ s) (hst : s ≤ t) (i : ι) :
    F.inclusion hst i ≫ F.inclusion hrs i = F.inclusion (hrs.trans hst) i := by
  simp [inclusion]

/-- Naturality of a filtration subobject arrow under an equality of grading
indices.  This is the transport lemma needed whenever a complex shape writes
the predecessor as an expression such as `(k + 1) - 1`. -/
lemma transport_arrow (F : Filtration A) (s : ℤ) {i j : ι} (h : i = j) :
    eqToHom (congrArg (fun k => Subobject.underlying.obj (F.F s k)) h) ≫
        (F.F s j).arrow =
      (F.F s i).arrow ≫ eqToHom (congrArg A h) := by
  subst h
  simp

/-- The level inclusions are natural with respect to index transports. -/
lemma inclusion_naturality (F : Filtration A) {t s : ℤ} (h : t ≤ s)
    {i j : ι} (hij : i = j) :
    F.inclusion h i ≫
        eqToHom (congrArg (fun k => Subobject.underlying.obj (F.F t k)) hij) =
      eqToHom (congrArg (fun k => Subobject.underlying.obj (F.F s k)) hij) ≫
        F.inclusion h j := by
  subst hij
  simp


/-- The associated graded piece
$\operatorname{gr}^s_F A_i = F^s A_i/F^{s+1} A_i$. -/
noncomputable def associatedGraded [Abelian C] (F : Filtration A) (s : ℤ) (i : ι) : C :=
  cokernel (Subobject.ofLE (F.F (s + 1) i) (F.F s i) (F.decreasing s i))

/-- The quotient map from a filtration level to its associated graded piece. -/
noncomputable def toAssociatedGraded [Abelian C] (F : Filtration A) (s : ℤ) (i : ι) :
    Subobject.underlying.obj (F.F s i) ⟶ F.associatedGraded s i :=
  cokernel.π (Subobject.ofLE (F.F (s + 1) i) (F.F s i) (F.decreasing s i))

/-- A generalized element of one filtration level maps to zero in the
associated graded exactly when it lifts through the next filtration level. -/
lemma comp_toAssociatedGraded_eq_zero_iff_lifts [Abelian C]
    (F : Filtration A) {T : C} (s : ℤ) (i : ι)
    (x : T ⟶ Subobject.underlying.obj (F.F s i)) :
    x ≫ F.toAssociatedGraded s i = 0 ↔
      ∃ x' : T ⟶ Subobject.underlying.obj (F.F (s + 1) i),
        x' ≫ Subobject.ofLE (F.F (s + 1) i) (F.F s i)
          (F.decreasing s i) = x := by
  unfold toAssociatedGraded associatedGraded
  constructor
  · intro h
    exact ⟨Abelian.monoLift _ x h, Abelian.monoLift_comp _ x h⟩
  · rintro ⟨x', rfl⟩
    rw [Category.assoc, cokernel.condition, Limits.comp_zero]

/-- Two generalized elements have the same associated-graded image exactly
when their difference lifts through the next filtration level. -/
lemma comp_toAssociatedGraded_eq_iff_sub_lifts [Abelian C]
    (F : Filtration A) {T : C} (s : ℤ) (i : ι)
    (x x' : T ⟶ Subobject.underlying.obj (F.F s i)) :
    x ≫ F.toAssociatedGraded s i = x' ≫ F.toAssociatedGraded s i ↔
      ∃ z : T ⟶ Subobject.underlying.obj (F.F (s + 1) i),
        z ≫ Subobject.ofLE (F.F (s + 1) i) (F.F s i)
          (F.decreasing s i) = x - x' := by
  rw [← sub_eq_zero, ← Preadditive.sub_comp]
  exact F.comp_toAssociatedGraded_eq_zero_iff_lifts s i (x - x')

/-- All associated graded pieces, graded by filtration degree and the original
grading index. -/
noncomputable def associatedGradedObject [Abelian C] (F : Filtration A) :
    CategoryTheory.GradedObject (ℤ × ι) C :=
  fun si => F.associatedGraded si.1 si.2

/-- A filtration is degreewise eventually top: every component is the whole
object at some filtration level.  Because the filtration is decreasing, it is
then top at every lower level.  This predicate is stronger than ordinary
exhaustiveness expressed only by a union or colimit of filtration levels. -/
def IsExhaustive (F : Filtration A) : Prop :=
  ∀ i : ι, ∃ s : ℤ, F.F s i = ⊤

/-- A filtration is degreewise eventually bottom: every component vanishes at
some filtration level.  Because the filtration is decreasing, it then vanishes
at every higher level.  This is stronger than separatedness, which asks only
for zero intersection. -/
def IsEventuallyZero [Abelian C] (F : Filtration A) : Prop :=
  ∀ i : ι, ∃ s : ℤ, F.F s i = ⊥

/-- A filtration is bounded below degreewise if sufficiently low levels are
the whole object. -/
structure IsBoundedBelow (F : Filtration A) where
  /-- A lower filtration bound for each graded component. -/
  lower : ι → ℤ
  eq_top_of_le : ∀ (i : ι) (s : ℤ), s ≤ lower i → F.F s i = ⊤

/-- A filtration is bounded above degreewise if sufficiently high levels are
zero. -/
structure IsBoundedAbove [Abelian C] (F : Filtration A) where
  /-- An upper filtration bound for each graded component. -/
  upper : ι → ℤ
  eq_bot_of_le : ∀ (i : ι) (s : ℤ), upper i ≤ s → F.F s i = ⊥

/-- A degreewise bounded filtration has both a lower and an upper bound. -/
structure IsBounded [Abelian C] (F : Filtration A) extends IsBoundedBelow F, IsBoundedAbove F where
  lower_le_upper : ∀ i : ι, lower i ≤ upper i

/-- A bounded-below filtration is exhaustive. -/
lemma IsBoundedBelow.isExhaustive {F : Filtration A} (hF : IsBoundedBelow F) :
    IsExhaustive F := by
  intro i
  exact ⟨hF.lower i, hF.eq_top_of_le i (hF.lower i) le_rfl⟩

/-- A bounded-above filtration is eventually zero. -/
lemma IsBoundedAbove.isEventuallyZero [Abelian C] {F : Filtration A} (hF : IsBoundedAbove F) :
    IsEventuallyZero F := by
  intro i
  exact ⟨hF.upper i, hF.eq_bot_of_le i (hF.upper i) le_rfl⟩

section MittagLeffler

variable [Abelian C]

private lemma imageSubobject_ofLE_eq_bot_of_eq_bot {B : C} (X Y : Subobject B)
    (h : X ≤ Y) (hX : X = ⊥) : imageSubobject (Subobject.ofLE X Y h) = ⊥ := by
  subst hX
  have hzero : Subobject.ofLE ⊥ Y h = 0 := by
    apply (cancel_mono Y.arrow).mp
    rw [Subobject.ofLE_arrow, Subobject.bot_arrow, zero_comp]
  rw [hzero, imageSubobject_zero]

/-! ### Mittag--Leffler stabilization

The categorical form records stabilization of the images of the deeper
filtration levels inside a fixed level.  It is deliberately stated using
subobjects rather than elements, so it applies to every abelian category. -/

/-- A decreasing filtration satisfies the Mittag--Leffler condition when the
images of its deeper levels in each fixed level eventually stabilize.

This reusable condition is the filtration-side prerequisite for the inverse-limit
ESS extension target `lem:synthetic-ess-coherent-tower-limit` in
`blueprint/src/chapters/comparison_and_rules.tex`. -/
def IsMittagLeffler (F : Filtration A) : Prop :=
  ∀ (i : ι) (s : ℤ), ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    imageSubobject (Subobject.ofLE (F.F (s + (n : ℤ)) i) (F.F s i)
      (F.le_of_le (by omega) i)) =
      imageSubobject (Subobject.ofLE (F.F (s + (N : ℤ)) i) (F.F s i)
        (F.le_of_le (by omega) i))

/-- A degreewise bounded-above filtration has eventually zero images and hence
satisfies the categorical Mittag--Leffler condition. -/
lemma IsBoundedAbove.isMittagLeffler {F : Filtration A}
    (hF : IsBoundedAbove F) : IsMittagLeffler F := by
  intro i s
  refine ⟨(hF.upper i - s).toNat, ?_⟩
  intro n hn
  have hN : hF.upper i ≤ s + ((hF.upper i - s).toNat : ℤ) := by omega
  have hn' : hF.upper i ≤ s + (n : ℤ) := by omega
  rw [imageSubobject_ofLE_eq_bot_of_eq_bot _ _ _
      (hF.eq_bot_of_le i _ hn'),
    imageSubobject_ofLE_eq_bot_of_eq_bot _ _ _
      (hF.eq_bot_of_le i _ hN)]

/-- A degreewise eventually-zero filtration satisfies the
Mittag--Leffler condition. -/
lemma IsEventuallyZero.isMittagLeffler {F : Filtration A}
    (hF : IsEventuallyZero F) : IsMittagLeffler F := by
  let hB : IsBoundedAbove F :=
    { upper := fun i => Classical.choose (hF i)
      eq_bot_of_le := by
        intro i s hs
        apply le_antisymm
        · rw [← Classical.choose_spec (hF i)]
          exact F.le_of_le hs i
        · exact bot_le }
  exact hB.isMittagLeffler

end MittagLeffler

end Filtration

/-- A morphism of filtered graded objects is a graded map whose restriction to
each filtration subobject factors through the corresponding target
subobject. -/
structure FilteredMorphism {ι : Type w}
    {A B : CategoryTheory.GradedObject ι C} (F : Filtration A) (G : Filtration B) where
  /-- The underlying degree-preserving map. -/
  map : A ⟶ B
  /-- Preservation of every filtration level. -/
  preserves : ∀ (s : ℤ) (i : ι),
    ∃ φ : Subobject.underlying.obj (F.F s i) ⟶ Subobject.underlying.obj (G.F s i),
      φ ≫ (G.F s i).arrow = (F.F s i).arrow ≫ map i

namespace FilteredMorphism

variable {ι : Type w}
  {A B D : CategoryTheory.GradedObject ι C}
  {F : Filtration A} {G : Filtration B} {H : Filtration D}

/-- The identity map of a filtered graded object. -/
def id (F : Filtration A) : FilteredMorphism F F where
  map := 𝟙 A
  preserves := fun s i => ⟨𝟙 _, by simp⟩

/-- Composition of filtration-preserving graded maps. -/
def comp (f : FilteredMorphism F G) (g : FilteredMorphism G H) :
    FilteredMorphism F H where
  map := f.map ≫ g.map
  preserves := fun s i => by
    refine ⟨(f.preserves s i).choose ≫ (g.preserves s i).choose, ?_⟩
    change ((f.preserves s i).choose ≫ (g.preserves s i).choose) ≫
      (H.F s i).arrow = (F.F s i).arrow ≫ (f.map i ≫ g.map i)
    rw [Category.assoc, (g.preserves s i).choose_spec, ← Category.assoc,
      (f.preserves s i).choose_spec]
    simp only [Category.assoc]

lemma id_preserves_eq (F : Filtration A) (s : ℤ) (i : ι) :
    ((FilteredMorphism.id F).preserves s i).choose = 𝟙 _ := by
  apply (cancel_mono (F.F s i).arrow).mp
  rw [(FilteredMorphism.id F).preserves s i |>.choose_spec]
  dsimp [FilteredMorphism.id]
  simp

lemma comp_preserves_eq (f : FilteredMorphism F G) (g : FilteredMorphism G H)
    (s : ℤ) (i : ι) :
    ((FilteredMorphism.comp f g).preserves s i).choose =
      (f.preserves s i).choose ≫ (g.preserves s i).choose := by
  apply (cancel_mono (H.F s i).arrow).mp
  calc
    ((FilteredMorphism.comp f g).preserves s i).choose ≫
          (H.F s i).arrow =
        (F.F s i).arrow ≫ (FilteredMorphism.comp f g).map i :=
      (FilteredMorphism.comp f g).preserves s i |>.choose_spec
    _ = ((F.F s i).arrow ≫ f.map i) ≫ g.map i := by
      simp only [FilteredMorphism.comp,
        GradedObject.categoryOfGradedObjects_comp]
      simp only [Category.assoc]
    _ = ((f.preserves s i).choose ≫ (G.F s i).arrow) ≫ g.map i := by
      rw [(f.preserves s i).choose_spec]
    _ = (f.preserves s i).choose ≫
          ((G.F s i).arrow ≫ g.map i) := by simp only [Category.assoc]
    _ = (f.preserves s i).choose ≫
          ((g.preserves s i).choose ≫ (H.F s i).arrow) := by
      rw [(g.preserves s i).choose_spec]
    _ = ((f.preserves s i).choose ≫ (g.preserves s i).choose) ≫
          (H.F s i).arrow := by simp only [Category.assoc]

/-- The map on associated graded pieces induced by a filtration-preserving
morphism. -/
noncomputable def associatedGradedMap [Abelian C] (f : FilteredMorphism F G) (s : ℤ) (i : ι) :
    F.associatedGraded s i ⟶ G.associatedGraded s i :=
  cokernel.map
    (Subobject.ofLE (F.F (s + 1) i) (F.F s i) (F.decreasing s i))
    (Subobject.ofLE (G.F (s + 1) i) (G.F s i) (G.decreasing s i))
    (f.preserves (s + 1) i).choose
    (f.preserves s i).choose
    (by
      apply (cancel_mono ((G.F s i).arrow)).mp
      simp only [Category.assoc, Subobject.ofLE_arrow]
      rw [(f.preserves s i).choose_spec, (f.preserves (s + 1) i).choose_spec,
        ← Category.assoc, Subobject.ofLE_arrow])

/-- The quotient projections commute with the map induced on associated graded
pieces.  This is the universal-property equation used by later filtered
complex constructions. -/
lemma toAssociatedGraded_comp_associatedGradedMap [Abelian C]
    (f : FilteredMorphism F G) (s : ℤ) (i : ι) :
    F.toAssociatedGraded s i ≫ f.associatedGradedMap s i =
      (f.preserves s i).choose ≫ G.toAssociatedGraded s i := by
  unfold Filtration.toAssociatedGraded FilteredMorphism.associatedGradedMap
  dsimp only [cokernel.map]
  exact cokernel.π_desc _ _ _

@[simp]
lemma associatedGradedMap_id [Abelian C] (F : Filtration A) (s : ℤ) (i : ι) :
    (FilteredMorphism.id F).associatedGradedMap s i = 𝟙 _ := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE (F.F (s + 1) i)
    (F.F s i) (F.decreasing s i)))).mp
  have h := toAssociatedGraded_comp_associatedGradedMap
    (FilteredMorphism.id F) s i
  have hi := id_preserves_eq F s i
  change F.toAssociatedGraded s i ≫
      (FilteredMorphism.id F).associatedGradedMap s i =
    F.toAssociatedGraded s i ≫ 𝟙 _
  rw [h, hi]
  simp

@[simp]
lemma associatedGradedMap_comp [Abelian C]
    (f : FilteredMorphism F G) (g : FilteredMorphism G H) (s : ℤ) (i : ι) :
    (FilteredMorphism.comp f g).associatedGradedMap s i =
      f.associatedGradedMap s i ≫ g.associatedGradedMap s i := by
  apply (cancel_epi (cokernel.π (Subobject.ofLE (F.F (s + 1) i)
    (F.F s i) (F.decreasing s i)))).mp
  calc
    F.toAssociatedGraded s i ≫
          (FilteredMorphism.comp f g).associatedGradedMap s i =
        ((FilteredMorphism.comp f g).preserves s i).choose ≫
          H.toAssociatedGraded s i :=
      toAssociatedGraded_comp_associatedGradedMap _ _ _
    _ = (f.preserves s i).choose ≫ (g.preserves s i).choose ≫
          H.toAssociatedGraded s i := by
      rw [comp_preserves_eq]
      simp only [Category.assoc]
    _ = (f.preserves s i).choose ≫
          (G.toAssociatedGraded s i ≫ g.associatedGradedMap s i) := by
      simpa only [Category.assoc] using
        congrArg (fun q => (f.preserves s i).choose ≫ q)
          (toAssociatedGraded_comp_associatedGradedMap g s i).symm
    _ = (F.toAssociatedGraded s i ≫ f.associatedGradedMap s i) ≫
          g.associatedGradedMap s i := by
      simpa only [Category.assoc] using
        congrArg (fun q => q ≫ g.associatedGradedMap s i)
          (toAssociatedGraded_comp_associatedGradedMap f s i).symm
    _ = F.toAssociatedGraded s i ≫
          (f.associatedGradedMap s i ≫ g.associatedGradedMap s i) := by
      simp only [Category.assoc]

end FilteredMorphism

end KIP126.Core.Algebra
