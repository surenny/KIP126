import KIP126.Core.Algebra.Completion.Basic

/-!
# Completion safety regressions

These examples exercise the public Mittag--Leffler and witness-indexed
completion interfaces without introducing a global completeness assumption.
-/

namespace KIP126.Core.Algebra

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type w} {A : CategoryTheory.GradedObject ι C}

example (F : Filtration A) (hF : F.IsBoundedAbove) :
    F.IsMittagLeffler :=
  hF.isMittagLeffler

example (F : Filtration A) (hF : F.IsEventuallyZero) :
    F.IsMittagLeffler :=
  hF.isMittagLeffler

noncomputable example (F : Filtration A) (W : ∀ i : ι, F.CompletionWitness i) :
    Filtration (fun i => F.completionObject W i) :=
  F.completionFiltration W

noncomputable example (F : Filtration A) (W : ∀ i : ι, F.CompletionWitness i)
    (s : ℤ) (i : ι) :
    (F.completionFiltration W).F s i =
      kernelSubobject (F.completionProjection W s i) :=
  F.completionFiltration_F W s i

example (F : Filtration A) (W : ∀ i : ι, F.CompletionWitness i)
    {t s : ℤ} (h : t ≤ s) (i : ι) :
    F.completionProjection W s i ≫ F.quotientTransition h i =
      F.completionProjection W t i :=
  F.completionProjection_comp_quotientTransition W h i

end KIP126.Core.Algebra
