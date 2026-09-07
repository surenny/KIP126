import KIP126.Synthetic.SpectralSequence.Basic

namespace KIP126.Synthetic.SpectralSequence

open CategoryTheory

structure TypedLambdaAction (A : SyntheticAdamsSS) where
  map : ∀ (r : ℤ) (hr : 2 ≤ r) (i : Tridegree),
    (A.sequence.page r).X i ⟶ (A.sequence.page r).X (lambdaTarget i)
  homologyMap : ∀ (r : ℤ) (hr : 2 ≤ r) (i : Tridegree),
    (A.sequence.page r).homology i ⟶
      (A.sequence.page r).homology (lambdaTarget i)
  page_passage_comm : ∀ (r : ℤ) (hr : 2 ≤ r) (i : Tridegree),
    homologyMap r hr i ≫
        (A.sequence.iso r (r + 1) (lambdaTarget i) rfl hr).hom =
      (A.sequence.iso r (r + 1) i rfl hr).hom ≫
        map (r + 1) (by omega) i
  differential_comm : ∀ (r : ℤ) (hr : 2 ≤ r) (i : Tridegree),
    (A.sequence.page r).d i (syntheticAdamsTarget r.toNat i) ≫
        map r hr (syntheticAdamsTarget r.toNat i) =
      map r hr i ≫
        (A.sequence.page r).d (lambdaTarget i)
          (lambdaTarget (syntheticAdamsTarget r.toNat i))
  map_two_eq_lambdaMap : ∀ i : Tridegree,
    map 2 (by norm_num) i = A.lambdaMap i

def lambdaMapFromAction (A : SyntheticAdamsSS) (L : TypedLambdaAction A)
    (i : Tridegree) :
    (A.E₂).X i ⟶ (A.E₂).X (lambdaTarget i) :=
  L.map 2 (by norm_num) i

theorem lambdaMapFromAction_eq_lambdaMap
    (A : SyntheticAdamsSS) (L : TypedLambdaAction A) (i : Tridegree) :
    lambdaMapFromAction A L i = A.lambdaMap i :=
  L.map_two_eq_lambdaMap i

def lambdaMapFromAction_degree (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (i : Tridegree) :
    (A.E₂).X i ⟶ (A.E₂).X (i + lambdaDegree) :=
  lambdaMapFromAction A L i

structure SyntheticPageRepresentative (A : SyntheticAdamsSS) where
  name : String
  degree : Tridegree
  representative : (A.E₂).X degree
  nonzero : representative ≠ 0

structure H₄LambdaSlice (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) where
  h₄_nonzero : A.h₄ ≠ 0
  h₀h₃Squared_nonzero : A.h₀h₃Squared ≠ 0
  lambdaShifted_nonzero :
    (lambdaMapFromAction A L (3, 17, 17)).hom A.h₀h₃Squared ≠ 0
  differential_eq_lambdaShifted :
    (A.d₂ (1, 16, 16)).hom A.h₄ =
      (lambdaMapFromAction A L (3, 17, 17)).hom A.h₀h₃Squared

def h₄Representative (A : SyntheticAdamsSS) (L : TypedLambdaAction A)
    (S : H₄LambdaSlice A L) : SyntheticPageRepresentative A :=
  { name := "h₄"
    degree := (1, 16, 16)
    representative := A.h₄
    nonzero := S.h₄_nonzero }

def h₀h₃SquaredRepresentative (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (S : H₄LambdaSlice A L) :
    SyntheticPageRepresentative A :=
  { name := "h₀h₃²"
    degree := (3, 17, 17)
    representative := A.h₀h₃Squared
    nonzero := S.h₀h₃Squared_nonzero }

def lambdaShiftedRepresentative (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (S : H₄LambdaSlice A L) :
    SyntheticPageRepresentative A :=
  { name := "λ·h₀h₃²"
    degree := lambdaTarget (3, 17, 17)
    representative := (lambdaMapFromAction A L (3, 17, 17)).hom A.h₀h₃Squared
    nonzero := S.lambdaShifted_nonzero }

@[simp] theorem h₄Representative_degree (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (S : H₄LambdaSlice A L) :
    (h₄Representative A L S).degree = (1, 16, 16) := rfl

@[simp] theorem h₀h₃SquaredRepresentative_degree (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (S : H₄LambdaSlice A L) :
    (h₀h₃SquaredRepresentative A L S).degree = (3, 17, 17) := rfl

@[simp] theorem lambdaShiftedRepresentative_degree (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (S : H₄LambdaSlice A L) :
    (lambdaShiftedRepresentative A L S).degree = (3, 17, 16) := by
  simp [lambdaShiftedRepresentative, lambdaTarget, lambdaDegree]

theorem h₄Representative_nonzero (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (S : H₄LambdaSlice A L) :
    (h₄Representative A L S).representative ≠ 0 :=
  S.h₄_nonzero

theorem h₀h₃SquaredRepresentative_nonzero (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (S : H₄LambdaSlice A L) :
    (h₀h₃SquaredRepresentative A L S).representative ≠ 0 :=
  S.h₀h₃Squared_nonzero

theorem lambdaShiftedRepresentative_nonzero (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (S : H₄LambdaSlice A L) :
    (lambdaShiftedRepresentative A L S).representative ≠ 0 :=
  S.lambdaShifted_nonzero

theorem h₄_differential_eq_lambdaShifted (A : SyntheticAdamsSS)
    (L : TypedLambdaAction A) (S : H₄LambdaSlice A L) :
    (A.d₂ (h₄Representative A L S).degree).hom
        (h₄Representative A L S).representative =
      (lambdaShiftedRepresentative A L S).representative := by
  exact S.differential_eq_lambdaShifted

end KIP126.Synthetic.SpectralSequence
