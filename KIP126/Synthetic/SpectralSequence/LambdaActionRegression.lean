import KIP126.Synthetic.SpectralSequence.LambdaAction

namespace KIP126.Synthetic.SpectralSequence.Regression

open KIP126.Synthetic.SpectralSequence

example (A : SyntheticAdamsSS) (L : TypedLambdaAction A) (i : Tridegree) :
    lambdaMapFromAction A L i = A.lambdaMap i :=
  lambdaMapFromAction_eq_lambdaMap A L i

example (A : SyntheticAdamsSS) (L : TypedLambdaAction A)
    (S : H₄LambdaSlice A L) :
    (h₄Representative A L S).degree = (1, 16, 16) :=
  h₄Representative_degree A L S

example (A : SyntheticAdamsSS) (L : TypedLambdaAction A)
    (S : H₄LambdaSlice A L) :
    (h₀h₃SquaredRepresentative A L S).degree = (3, 17, 17) :=
  h₀h₃SquaredRepresentative_degree A L S

example (A : SyntheticAdamsSS) (L : TypedLambdaAction A)
    (S : H₄LambdaSlice A L) :
    (lambdaShiftedRepresentative A L S).degree = (3, 17, 16) :=
  lambdaShiftedRepresentative_degree A L S

example (A : SyntheticAdamsSS) (L : TypedLambdaAction A)
    (S : H₄LambdaSlice A L) :
    (h₄Representative A L S).representative ≠ 0 ∧
      (h₀h₃SquaredRepresentative A L S).representative ≠ 0 ∧
      (lambdaShiftedRepresentative A L S).representative ≠ 0 := by
  exact ⟨h₄Representative_nonzero A L S,
    h₀h₃SquaredRepresentative_nonzero A L S,
    lambdaShiftedRepresentative_nonzero A L S⟩

example (A : SyntheticAdamsSS) (L : TypedLambdaAction A)
    (S : H₄LambdaSlice A L) :
    (A.d₂ (h₄Representative A L S).degree).hom
        (h₄Representative A L S).representative =
      (lambdaShiftedRepresentative A L S).representative :=
  h₄_differential_eq_lambdaShifted A L S

end KIP126.Synthetic.SpectralSequence.Regression
