module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.DiagonalSurjectivity
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricInverse
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.TwoSummands

set_option autoImplicit false

open AlgebraicGeometry AlgebraicGeometry.RingedSpace CategoryTheory.Waldhausen

universe u

noncomputable example (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    (perfectComplexesWaldhausen X.toRingedSpace).K n ×
        (perfectComplexesWaldhausen X.toRingedSpace).K n ≃*
      (perfectComplexesWaldhausen (projectiveSpaceOver 1 X).toRingedSpace).K n :=
  X.projectiveLineKEquiv n

example (X : Scheme.{u}) [CompactSpace X] (n : ℕ)
    (x : (perfectComplexesWaldhausen (projectiveSpaceOver 1 X).toRingedSpace).K n) :
    (X.projectiveLineKEquiv n).symm x = X.projectiveLineCorrectedCoordinates n x :=
  X.projectiveLineKEquiv_symm_apply n x

#print axioms AlgebraicGeometry.Scheme.projectiveLineKEquiv
#print axioms AlgebraicGeometry.Scheme.projectiveLineKEquiv_symm_apply
#print axioms AlgebraicGeometry.Scheme.projectiveLineKMap_surjective
#print axioms AlgebraicGeometry.Scheme.projectiveLineCorrectedCoordinates_leftInverse
