module

import Colib.AlgebraicGeometry.Normalization.StrictLocalBaseChange.Normal

open AlgebraicGeometry CategoryTheory.Limits

universe u

example (B : BigEtaleSite.{u}) {S X : Scheme.{u}} (hS : B.Contains S)
    (s : GeometricPoint S) (p : X ⟶ S) [IsNormal X] :
    IsNormal (pullback p (strictHenselizationToBase B S hS s)) :=
  isNormal_pullback_strictHenselizationToBase B hS s p

#print axioms AlgebraicGeometry.isNormal_pullback_of_indEtale
#print axioms AlgebraicGeometry.isNormal_pullback_strictHenselizationToBase

#print axioms AlgebraicGeometry.flat_strictHenselizationToBase
