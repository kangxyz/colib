/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.WeilOpenRestriction

open AlgebraicGeometry CategoryTheory

universe u

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (Z : PrimeDivisor U) :
    effectiveCartierMultiplicity (I.comap j) Z =
      effectiveCartierMultiplicity I (OpenWeilRestriction.primeDivisorMap j Z) :=
  OpenWeilRestriction.effectiveCartierMultiplicity_comap j I Z

example {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [IsNoetherian X] [IsIntegral X] [IsNoetherian U] [IsIntegral U]
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    OpenWeilRestriction.restrictWeil j (effectiveCartierWeilDivisor I hI) =
      effectiveCartierWeilDivisor (I.comap j)
        (Stacks.Divisors.isPullbackDefined_of_flat j I hI) :=
  OpenWeilRestriction.restrictWeil_effectiveCartierWeilDivisor j I hI

#print axioms AlgebraicGeometry.OpenWeilRestriction.effectiveCartierMultiplicity_comap
#print axioms AlgebraicGeometry.OpenWeilRestriction.restrictWeil_effectiveCartierWeilDivisor
