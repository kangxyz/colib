/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.ProjectiveSpace.PrincipalOpen
import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace

/-! Focused checks of the native homogeneous localization and its unchanged generators.

The native scheme-base `ProjectiveSpace` is imported explicitly to check that these polynomial
chart extensions coexist with the existing declaration.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AlgebraicGeometry.ProjectiveSpace

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

variable (k ι : Type u) [CommRing k] [Finite ι] (i j : ι)

example : Spec (.of (coordinateRing k ι i)) ⟶
    Proj (homogeneousSubmodule ι k) := coordinateChart k ι i

example (n : ℕ) (S : Scheme.{u}) : Scheme.{u} := AlgebraicGeometry.ProjectiveSpace n S

example : coordinateRing k ι i = Away (homogeneousSubmodule ι k) (X i) := rfl

example (a : k) : coordinateRingCoefficient k ι i a =
    Away.mk _ (isHomogeneous_X k i) 0 (C a) (by simp) := rfl

example : coordinateRatio k ι i j =
    Away.mk _ (isHomogeneous_X k i) 1 (X j) (by simpa using isHomogeneous_X k j) := rfl

example : (polynomialToCoordinateRing k ι i).comp (coordinateRingToPolynomial k ι i) =
    RingHom.id _ := polynomialToCoordinateRing_comp_coordinateRingToPolynomial k ι i

example (a : k) : coordinateRingEquivPolynomial k ι i (coordinateRingCoefficient k ι i a) =
    C a := coordinateRingToPolynomial_coefficient k ι i a

example (j : {j : ι // j ≠ i}) :
    coordinateRingEquivPolynomial k ι i (coordinateRatio k ι i j.val) = X j :=
  coordinateRingToPolynomial_ratio k ι i j

example : coordinateChart k ι i ⁻¹ᵁ coordinateOpen k ι j =
    PrimeSpectrum.basicOpen (coordinateRatio k ι i j) :=
  coordinateChart_preimage_coordinateOpen k ι i j

example : IsProper (toSpec k ι) := inferInstance

example : coordinateChart k ι i ≫ toSpec k ι =
    Spec.map (CommRingCat.ofHom (coordinateCoefficientHom k ι i)) :=
  coordinateChart_toSpec k ι i

end

section NativeComparison

variable (k : Type u) [CommRing k] (n : ℕ) (i : Fin (n + 1))

example : (coordinateRingEquivPolynomial k (Fin (n + 1)) i).symm =
    Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv k n i := by
  apply RingEquiv.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    change polynomialToCoordinateRing k (Fin (n + 1)) i (C a) = _
    rw [polynomialToCoordinateRing_C]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv_apply,
      Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_C]
    exact (Stacks.AlgebraicGeometry.ProjPolyChart.coeffToAway_eq_mk k n i a).symm
  · intro j
    change polynomialToCoordinateRing k (Fin (n + 1)) i (X j) = _
    rw [polynomialToCoordinateRing_X]
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv_apply,
      Stacks.AlgebraicGeometry.ProjPolyChart.chartHom_X]
    rfl

end NativeComparison
