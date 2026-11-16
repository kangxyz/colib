/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateChartRatio
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization

/-! # Trivializing the hyperplane bundle by its chart coordinate -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

set_option backward.isDefEq.respectTransparency false in
/-- The section `Tᵢ` induces the actual unit-to-hyperplane-bundle trivialization on `D₊(Tᵢ)`. -/
theorem isIso_coordinateSection_over (S : Scheme.{u}) (i : Fin 2) :
    IsIso (((twistOver 1 S 1).unitHomEquiv.symm (coordinateSection S i)).over
      (standardChart S i)) := by
  let X := projectiveSpaceOver 1 S
  let : ∀ x : X.toRingedSpace.carrier,
      IsLocalRing (ringStalk X.toRingedSpace x) := fun x =>
    X.isLocalRing x
  apply Stacks.SheafOfModules.isIso_over_of_le_nonvanishingLocus
    (twistOverNegIsoUnit 1 S 1) (coordinateSection S i) (standardChart S i)
  intro x hx
  rw [coordinateSection_eq_sectionsOfTop, Stacks.AmpleBridge.nonvanishingLocus_sectionsOfTop]
  exact mem_nonvanishingLocus_coordinateSectionTop S i hx

end AlgebraicGeometry.Scheme.ProjectiveLine
