/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Complex
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Representable
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.WeightOne

/-! # The weight-one complex of the reduced torus motive -/

public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

local notation "B" => SmoothSite.base (Spec (CommRingCat.of k))

/-- The shifted singular motive of the original base quotient is the
actual signed weight-one motivic complex. -/
def torusCancellationBaseMotivicComplexIso :
    ((effectiveMotivesMinusToDerived k).obj
      ((singularEffectiveMotiveFunctor k).obj (torusCancellationCoefficients k (Cor.mk B))))⟦
        (-1 : ℤ)⟧ ≅ DerivedCategory.Q.obj (motivicComplex k 1) := by
  let N := SheafWithTransfers.{u + 1} k
  let Q := DerivedCategory.Q (C := N)
  let a := singularSheafCochainFunctor k 0
  let e := a.mapIso (torusCancellationBaseWeightOneIso k)
  exact (shiftFunctor _ (-1 : ℤ)).mapIso (Q.mapIso e) ≪≫
    ((Q.commShiftIso (-1 : ℤ)).app (a.obj (reducedTorus k 1))).symm

end AlgebraicGeometry.MotivicHomotopy
