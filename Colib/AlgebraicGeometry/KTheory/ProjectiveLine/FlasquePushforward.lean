/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasquePushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence

/-! # Perfectness of bounded-below flasque direct images -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance 2000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local notation "F" => (Functor.mapHomologicalComplex (pushforward f) (ComplexShape.up ℤ))

/-- Perfectness of the actual direct-image representative, by Stacks Tag 0B91. -/
theorem isPerfectComplex_flasquePushforward [Flat f] [IsProper f]
    [LocallyOfFinitePresentation f] (K : CochainComplex X.Modules ℤ)
    (hK : IsPerfectComplex (X := X.toRingedSpace) K)
    (hb : CochainComplex.plus X.Modules K)
    (hfl : ∀ n, TopCat.Sheaf.IsFlasque
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).obj (K.X n))) :
    IsPerfectComplex (X := Y.toRingedSpace) ((F).obj K) :=
  isPerfectComplex_of_isPerfect_representation
    (isPerfect_derivedPushforward_of_flat_of_isProper f _ hK.isPerfect)
    ⟨flasquePushforwardIso f K hb hfl⟩

end AlgebraicGeometry.Scheme.Modules
