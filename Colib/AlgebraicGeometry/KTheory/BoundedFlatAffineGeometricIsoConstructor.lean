/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineNormalizationSplit

/-! The exact constructor of the affine geometric composition isomorphism. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual comparison includes precisely the original Spec composition transport. -/
theorem boundedAboveFlatAffineGeometricCompIso_eq_trans
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineGeometricCompIso f g =
      eqToIso (congrArg boundedAboveFlatPerfectPullback (Spec.map_comp f g)) ≪≫
        boundedAboveFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f) := by
  rfl

end AlgebraicGeometry.Scheme.Modules
