/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSections
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfect
/-! # Original identity evaluation into actual perfect complexes -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
/-- Native identity evaluation followed by the literal bounded-flat perfect inclusion. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientPerfectEvaluation.lean:32"
  "adaptation" "Original actual ordinary perfect evaluation"]
def boundedAboveFlatCoefficientFullOpenPerfectEvaluation (_f : P ⟶ Q) (a : Under R) :
    BoundedAboveFlatCoefficientSections (op P, a) ⥤
      ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := (space (op P, a)).toRingedSpace)) :=
  boundedAboveFlatCoefficientOriginalEvaluation (op P, a) ⋙
    RingedSpace.boundedAboveFlatPerfectInclusion (space (op P, a)).toRingedSpace
end AlgebraicGeometry.Scheme.Modules
