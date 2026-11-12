/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupportedApproximation

public import Colib.AlgebraicGeometry.Modules.BoundedFlatCoefficientSupportRestriction
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectSupport


/-! # Original supported coefficient evaluation into perfect complexes

This is the literal supported bounded-flat evaluation followed by its actual inclusion.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.StrictSections AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] (T : Q.left.Opens)
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation
  boundedAboveFlatCoefficientSupportedEvaluation

/-- Original supported native evaluation followed by the actual supported perfect inclusion. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/\
    CoefficientSupportedPerfectEvaluation.lean:31"
  "adaptation" "Actual supported quotient grade, original evaluation and same chosen zero"]
def boundedAboveFlatCoefficientSupportedFullOpenPerfectEvaluation (a : Under R) :
    BoundedAboveFlatCoefficientSupportedOpenSections f T a ⥤
      (perfectSupported (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι).FullSubcategory :=
  boundedAboveFlatCoefficientSupportedEvaluation (boundedAboveFlatCoefficientOpenSupportOpen f T
    a).ι ⋙
    boundedAboveFlatPerfectSupportedInclusion (boundedAboveFlatCoefficientOpenSupportOpen f T a).ι

end AlgebraicGeometry.Scheme.Modules
