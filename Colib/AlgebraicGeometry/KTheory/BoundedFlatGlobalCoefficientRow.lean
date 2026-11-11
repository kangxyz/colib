/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalCoefficientModelRestriction

/-! # The original global and coefficient section rows -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}}

/-- The actual coefficient row of the global section Model diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentAction.lean:26"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def globalRow (P : Over (Spec R)) : Under R ⥤ WideSubcategory preservesZero.{u + 1} :=
  row P ⋙ AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R ⋙
    boundedAboveFlatGlobalSectionModelFunctor

/-- Original restriction from the global row to the existing coefficient-first row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionLaurentAction.lean:30"
  "adaptation" "Original coefficient row, Laurent scalar and unchanged Bass seed/telescope"]
def rowRestriction (P : Over (Spec R)) :
    globalRow P ⟶ boundedAboveFlatCoefficientSectionModelRow P :=
  Functor.whiskerLeft (row P) (boundedAboveFlatGlobalCoefficientModelRestriction R)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
