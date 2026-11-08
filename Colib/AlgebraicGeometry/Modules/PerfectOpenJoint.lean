/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectJoint
public import Colib.AlgebraicGeometry.Modules.PerfectOpenWeak

/-! # Native perfect joint cylinders for open-detected weak equivalences

The fine category and ambient monomorphism cofibrations are unchanged. This
specializes the constructed native cylinder to the actual nested relative weak
class of an arbitrary open immersion. Source-only draft; not elaborated.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- Constructed joint data for the original native relative-open model. -/
def perfectOpenJointData : Waldhausen.Fibration.RowFactorization.JointData
    (perfectOpenNested j) :=
  RingedSpace.perfectComplexesJointData X.toRingedSpace (perfectOpenNested j)

/-- The actual second endpoint is a section, with no extra cylinder hypothesis. -/
theorem perfectOpenJointData_secondEndpointSection :
    Waldhausen.Fibration.RowFactorization.SecondEndpointSection (perfectOpenNested j)
      (perfectOpenJointData j) :=
  RingedSpace.perfectComplexesJointData_secondEndpointSection X.toRingedSpace
    (perfectOpenNested j)

end AlgebraicGeometry.Scheme.Modules
