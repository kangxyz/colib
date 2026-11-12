/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Modules.PerfectOpenWeak
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ImageQuotient
/-! # Actual raw ordinary relative-open image-quotient grading

Only the original grading definition is selected. No deficit spectrum or stable
comparison is asserted in this owner.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.AlgebraicGrothendieck
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The literal quotient by the original relative-open restriction's algebraic image. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/OpenDeficitGrading.lean:33"
  "adaptation" "Original raw relative-open image quotient grading"]
def perfectOpenDeficitGrading :
    Cofinality.Grading (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)
      (ImageQuotient (perfectOpenWeakWaldhausen j) (perfectComplexesRestrictOpenImmersion j)
        (perfectOpenRestrict_isExact j)) :=
  imageQuotientGrading (perfectOpenWeakWaldhausen j) (perfectComplexesRestrictOpenImmersion j)
    (perfectOpenRestrict_isExact j)

end AlgebraicGeometry.Scheme.Modules
