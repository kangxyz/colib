/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardChartPolynomial

/-!
# The actual overlap of the two projective-line charts

The two maps are the canonical restriction and open inclusion. They exhibit the
overlap as the pullback of the original two chart immersions into the native line.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

variable (S : Scheme.{u})

/-- The actual overlap map to the positive chart. -/
def overlapToPositive : (chartOverlap S).toScheme ⟶ (positiveChart S).toScheme :=
  (negativeChart S).ι ∣_ positiveChart S

/-- The actual overlap map to the negative chart. -/
def overlapToNegative : (chartOverlap S).toScheme ⟶ (negativeChart S).toScheme :=
  (chartOverlap S).ι

/-- The canonical overlap square is cartesian, with both original inclusions. -/
theorem overlap_isPullback :
    IsPullback (overlapToPositive S) (overlapToNegative S)
      (positiveChart S).ι (negativeChart S).ι :=
  isPullback_morphismRestrict (negativeChart S).ι (positiveChart S)

/-- The two maps agree after inclusion into the canonical line. -/
@[reassoc]
theorem overlapToPositive_comp :
    overlapToPositive S ≫ (positiveChart S).ι =
      overlapToNegative S ≫ (negativeChart S).ι :=
  (overlap_isPullback S).w

instance : IsOpenImmersion (overlapToPositive S) := by
  let : IsOpenImmersion (overlapToPositive S ≫ (positiveChart S).ι) := by
    rw [overlapToPositive_comp]
    unfold overlapToNegative
    infer_instance
  exact IsOpenImmersion.of_comp _ (positiveChart S).ι

instance : IsOpenImmersion (overlapToNegative S) := by
  unfold overlapToNegative
  infer_instance

end AlgebraicGeometry.Scheme.ProjectiveLine
