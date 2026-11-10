/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenStructure
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeakEquivalence

/-!
# The actual relative-open section evaluation equivalence

The inverse of original evaluation preserves the genuine open-detected weak class by its
actual counit. Both directions are exact for the same original relative-open structures.
The target remains the relative model on the ambient scheme, with no full-open identification.
-/
@[expose] public section

open CategoryTheory.Waldhausen

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules
open Waldhausen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedAboveFlatAffineOriginalEvaluation

/-- The original evaluation inverse is exact for the actual relative-open section weak class. -/
theorem boundedAboveFlatAffineSectionOpenEquivalence_inverse_exact :
    IsExact (boundedAboveFlatPerfectOpenWaldhausen j).cof
      (boundedAboveFlatPerfectOpenWaldhausen j).weq
      (boundedAboveFlatAffineSectionOpenWaldhausen j).cof
      (boundedAboveFlatAffineSectionOpenWaldhausen j).weq
      (boundedAboveFlatAffineSectionEquivalence R).inverse :=
  Structure.withInverseImageWeak_inverse_exact (boundedAboveFlatAffineSectionEquivalence R)
    (boundedAboveFlatAffineOriginalEvaluation_exact R)
    (boundedAboveFlatAffineSectionEquivalence_inverse_exact R) (boundedAboveFlatPerfectOpenNested j)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionOpenEquivalence.lean:31-38"
  "adaptation" "Actual inherited-zero evaluation, original maps and their complete comparison"]
  boundedAboveFlatAffineSectionOpenEquivalence_inverse_exact

end AlgebraicGeometry.Scheme.Modules
