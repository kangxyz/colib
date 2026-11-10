/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineEvaluationComparison
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty

/-!
# Complete weakness of the actual affine evaluation at every level

The existing evaluation map has the already constructed normalized homotopy inverse.
Its entire level map is therefore a weak equivalence, including the zeroth level.
-/
@[expose] public noncomputable section

open Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual section evaluation is completely weak at every original level. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/SectionSpectrumEquivalence.lean:79-89"
  "adaptation" "Complete weakness from the existing actual evaluation level homotopy equivalence"]
theorem boundedAboveFlatAffineEvaluation_level_isWeakHomotopyEquivalence
    (R : CommRingCat.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((boundedAboveFlatAffineEvaluationPrespectrumMap R).map n) :=
  isWeakHomotopyEquivalence_of_homotopyEquiv
    (boundedAboveFlatAffineEvaluationLevelEquiv R n)

end AlgebraicGeometry.Scheme.Modules
