/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleRightFirst
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleWhiskering
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumTripleTracks
public import Colib.Topology.Prespectrum.ScalarTripleEvaluation

/-!
# The full evaluation of the original split pullback comparison

The six ordered triangle faces, with reverse left middle followed by right middle,
give the five scalar inputs for the same native relative homotopy. Adapted from
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TripleNativeEvaluation.lean:25-50`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex

open BoundedFlatPerfectSplitTripleParameters

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The actual scalar parameters evaluate to the whole split comparison, including level zero. -/
theorem comparison_native_evaluation (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (BoundedFlatPerfectTripleSimplex.structureOn T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (comparisonParameter (r, s), x) =
      (boundedAboveFlatPerfectTripleTrackComparison f g h).level n (r, (s, x)) := by
  unfold comparisonParameter boundedAboveFlatPerfectTripleTrackComparison
  exact Homotopy.RelHomotopy.scalar_triple_evaluation
    (E := originalPrespectrum (BoundedFlatPerfectTripleSimplex.structureOn T))
    (F := originalPrespectrum (BoundedFlatPerfectTripleSimplex.structureOn X))
    n (fun z x ↦ prespectrumSimplexFamily (simplex f g h) n (z, x))
    leftFirstParameter leftSecondParameter
    (normalizedLeftParameter.symm.trans normalizedRightParameter)
    rightFirstParameter rightSecondParameter
    (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap (Category.assoc f g h))
    (Category.assoc _ _ _).symm
    (boundedAboveFlatPerfectNormalizedCompTrackComparison f (g ≫ h))
    ((boundedAboveFlatPerfectNormalizedCompTrackComparison g h).postcomp
      (boundedAboveFlatPerfectPullbackPrespectrumMap f))
    (boundedAboveFlatPerfectNormalizedCompTrackComparison (f ≫ g) h)
    (Homotopy.RelHomotopy.precomp (boundedAboveFlatPerfectPullbackPrespectrumMap h)
      (boundedAboveFlatPerfectNormalizedCompTrackComparison f g))
    (boundedAboveFlatPerfectNormalizedTripleTrackComparison f g h)
    (leftFirst_native f g h n) (leftSecond_native f g h n) (normalized_native_comparison f g h n)
    (rightFirst_native f g h n) (rightSecond_native f g h n) r s x

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex
