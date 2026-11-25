/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleEvaluation
public import Colib.KTheory.Waldhausen.Iterated.SimplexPathEmbedding

/-! The literal split binary path in its original normalization triangle. -/
/-! Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/BinaryNativePath.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBinarySimplex

/-- Both native normalization pieces remain in the binary path, at every original level. -/
theorem native_path {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) (t : unitInterval)
    (x : (originalPrespectrum (BoundedFlatPerfectTripleSimplex.structureOn Z)).space n) :
    prespectrumSimplexFamily (simplex f g) n (binaryPath (k := 2) 0 1 2 t, x) =
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g).level n (t, x) := by
  have h := (whole_triangle f g n 1 t x).trans (native_apply f g n 1 t x).symm
  rw [CategoryTheory.TheoremB.compositionTriangleHomotopy.apply_one] at h
  exact h.trans
    (((boundedAboveFlatPerfectNormalizedCompTrackComparison f g).level n).apply_one (t, x))

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectBinarySimplex
