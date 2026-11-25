/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Colib.KTheory.Waldhausen.Iterated.SimplexPathEmbedding
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleParameters
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareMergedSimplex

/-!
# Scalar paths in the actual merged double-square diagram

The three original split-triple homotopies lift with their literal four-edge boundary
paths. The ten routes retain their order and original intermediate vertices.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/DoubleSquareScalarPaths.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Topology
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths

/-- The embedded left scalar path follows the two original binary paths. -/
theorem map_splitLeft {k : ℕ} (α : ⦋7⦌ ⟶ ⦋k⦌) (t : unitInterval) :
    embed α (BoundedFlatPerfectSplitTripleParameters.splitLeftPath t) =
      ((binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2)).trans
        (binaryPath (α.toOrderHom 2) (α.toOrderHom 3) (α.toOrderHom 7))) t :=
  map_trans_values _ _ _ _ _ (map_binaryPath α 0 1 2) (map_binaryPath α 2 3 7) t

/-- The embedded right scalar path follows the two original binary paths. -/
theorem map_splitRight {k : ℕ} (α : ⦋7⦌ ⟶ ⦋k⦌) (t : unitInterval) :
    embed α (BoundedFlatPerfectSplitTripleParameters.splitRightPath t) =
      ((binaryPath (α.toOrderHom 0) (α.toOrderHom 4) (α.toOrderHom 5)).trans
        (binaryPath (α.toOrderHom 5) (α.toOrderHom 6) (α.toOrderHom 7))) t :=
  map_trans_values _ _ _ _ _ (map_binaryPath α 0 4 5) (map_binaryPath α 5 6 7) t

/-- The binary scalar route `0 → 1 → 2` for the source total normalization. -/
abbrev sourceTotal := binaryPath (k := 17) 0 1 2
/-- The binary scalar route `2 → 3 → 11` for the source chart normalization. -/
abbrev sourceChart := binaryPath (k := 17) 2 3 11
/-- The binary scalar route `0 → 8 → 9` to the first intermediate vertex. -/
abbrev firstIntermediate := binaryPath (k := 17) 0 8 9
/-- The binary scalar route `9 → 10 → 11` for the first restriction. -/
abbrev firstRestriction := binaryPath (k := 17) 9 10 11
/-- The binary scalar route `0 → 4 → 5` for the middle total normalization. -/
abbrev middleTotal := binaryPath (k := 17) 0 4 5
/-- The binary scalar route `5 → 6 → 13` for the middle chart normalization. -/
abbrev middleChart := binaryPath (k := 17) 5 6 13
/-- The binary scalar route `9 → 12 → 13` for the second restriction. -/
abbrev secondRestriction := binaryPath (k := 17) 9 12 13
/-- The binary scalar route `0 → 14 → 15` for the target total normalization. -/
abbrev targetTotal := binaryPath (k := 17) 0 14 15
/-- The binary scalar route `15 → 16 → 17` for the target chart normalization. -/
abbrev targetChart := binaryPath (k := 17) 15 16 17
/-- The binary scalar route `5 → 7 → 17` for the last restriction. -/
abbrev lastRestriction := binaryPath (k := 17) 5 7 17

/-- The split-triple homotopy comparing the source total/chart route with the first
intermediate/restriction route. -/
def firstComparison : (sourceTotal.trans sourceChart).Homotopy
    (firstIntermediate.trans firstRestriction) :=
  Path.Homotopy.mapOfPaths (embed BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace)
    BoundedFlatPerfectSplitTripleParameters.comparisonParameter _ _
    (map_splitLeft BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace)
    (map_splitRight BoundedFlatPerfectDoubleSquareMergedSimplex.firstFace)

/-- The split-triple homotopy comparing the middle total/chart route with the
first-intermediate/second-restriction route. -/
def middleComparison : (middleTotal.trans middleChart).Homotopy
    (firstIntermediate.trans secondRestriction) :=
  Path.Homotopy.mapOfPaths (embed BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace)
    BoundedFlatPerfectSplitTripleParameters.comparisonParameter _ _
    (map_splitLeft BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace)
    (map_splitRight BoundedFlatPerfectDoubleSquareMergedSimplex.middleFace)

/-- The split-triple homotopy comparing the middle-total/last-restriction route with the target
total/chart route. -/
def lastComparison : (middleTotal.trans lastRestriction).Homotopy
    (targetTotal.trans targetChart) :=
  Path.Homotopy.mapOfPaths (embed BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace)
    BoundedFlatPerfectSplitTripleParameters.comparisonParameter _ _
    (map_splitLeft BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace)
    (map_splitRight BoundedFlatPerfectDoubleSquareMergedSimplex.lastFace)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectDoubleSquareScalarPaths
