/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleSimplex
public import Colib.KTheory.Waldhausen.Iterated.SimplexParameterPaths

/-!
# The six original parameter faces of the split pullback triple

The shared eight-vertex simplex retains the original affine edge and triangle parameters.
The middle input reverses its left triangle before traversing the right one, and the
two outer pairs retain their separate horizontal pasting.

Adapted from `SplitTripleParameters.lean:24–56` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory Convexity Topology
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleParameters

open SimplexParameters BoundedFlatPerfectSplitTripleSimplex

/-- The scalar triangle on vertices `0, 1, 2` for the first left split-triple comparison. -/
def leftFirstParameter := triangle (k := 7) (triangleFace 0 1 2 (by decide) (by decide))
/-- The scalar triangle on vertices `2, 3, 7` for the second left split-triple comparison. -/
def leftSecondParameter := triangle (k := 7) (triangleFace 2 3 7 (by decide) (by decide))
/--
The scalar triangle on vertices `0, 2, 7` for the normalized left triple-composition comparison.
-/
def normalizedLeftParameter := triangle (k := 7) (triangleFace 0 2 7 (by decide) (by decide))
/-- The scalar triangle on vertices `0, 4, 5` for the first right split-triple comparison. -/
def rightFirstParameter := triangle (k := 7) (triangleFace 0 4 5 (by decide) (by decide))
/-- The scalar triangle on vertices `5, 6, 7` for the second right split-triple comparison. -/
def rightSecondParameter := triangle (k := 7) (triangleFace 5 6 7 (by decide) (by decide))
/--
The scalar triangle on vertices `0, 5, 7` for the normalized right triple-composition
comparison.
-/
def normalizedRightParameter := triangle (k := 7) (triangleFace 0 5 7 (by decide) (by decide))

/-- The fully split left path has precisely the old two-by-two association. -/
def splitLeftPath : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 8)) (StdSimplex.single 7) :=
  ((edge 0 1).trans (edge 1 2)).trans ((edge 2 3).trans (edge 3 7))

/-- The fully split right path retains its separate pair of old binary comparisons. -/
def splitRightPath : Path (StdSimplex.single 0 : StdSimplex ℝ (Fin 8)) (StdSimplex.single 7) :=
  ((edge 0 4).trans (edge 4 5)).trans ((edge 5 6).trans (edge 6 7))

/-- An explicit compatible scalar lift candidate of the full old split-triple surface.
The six whole native triangle identities below are its geometric inputs. -/
def comparisonParameter : splitLeftPath.Homotopy splitRightPath :=
  (leftFirstParameter.hcomp leftSecondParameter).symm.trans
    ((normalizedLeftParameter.symm.trans normalizedRightParameter).trans
      (rightFirstParameter.hcomp rightSecondParameter))

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleParameters
