/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumBinaryPath
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareFiveSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareTrackOriginal
public import Colib.KTheory.Waldhausen.Iterated.SimplexLiftOperations

/-!
# The actual square track in the five-node family

Adapted from `NativeSquareFiveSimplex.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Convexity Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectNativeSquareFiveSimplex

variable {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
  (h : p ≫ v = q ≫ w)

/-- The first literal two-piece normalization path. -/
theorem first_path : PathLift (simplex p v q w h) (binaryPath 0 1 2)
    (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy p v) := by
  intro n t x
  have he := map_binaryPath firstFace 0 1 2 t
  change StdSimplex.map firstFace.toOrderHom (binaryPath (k := 2) 0 1 2 t) =
    binaryPath (k := 4) 0 1 2 t at he
  rw [← he, prespectrumSimplexFamily_face, first_face]
  exact BoundedFlatPerfectBinarySimplex.native_path p v n t x

/-- The second literal path, with the same endpoint cast as the original exported square. -/
theorem second_path : PathLift (simplex p v q w h) (binaryPath 0 3 4)
    ((boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy q w).cast
      (congrArg boundedAboveFlatPerfectPullbackPrespectrumMap h).symm rfl) := by
  intro n t x
  have he := map_binaryPath secondFace 0 1 2 t
  change StdSimplex.map secondFace.toOrderHom (binaryPath (k := 2) 0 1 2 t) =
    binaryPath (k := 4) 0 3 4 t at he
  rw [← he, prespectrumSimplexFamily_face, second_face]
  exact BoundedFlatPerfectBinarySimplex.native_path q w n t x

/-- The unchanged original reversed first binary path followed by the second. -/
def parameter : Path (StdSimplex.single 2 : StdSimplex ℝ (Fin 5)) (StdSimplex.single 4) :=
  (binaryPath 0 1 2).symm.trans (binaryPath 0 3 4)

/-- The whole original exported square homotopy is this exact scalar path, at every level. -/
theorem native : PathLift (simplex p v q w h) parameter
    (boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy p v q w h) := by
  rw [boundedAboveFlatPerfectPullbackPrespectrumSquareHomotopy_eq]
  exact PathLift.trans _ (PathLift.symm _ (first_path p v q w h)) (second_path p v q w h)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectNativeSquareFiveSimplex
