/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSquareFivePath
public import Colib.Topology.Path.ScalarPathCells

/-! The four actual ordered edge images of the original reverse-forward five-node square path. -/
@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Topology Path.CarrierHalfPaths
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectNativeSquareFiveSimplex

/-- Each primitive edge occurs in the given order inside its actual five-node reference. -/
def edgeFace (i : Fin 4) : ⦋1⦌ ⟶ ⦋4⦌ :=
  SimplexCategory.Hom.mk ⟨![![0, 1, 0, 3] i, ![1, 2, 3, 4] i],
    by fin_cases i <;> decide⟩

/-- Every value of the original nested path belongs to one of its four actual edges. -/
theorem square_path_in (s : unitInterval) :
    ∃ (i : Fin 4) (z : StdSimplex ℝ (Fin 2)),
      StdSimplex.map (edgeFace i).toOrderHom z = parameter s := by
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [parameter, path_lower]
    rw [Path.symm_apply, Function.comp_apply]
    rcases cover (unitInterval.symm t) with ⟨r, hr⟩ | ⟨r, hr⟩
    · rw [← hr, binaryPath, path_lower]
      exact ⟨0, edge 0 1 r, map_edge (edgeFace 0) 0 1 r⟩
    · rw [← hr, binaryPath, path_upper]
      exact ⟨1, edge 0 1 r, map_edge (edgeFace 1) 0 1 r⟩
  · rw [parameter, path_upper]
    rcases cover t with ⟨r, rfl⟩ | ⟨r, rfl⟩
    · rw [binaryPath, path_lower]
      exact ⟨2, edge 0 1 r, map_edge (edgeFace 2) 0 1 r⟩
    · rw [binaryPath, path_upper]
      exact ⟨3, edge 0 1 r, map_edge (edgeFace 3) 0 1 r⟩

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectNativeSquareFiveSimplex
