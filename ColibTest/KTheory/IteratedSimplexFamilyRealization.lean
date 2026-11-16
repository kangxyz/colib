module

public import Colib.KTheory.Waldhausen.Iterated.SimplexFamilyRealization

set_option autoImplicit false

@[expose] public noncomputable section

open CategoryTheory
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial Topology unitInterval

universe u

namespace ColibTest.IteratedSimplexFamilyRealization

variable {V W : WideSubcategory preservesZero.{u}}

/-- An entire realized three-simplex and a separate suspension time coexist unchanged. -/
theorem realized_cube_structure (r : ℕ) (S : ModelSimplex V W 3)
    (z : |(Δ[3] : SSet.{u})|) (t : unitInterval) (x : stageSpace r V) :
    stageSimplexRealization (r + 1) S (stageLoopMap r V x t, z) =
      stageLoopMap r W (stageSimplexRealization r S (x, z)) t :=
  stageSimplexRealization_structure r S z t x

/-- The same cubic family fixes the original realized zero in every stage. -/
theorem realized_cube_point (r : ℕ) (S : ModelSimplex V W 3) (z : |(Δ[3] : SSet.{u})|) :
    stageSimplexRealization r S (stagePoint r V, z) = stagePoint r W :=
  stageSimplexRealization_fixed_point r S z

end ColibTest.IteratedSimplexFamilyRealization
