/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.KTheory.Waldhausen.Iterated.SimplexFamilyStructure

/-!
# Exact realization of iterated S-simplex families

The realized higher parameter remains independent of the original structure-loop coordinate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor MonoidalCategory
open scoped Simplicial Topology unitInterval

universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet

variable {V W : WideSubcategory preservesZero.{u}} {k : ℕ}

/-- Realize exactly the full finite higher-parameter natural transformation. -/
def stageSimplexRealization (r : ℕ) (S : ModelSimplex V W k) :
    C(stageSpace r V × |(Δ[k] : SSet.{u})|, stageSpace r W) :=
  realizationSimplexFamily (stageTransformationSimplex r S)

/-- The original suspension time is held fixed by the realized simplex expansion. -/
@[colib_ref "quillen" "Quillen/Waldhausen/SConstruction/Iterated/SimplexFamily.lean:216-224"
  "adaptation" "The realized original structure loop retains its independent time."]
theorem stageSimplexRealization_structure (r : ℕ)
    (S : ModelSimplex V W k) (z : |(Δ[k] : SSet.{u})|) (t : unitInterval)
    (x : stageSpace r V) :
    stageSimplexRealization (r + 1) S (stageLoopMap r V x t, z) =
      stageLoopMap r W (stageSimplexRealization r S (x, z)) t :=
  realizationSimplexFamily_interchange (stageTransformationSimplex r S)
    (stageTransformationSimplex (r + 1) S) (stageHomotopy r V) (stageHomotopy r W)
    (stageTransformationSimplex_structure r S) z t x

/-- Every simplex of the parameter holds the original chosen vertex fixed. -/
theorem stageTransformationSimplex_fixed_vertex (r : ℕ) (S : ModelSimplex V W k) :
    SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[k] ≫ stageTransformationSimplex r S =
      CartesianMonoidalCategory.fst Δ[0] Δ[k] ≫ SSet.yonedaEquiv.symm (stageVertex r W) := by
  ext n z : 4
  change stageSimplexFunction r S n
    (((stages r).obj V).map z.1.down.op (stageVertex r V)) z.2 =
      ((stages r).obj W).map z.1.down.op (stageVertex r W)
  have hz : z.1.down = n.unop.const ⦋0⦌ 0 :=
    @Subsingleton.elim (n.unop ⟶ ⦋0⦌) inferInstance _ _
  rw [hz]
  exact stageSimplexFunction_zeroSimplex r S n z.2

/-- The original base point stays fixed throughout the realized family. -/
theorem stageSimplexRealization_fixed_point (r : ℕ)
    (S : ModelSimplex V W k) (z : |(Δ[k] : SSet.{u})|) :
    stageSimplexRealization r S (stagePoint r V, z) = stagePoint r W := by
  let p := (realizationProductSimplexIso (Δ[0] : SSet.{u}) k).inv (default, z)
  have hn := ConcreteCategory.congr_hom
    (realizationProductSimplexIso_inv_whisker (SSet.yonedaEquiv.symm (stageVertex r V)) k)
    (default, z)
  change SSet.toTop.map (SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[k]) p =
    (realizationProductSimplexIso ((stages r).obj V) k).inv (stagePoint r V, z) at hn
  change SSet.toTop.map (stageTransformationSimplex r S)
    ((realizationProductSimplexIso ((stages r).obj V) k).inv (stagePoint r V, z)) = _
  rw [← hn]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[k]) ≫
    SSet.toTop.map (stageTransformationSimplex r S)) p = _
  rw [← Functor.map_comp, stageTransformationSimplex_fixed_vertex,
    Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map (CartesianMonoidalCategory.fst Δ[0] Δ[k]) p) default]
  rfl

end CategoryTheory.Waldhausen.IteratedS
