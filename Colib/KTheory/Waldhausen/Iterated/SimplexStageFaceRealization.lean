/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/

module

public import Colib.KTheory.Waldhausen.Iterated.SimplexStageSpecifications
public import Colib.Topology.ClassifyingSpace.FunctorChain

/-!
# Realization of the original iterated S-simplex faces

The realized face uses the actual subchain, via inverse product-simplex naturality.

Adapted from Quillen/Waldhausen/SConstruction/Iterated/SimplexFaces.lean:134-154
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

/-- Every geometric simplex face realizes the exact original subchain family. -/
theorem stageSimplexRealization_face (r : ℕ)
    {V W : WideSubcategory preservesZero.{u}} {k l : ℕ}
    (S : ModelSimplex V W k) (α : ⦋l⦌ ⟶ ⦋k⦌)
    (x : stageSpace r V) (z : |(Δ[l] : SSet.{u})|) :
    stageSimplexRealization r S (x, SSet.toTop.map (SSet.stdSimplex.map α) z) =
      stageSimplexRealization r (S.face α) (x, z) := by
  have hp := ConcreteCategory.congr_hom
    (realizationProductSimplexIso_inv_naturality (𝟙 ((stages r).obj V)) α) (x, z)
  have hv : (SSet.toTop.map (𝟙 ((stages r).obj V)) ⊗ₘ
      SSet.toTop.map (SSet.stdSimplex.map α)) (x, z) =
      (x, SSet.toTop.map (SSet.stdSimplex.map α) z) := by simp
  rw [TopCat.comp_app, TopCat.comp_app, hv] at hp
  change SSet.toTop.map (stageTransformationSimplex r S)
    ((realizationProductSimplexIso ((stages r).obj V) k).inv
      (x, SSet.toTop.map (SSet.stdSimplex.map α) z)) = _
  rw [← hp]
  change (SSet.toTop.map ((𝟙 ((stages r).obj V)) ⊗ₘ SSet.stdSimplex.map α) ≫
    SSet.toTop.map (stageTransformationSimplex r S))
      ((realizationProductSimplexIso ((stages r).obj V) l).inv (x, z)) = _
  rw [← Functor.map_comp, stageTransformationSimplex_face]
  rfl

end CategoryTheory.Waldhausen.IteratedS
