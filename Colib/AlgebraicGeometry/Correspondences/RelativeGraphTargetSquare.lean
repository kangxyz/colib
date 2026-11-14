/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphLift

/-!
# The actual target-map square of relative graphs

This square is the input to native finite
support pushforward for target naturality. No cycle naturality is assumed.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable (U : SmoothSite (Spec (CommRingCat.of k)))
variable {Y Z : SmoothSite (Spec (CommRingCat.of k))}

/-- Retaining the source coordinate commutes with the literal target map. -/
theorem ambientLift_graphTargetMap (g : Y ⟶ Z) :
    ambientLift k U Y ≫ graphTargetMap k U (SmoothSite.productMap (𝟙 U) g) =
      graphTargetMap k U g ≫ ambientLift k U Z := by
  apply pullback.hom_ext
  · simp [graphTargetMap, ambientLift, pullbackSymmetry_hom_comp_fst]
  · simp only [Category.assoc, SmoothSite.product_hom, ambientLift_snd]
    apply pullback.hom_ext <;>
      simp [graphTargetMap, SmoothSite.productMap, SmoothSite.productLift,
        SmoothSite.productFst, SmoothSite.productSnd, ambientLift]

end AlgebraicGeometry.Cor.RelativeGraph
