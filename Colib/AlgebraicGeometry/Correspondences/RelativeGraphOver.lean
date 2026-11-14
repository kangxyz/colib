/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphProjection

/-!
# Explicit relative graph over a source morphism

The map retains (v,f(v),y), with a literal
retraction forgetting f(v). No source naturality of correspondences is assumed.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {V U Y : SmoothSite (Spec (CommRingCat.of k))}

/-- The actual (v,y) |-> (v,(f(v),y)) map. -/
def ambientOver (f : V ⟶ U) : (SmoothSite.product V Y).left ⟶
    pullback V.hom (SmoothSite.product U Y).hom :=
  ambientLift k V Y ≫ graphTargetMap k V (SmoothSite.productMap f (𝟙 Y))

/-- Forget the retained U coordinate. -/
def ambientForget : pullback V.hom (SmoothSite.product U Y).hom ⟶
    (SmoothSite.product V Y).left :=
  graphTargetMap k V (SmoothSite.productSnd U Y)

/-- The graph has a genuine scheme-theoretic retraction. -/
theorem ambientOver_forget (f : V ⟶ U) :
    ambientOver k (Y := Y) f ≫ ambientForget k = 𝟙 (SmoothSite.product V Y).left := by
  apply pullback.hom_ext
  · simp [ambientOver, ambientForget, graphTargetMap, SmoothSite.product_hom]
  · simp [ambientOver, ambientForget, graphTargetMap, SmoothSite.product_hom,
      SmoothSite.productMap, SmoothSite.productSnd, SmoothSite.productLift]

/-- It is a closed graph, not merely an injective map on underlying points. -/
instance ambientOver_isClosedImmersion (f : V ⟶ U) :
    IsClosedImmersion (ambientOver k (Y := Y) f) := by
  let p := ambientForget k (V := V) (U := U) (Y := Y)
  have : IsSeparated (p ≫ pullback.fst V.hom Y.hom) := by
    change IsSeparated (ambientForget k ≫ pullback.fst V.hom Y.hom)
    rw [ambientForget, graphTargetMap_fst]
    infer_instance
  have : IsSeparated p := IsSeparated.of_comp p (pullback.fst V.hom Y.hom)
  have : IsClosedImmersion (ambientOver k (Y := Y) f ≫ p) := by
    rw [ambientOver_forget]
    infer_instance
  exact IsClosedImmersion.of_comp _ p

end AlgebraicGeometry.Cor.RelativeGraph
