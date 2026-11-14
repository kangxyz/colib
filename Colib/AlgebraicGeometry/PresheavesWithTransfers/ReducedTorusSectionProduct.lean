/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphTargetNaturality
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusParameter

/-!
# Bilinear section products and the parameter unit axis

Apply the original reduced torus parameter map and pull back along the
canonical relative graph of an actual signed correspondence. The product is
additive in both inputs and kills every unit-axis correspondence. No source
naturality or singular chain multiplication is asserted.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry.Scheme
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
open Cor.RelativeGraph
variable (k : Type u) [Field k]
local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
variable (U : SmoothSite (Spec (CommRingCat.of k)))

/-- A true section product from the actual parameter map and relative graph. -/
def reducedTorusSectionProduct (q : ℕ) :
    sections (reducedTorus k q) (Cor.mk U) → (Cor.mk U ⟶ Cor.mk G) →
      sections (reducedTorus k (q + 1)) (Cor.mk U) := by
  intro s b
  exact transfer (reducedTorus k (q + 1)) (relativeGraphLift k U G b)
    ((reducedTorusParameterProduct k q).hom.app (op (Cor.mk U)) s)

/-- The section product is additive in its original reduced-torus input. -/
theorem reducedTorusSectionProduct_add_left (q : ℕ)
    (s t : sections (reducedTorus k q) (Cor.mk U)) (b : Cor.mk U ⟶ Cor.mk G) :
    reducedTorusSectionProduct k U q (s + t) b =
      reducedTorusSectionProduct k U q s b + reducedTorusSectionProduct k U q t b := by
  unfold reducedTorusSectionProduct
  rw [map_add, map_add]

/-- The section product retains addition of all signed parameter correspondences. -/
theorem reducedTorusSectionProduct_add_right (q : ℕ)
    (s : sections (reducedTorus k q) (Cor.mk U)) (a b : Cor.mk U ⟶ Cor.mk G) :
    reducedTorusSectionProduct k U q s (a + b) =
      reducedTorusSectionProduct k U q s a + reducedTorusSectionProduct k U q s b := by
  unfold reducedTorusSectionProduct
  rw [map_add, transfer_add]
  rfl

/-- The entire actual unit axis vanishes, including arbitrary signed
correspondences to the base; this is not restricted to a rational point graph. -/
theorem reducedTorusSectionProduct_unit_axis (q : ℕ)
    (s : sections (reducedTorus k q) (Cor.mk U))
    (a : Cor.mk U ⟶ Cor.mk (SmoothSite.base S)) :
    reducedTorusSectionProduct k U q s
      (a ≫ (Cor.graphFunctor k).map (SmoothSite.torusOne S)) = 0 := by
  let P := reducedTorus k (q + 1)
  have h := congrArg (fun f => f.hom.app (op (Cor.mk U)) s)
    (reducedTorusParameterProduct_parameterPullback_one k q)
  have hzero : transfer P
      ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 U) (SmoothSite.torusOne S)))
      ((reducedTorusParameterProduct k q).hom.app (op (Cor.mk U)) s) = 0 := h
  unfold reducedTorusSectionProduct
  rw [relativeGraphLift_comp_graph, transfer_comp]
  change transfer P (relativeGraphLift k U (SmoothSite.base S) a)
    (transfer P ((Cor.graphFunctor k).map
      (SmoothSite.productMap (𝟙 U) (SmoothSite.torusOne S)))
      ((reducedTorusParameterProduct k q).hom.app (op (Cor.mk U)) s)) = 0
  rw [hzero, map_zero]

end AlgebraicGeometry.PresheafWithTransfers
