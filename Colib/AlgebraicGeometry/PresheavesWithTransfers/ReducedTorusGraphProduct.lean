/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusParameter
import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry

/-!
# Exterior multiplication by a torus graph

The original parameter product can be specialized along any smooth-site
map to the native torus. On a represented section the operation is the
exterior product with the identity of the torus, pulled back along that
map in the parameter variable. For a structural graph in weight zero
the result is the reduced graph of the specified torus coordinate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₘ" => multiplicativeGroupObject Sₖ

/-- Specialize the actual reduced parameter product along a map to the torus. -/
def reducedTorusGraphProduct (q : ℕ) (X : Cor k) {Y : SmoothSite Sₖ} (a : Y ⟶ Gₘ) :
    sections (reducedTorus k q) X ⟶
      sections (reducedTorus k (q + 1)) (Cor.mk (product X.toSmoothSite Y)) :=
  (reducedTorusParameterProduct k q).hom.app (op X) ≫
    transfer (reducedTorus k (q + 1))
      ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) a))

/-- The specialization retains the original signed coefficient and graph of the product map. -/
theorem reducedTorusGraphProduct_apply (q : ℕ) (X : Cor k) {Y : SmoothSite Sₖ}
    (a : Y ⟶ Gₘ) (α : X ⟶ Cor.mk (torusPower Sₖ q)) :
    reducedTorusGraphProduct k q X a
      ((toReducedTorus k q).hom.app (op X) (ULift.up α)) =
      (toReducedTorus k (q + 1)).hom.app (op (Cor.mk (product X.toSmoothSite Y)))
        (ULift.up ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) a) ≫
          (Cor.parameterProduct Gₘ).map α ≫
          (Cor.graphFunctor k).map (torusPowerParameterSwap Sₖ q))) := by
  rw [reducedTorusGraphProduct, ConcreteCategory.comp_apply, reducedTorusParameterProduct_apply]
  let G := Cor.graphFunctor k
  let T := Cor.mk (product X.toSmoothSite Gₘ)
  let W := Cor.mk (product X.toSmoothSite Y)
  let g : W ⟶ T := G.map (SmoothSite.productMap (𝟙 X.toSmoothSite) a)
  let β : T ⟶ Cor.mk (torusPower Sₖ (q + 1)) :=
    (Cor.parameterProduct Gₘ).map α ≫ G.map (torusPowerParameterSwap Sₖ q)
  exact reducedTorus_transfer_apply k (q + 1) g β

/-- Restriction of the geometric parameter commutes with the original product. -/
@[reassoc]
theorem reducedTorusGraphProduct_naturality (q : ℕ) (X : Cor k)
    {Y Z : SmoothSite Sₖ} (f : Y ⟶ Z) (a : Z ⟶ Gₘ) :
    reducedTorusGraphProduct k q X a ≫ transfer (reducedTorus k (q + 1))
        ((Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 X.toSmoothSite) f)) =
      reducedTorusGraphProduct k q X (f ≫ a) := by
  let G := Cor.graphFunctor k
  let P := reducedTorus k (q + 1)
  let T := Cor.mk (product X.toSmoothSite Gₘ)
  let g : Cor.mk (product X.toSmoothSite Y) ⟶ Cor.mk (product X.toSmoothSite Z) :=
    G.map (SmoothSite.productMap (𝟙 X.toSmoothSite) f)
  let b : Cor.mk (product X.toSmoothSite Z) ⟶ T :=
    G.map (SmoothSite.productMap (𝟙 X.toSmoothSite) a)
  let c : Cor.mk (product X.toSmoothSite Y) ⟶ T :=
    G.map (SmoothSite.productMap (𝟙 X.toSmoothSite) (f ≫ a))
  have hc : g ≫ b = c := by
    change G.map _ ≫ G.map _ = G.map _
    rw [← G.map_comp, ← SmoothSite.productMap_comp, Category.id_comp]
  change ((reducedTorusParameterProduct k q).hom.app (op X) ≫ transfer P b) ≫
    transfer P g = (reducedTorusParameterProduct k q).hom.app (op X) ≫ transfer P c
  rw [Category.assoc, ← transfer_comp, hc]

/-- The identity graph recovers the original parameter action. -/
theorem reducedTorusGraphProduct_id (q : ℕ) (X : Cor k) :
    reducedTorusGraphProduct k q X (𝟙 Gₘ) =
      (reducedTorusParameterProduct k q).hom.app (op X) := by
  let G := Cor.graphFunctor k
  let P := reducedTorus k (q + 1)
  let T := Cor.mk (product X.toSmoothSite Gₘ)
  let g : T ⟶ T := G.map (SmoothSite.productMap (𝟙 X.toSmoothSite) (𝟙 Gₘ))
  have hg : g = 𝟙 T := by
    change G.map _ = _
    rw [SmoothSite.productMap_id]
    exact G.map_id _
  change (reducedTorusParameterProduct k q).hom.app (op X) ≫ transfer P g =
    (reducedTorusParameterProduct k q).hom.app (op X)
  rw [hg, transfer_id]
  let f : sections (reducedTorus k q) X ⟶ sections P T :=
    (reducedTorusParameterProduct k q).hom.app (op X)
  exact Category.comp_id f

/-- The graph of the actual multiplicative basepoint acts by zero. -/
theorem reducedTorusGraphProduct_torusOne (q : ℕ) (X : Cor k) :
    reducedTorusGraphProduct k q X (torusOne Sₖ) = 0 := by
  have h := congrArg (fun η => η.hom.app (op X))
    (reducedTorusParameterProduct_parameterPullback_one k q)
  exact h

/-- The structural graph in weight zero acts on a torus graph by pulling
back that very graph along the second projection. -/
theorem reducedTorusGraphProduct_apply_structure (X Y : SmoothSite Sₖ) (a : Y ⟶ Gₘ) :
    reducedTorusGraphProduct k 0 (Cor.mk X) a
      ((toReducedTorus k 0).hom.app (op (Cor.mk X))
        (ULift.up ((Cor.graphFunctor k).map (Contraction.toBase X)))) =
      (toReducedTorus k 1).hom.app (op (Cor.mk (product X Y)))
        (ULift.up ((Cor.graphFunctor k).map
          (productSnd X Y ≫ a ≫ (torusPowerOneIso Sₖ).inv))) := by
  rw [reducedTorusGraphProduct_apply, Cor.parameterProduct_graph, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2
  apply (Cor.graphFunctor k).congr_map
  apply torusPower_hom_ext Sₖ 1
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have h : (torusPowerOneIso Sₖ).inv ≫ torusCoordinate Sₖ 1 0 = 𝟙 _ :=
    (torusPowerOneIso Sₖ).inv_hom_id
  simp only [Category.assoc, torusPowerParameterSwap_coordinate_zero, SmoothSite.productMap_snd,
    Category.comp_id, h]

end AlgebraicGeometry.PresheafWithTransfers
