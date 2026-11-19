/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusTensorParameter
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphGraph

/-! # Evaluation of the actual tensor pairing at a parameter coordinate

The parameter is a genuine smooth map to the multiplicative group. Its
represented reduced weight-one section gives the original parameter map,
not a separately defined multiplication.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- Pairing the pullback of a section with a genuine parameter coordinate is
pullback of the original parameter product along the literal product lift. -/
theorem reducedTorusSectionTensorMap_coordinate
    {U V : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U)
    (g : V ⟶ SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))) (q : ℕ)
    (s : sections (reducedTorus k q) (Cor.mk U)) :
    reducedTorusSectionTensorMap k V q
      (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s ⊗ₜ[ℤ]
        ((toReducedTorus k 1).hom.app (op (Cor.mk V))
          (ULift.up ((Cor.graphFunctor k).map
            (g ≫ (SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))).inv))))) =
      transfer (reducedTorus k (q + 1))
        ((Cor.graphFunctor k).map (SmoothSite.productLift f g))
        ((reducedTorusParameterProduct k q).hom.app (op (Cor.mk U)) s) := by
  let G := SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
  let Q := reducedTorus k (q + 1)
  let η := reducedTorusParameterProduct k q
  rw [reducedTorusSectionTensorMap_parameter, ← Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Cor.RelativeGraph.relativeGraphLift_graph]
  have hn := (NatTrans.naturality_apply η.hom ((Cor.graphFunctor k).map f).op s).symm
  change transfer Q ((Cor.parameterProduct G).map ((Cor.graphFunctor k).map f))
      (η.hom.app (op (Cor.mk U)) s) =
    η.hom.app (op (Cor.mk V))
      (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s) at hn
  rw [Cor.parameterProduct_graph] at hn
  rw [← hn]
  change (transfer Q ((Cor.graphFunctor k).map (SmoothSite.productMap f (𝟙 G))) ≫
    transfer Q ((Cor.graphFunctor k).map (SmoothSite.productLift (𝟙 V) g)))
      (η.hom.app (op (Cor.mk U)) s) = _
  rw [← transfer_comp, ← Functor.map_comp]
  have hp : SmoothSite.productLift (𝟙 V) g ≫ SmoothSite.productMap f (𝟙 G) =
      SmoothSite.productLift f g := by
    dsimp [G]
    apply SmoothSite.product_hom_ext <;> simp
  rw [hp]

end AlgebraicGeometry.PresheafWithTransfers
