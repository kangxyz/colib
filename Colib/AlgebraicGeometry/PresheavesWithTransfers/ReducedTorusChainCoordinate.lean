/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusTensorCoordinate
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusChainParameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.ParameterProduct

/-! # The original singular parameter map is the actual AW right-leg evaluation

This identifies the original chain parameter map in every degree, with its
literal last-factor swap. It does not invert AW or interchange signed shifts.
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

/-- Evaluating the original chain pairing on the universal parameter coordinate
recovers the original singular parameter map, including the simplex-factor swap. -/
theorem reducedTorusPresheafChainPairing_coordinate
    (U : SmoothSite (Spec (CommRingCat.of k))) (q n : ℕ)
    (s : sections (reducedTorus k q)
      (Cor.mk (SmoothSite.product U (AlgebraicSimplex.smoothSiteObj k n)))) :
    let G := SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
    let D := AlgebraicSimplex.smoothSiteObj k n
    let V := SmoothSite.product (SmoothSite.product U G) D
    let f := SmoothSite.productMap (SmoothSite.productFst U G) (𝟙 D)
    let g := SmoothSite.productFst (SmoothSite.product U G) D ≫ SmoothSite.productSnd U G
    (((reducedTorusPresheafChainPairing k q).f n).app
      (op (SmoothSite.product U G))).hom
        (transfer (reducedTorus k q) ((Cor.graphFunctor k).map f) s ⊗ₜ[ℤ]
          ((toReducedTorus k 1).hom.app (op (Cor.mk V))
            (ULift.up ((Cor.graphFunctor k).map
              (g ≫ (SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))).inv))))) =
      ((reducedTorusSingularParameterProduct k q).f n).app (op U) s := by
  intro G D V f g
  rw [reducedTorusSingularParameterProduct_f_app]
  change reducedTorusSectionTensorMap k V q _ =
    transfer (reducedTorus k (q + 1))
      ((Cor.graphFunctor k).map (SmoothSite.productSwapLast U G D))
      ((reducedTorusParameterProduct k q).hom.app
        (op (Cor.mk (SmoothSite.product U D))) s)
  have hp : SmoothSite.productLift f g = SmoothSite.productSwapLast U G D := by
    apply SmoothSite.product_hom_ext
    · apply SmoothSite.product_hom_ext <;> simp [f, SmoothSite.productSwapLast]
    · simp [g, SmoothSite.productSwapLast]
  simpa only [hp] using reducedTorusSectionTensorMap_coordinate k f g q s

end AlgebraicGeometry.PresheafWithTransfers
