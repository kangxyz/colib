/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusTensorParameter
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusPresheafAW

/-! # The parameter formula for the actual AW right leg -/
@[expose] public noncomputable section
open CategoryTheory Opposite AlgebraicGeometry.Scheme
open scoped TensorProduct
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]

/-- The actual chain pairing (the right leg of the AW span) has the parameter formula in every
chain degree, before applying an AW inverse. -/
theorem reducedTorusPresheafChainPairing_parameter
    (U : SmoothSite (Spec (CommRingCat.of k))) (q : ℕ) (n : ℕ)
    (s : sections (reducedTorus k q)
      (Cor.mk (SmoothSite.product U
        ((AlgebraicSimplex.cosimplicialSmoothSite k).obj (SimplexCategory.mk n)))))
    (r : Cor.mk (SmoothSite.product U
      ((AlgebraicSimplex.cosimplicialSmoothSite k).obj (SimplexCategory.mk n))) ⟶
        Cor.mk (SmoothSite.torusPower (Spec (CommRingCat.of k)) 1)) :
    let V := SmoothSite.product U
      ((AlgebraicSimplex.cosimplicialSmoothSite k).obj (SimplexCategory.mk n))
    (((reducedTorusPresheafChainPairing k q).f n).app (op U)).hom
      (s ⊗ₜ[ℤ] ((toReducedTorus k 1).hom.app (op (Cor.mk V)) (ULift.up r))) =
        transfer (reducedTorus k (q + 1))
          (Cor.RelativeGraph.relativeGraphLift k V _
            (r ≫ (Cor.graphFunctor k).map
              (SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))).hom))
          ((reducedTorusParameterProduct k q).hom.app (op (Cor.mk V)) s) := by
  exact reducedTorusSectionTensorMap_parameter k _ q s r

end AlgebraicGeometry.PresheafWithTransfers
