/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusSimplicialTensor

/-! # The integral tensor pairing recovers the original parameter product

The actual simplicial tensor pairing, evaluated on a represented weight-one
section, is the original parameter map pulled back along its relative graph.
This is a sectionwise comparison, not yet the shifted derived AW comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry.Scheme
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- On a pure tensor with an original weight-one quotient generator, the
integral tensor pairing is precisely the original relative-graph parameter map. -/
theorem reducedTorusSectionTensorMap_parameter
    (U : SmoothSite (Spec (CommRingCat.of k))) (q : ℕ)
    (s : sections (reducedTorus k q) (Cor.mk U))
    (r : Cor.mk U ⟶ Cor.mk (SmoothSite.torusPower (Spec (CommRingCat.of k)) 1)) :
    reducedTorusSectionTensorMap k U q
      (s ⊗ₜ[ℤ] ((toReducedTorus k 1).hom.app (op (Cor.mk U)) (ULift.up r))) =
        transfer (reducedTorus k (q + 1))
          (Cor.RelativeGraph.relativeGraphLift k U _
            (r ≫ (Cor.graphFunctor k).map
              (SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))).hom))
          ((reducedTorusParameterProduct k q).hom.app (op (Cor.mk U)) s) := by
  change reducedTorusBinarySectionProduct k U q s
    ((toReducedTorus k 1).hom.app (op (Cor.mk U)) (ULift.up r)) = _
  exact reducedTorusBinarySectionProduct_generator k U q s (ULift.up r)

/-- The actual simplicial tensor morphism has the parameter formula in every
simplex degree, before taking alternating chains or applying an AW inverse. -/
theorem reducedTorusSimplicialTensorProduct_parameter
    (U : SmoothSite (Spec (CommRingCat.of k))) (q : ℕ) (n : SimplexCategoryᵒᵖ)
    (s : sections (reducedTorus k q)
      (Cor.mk (SmoothSite.product U ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n.unop))))
    (r : Cor.mk (SmoothSite.product U
      ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n.unop)) ⟶
        Cor.mk (SmoothSite.torusPower (Spec (CommRingCat.of k)) 1)) :
    let V := SmoothSite.product U ((AlgebraicSimplex.cosimplicialSmoothSite k).obj n.unop)
    (((reducedTorusSimplicialTensorProduct k q).app n).app (op U)).hom
      (s ⊗ₜ[ℤ] ((toReducedTorus k 1).hom.app (op (Cor.mk V)) (ULift.up r))) =
        transfer (reducedTorus k (q + 1))
          (Cor.RelativeGraph.relativeGraphLift k V _
            (r ≫ (Cor.graphFunctor k).map
              (SmoothSite.torusPowerOneIso (Spec (CommRingCat.of k))).hom))
          ((reducedTorusParameterProduct k q).hom.app (op (Cor.mk V)) s) := by
  exact reducedTorusSectionTensorMap_parameter k _ q s r

end AlgebraicGeometry.PresheafWithTransfers
