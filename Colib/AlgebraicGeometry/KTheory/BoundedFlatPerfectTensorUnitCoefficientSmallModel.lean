/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitCoefficientRealization
public import Colib.CategoryTheory.Waldhausen.AsSmall.Double

/-!
# The actual coefficient cell in the original small-model S-prespectrum

Transport the independently constructed first coefficient cell by the original small-model
maps, including the actual exact postcomposition of both quotient-row directions. The complete
result is the original stage-zero tensor transformation followed by the original stage-cylinder.
This is a whole simplicial map identity, with neither time coordinate interchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite MonoidalCategory
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
      CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- Apply precisely the original small-model transport on the input and both output S-directions.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientSmallModel.lean:33"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
def tensorUnitPullbackSmallCoefficientCylinder :
    (((stages 0).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace))) ⊗
      Δ[1]) ⊗ Δ[1] ⟶
      (stages 1).obj (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) :=
  (((boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).asSmallSSetIso.inv ▷ Δ[1]) ▷ Δ[1]) ≫
    tensorUnitPullbackCoefficientCylinder f r ≫
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmallDoubleDiagonalMap

/-- The complete actual cell is the original normalized tensor track with its structure cylinder.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientSmallModel.lean:42"
  "adaptation" "Original two-direction AsSmall transport and finite coefficient stages."]
theorem tensorUnitPullbackSmallCoefficientCylinder_eq :
    tensorUnitPullbackSmallCoefficientCylinder f r =
      (stageTransformationCylinder 0 (tensorUnitPullbackModelTransformation f r)
        (tensorUnitPullbackModelTransformation_weak f r) ▷ Δ[1]) ≫
        stageCylinder 0 (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  change tensorUnitPullbackNormalizedCoefficientPrism f r (z.1.1.val ⋙ AsSmall.down)
      z.1.2.down z.2.down ⋙
        postcompose (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall
          (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall_up_exact n.unop =
    nerveCylinderDiagram (whiskerLeft z.1.1.val (tensorUnitPullbackModelTransformation f r))
      z.1.2.down ⋙ suspensionRow (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall
      z.2.down
  rw [tensorUnitPullbackNormalizedCoefficientPrism_eq, Functor.assoc,
    (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall_suspensionRow]
  rw [← Functor.assoc, ← iteratedNerveCylinderDiagram_postcomp]
  rfl

end AlgebraicGeometry.Scheme.Modules
