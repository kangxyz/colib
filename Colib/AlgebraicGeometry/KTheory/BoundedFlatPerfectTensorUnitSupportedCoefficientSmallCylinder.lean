/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientCylinder
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectTensorUnitSupportedCoefficientSmallModel
public import Colib.KTheory.Waldhausen.Iterated.RowTransformationCylinder

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
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.QuotientRows
open CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T)

variable (r : (Γ(S.right, ⊤))ˣ)

/-- Apply precisely the original small-model transport on the input and both output S-directions.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSmallMo\
    del.lean:63"
  "adaptation" "Original whole supported double cylinder and actual two-direction transport."]
def tensorSupportedPairSmallCoefficientCylinder :
    (((stages 0).obj
      (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen T.hom))) ⊗ Δ[1]) ⊗ Δ[1] ⟶
      (stages 1).obj (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen S.hom)) :=
  (((boundedAboveFlatPerfectSupportedWaldhausen T.hom).asSmallSSetIso.inv ▷ Δ[1]) ▷ Δ[1]) ≫
    tensorSupportedPairCoefficientCylinder p r ≫
      (boundedAboveFlatPerfectSupportedWaldhausen S.hom).asSmallDoubleDiagonalMap

/-- The complete actual cell is the original normalized tensor track with its structure cylinder.
-/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSmallMo\
    del.lean:72"
  "adaptation" "Original whole supported double cylinder and actual two-direction transport."]
theorem tensorSupportedPairSmallCoefficientCylinder_eq :
    tensorSupportedPairSmallCoefficientCylinder p r =
      (stageTransformationCylinder 0 (tensorSupportedPairModelTransformation p r)
        (tensorSupportedPairModelTransformation_weak p r) ▷ Δ[1]) ≫
        stageCylinder 0 (asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen S.hom)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  apply Subtype.ext
  change tensorSupportedPairNormalizedCoefficientPrism p r (z.1.1.val ⋙ AsSmall.down)
      z.1.2.down z.2.down ⋙
        postcompose (boundedAboveFlatPerfectSupportedWaldhausen S.hom)
          (boundedAboveFlatPerfectSupportedWaldhausen S.hom).asSmall
          (boundedAboveFlatPerfectSupportedWaldhausen S.hom).asSmall_up_exact n.unop =
    nerveCylinderDiagram (whiskerLeft z.1.1.val (tensorSupportedPairModelTransformation p r))
      z.1.2.down ⋙
      suspensionRow (boundedAboveFlatPerfectSupportedWaldhausen S.hom).asSmall z.2.down
  rw [tensorSupportedPairNormalizedCoefficientPrism_eq, Functor.assoc,
    (boundedAboveFlatPerfectSupportedWaldhausen S.hom).asSmall_suspensionRow]
  rw [← Functor.assoc, ← iteratedNerveCylinderDiagram_postcomp]
  rfl

/-- The independent supported cell is the genuine original first-row transformation cylinder. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitSupportedCoefficientSmallMo\
    del.lean:96"
  "adaptation" "Original whole supported double cylinder and actual two-direction transport."]
theorem tensorSupportedPairSmallCoefficientCylinder_row :
    tensorSupportedPairSmallCoefficientCylinder p r =
      rowTransformationCylinder (tensorSupportedPairModelTransformation p r)
        (tensorSupportedPairModelTransformation_weak p r) 0 := by
  rw [rowTransformationCylinder_eq, tensorSupportedPairSmallCoefficientCylinder_eq]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0562"] tensorSupportedPairSmallCoefficientCylinder_eq

end AlgebraicGeometry.Scheme.Modules
