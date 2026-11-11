/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatGlobalSupportedStructure
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum

/-! # The actual support inclusion and its selected-zero model map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
variable {Y U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- Forget only the original supported acyclicity, retaining its actual exact inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientInputNaturality.\
    lean:44"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def tensorCoefficientSupportedForget :
    (boundedAboveFlatPerfectSupported j).FullSubcategory ⥤ (boundedAboveFlatPerfectComplex
      Y.toRingedSpace).FullSubcategory :=
  ObjectProperty.ιOfLE (show boundedAboveFlatPerfectSupported j ≤ boundedAboveFlatPerfectComplex
      Y.toRingedSpace from
    fun _ h => h.1)

/-- The inherited support inclusion is exact for the original Waldhausen structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientInputNaturality.\
    lean:50"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
theorem tensorCoefficientSupportedForget_exact :
    IsExact (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace).cof (boundedAboveFlatPerfectWaldhausen
      Y.toRingedSpace).weq
      (tensorCoefficientSupportedForget j) :=
  by
    let := boundedAboveFlatPerfectComplex_containsZero (X := Y.toRingedSpace)
    let := boundedAboveFlatPerfectComplex_closedUnderIsomorphisms (X := Y.toRingedSpace)
    let : (CategoryTheory.ExactCategory.abelianExactStructure
        (CochainComplex Y.Modules ℤ)).IsExtensionClosed
          (boundedAboveFlatPerfectComplex Y.toRingedSpace) :=
      boundedAboveFlatPerfectComplex_extensionClosed (X := Y.toRingedSpace)
    let := boundedAboveFlatPerfectComplex_closedUnderFiniteProducts (X := Y.toRingedSpace)
    exact subcategoryInclusion_exact (A := Y.Modules)
      (boundedAboveFlatPerfectSupported j)
      (boundedAboveFlatPerfectComplex Y.toRingedSpace) (fun _ h => h.1)

/-- The actual supported input uses precisely the original chosen-zero rebase. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TensorUnitCoefficientInputNaturality.\
    lean:58"
  "adaptation" "Original support evaluation, actual inclusion and both zero comparisons."]
def tensorCoefficientSupportedForgetModel :
    asSmallCategory (boundedAboveFlatPerfectSupportedWaldhausen j) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen Y.toRingedSpace) :=
  asSmallCategoryMap _ _ (tensorCoefficientSupportedForget_exact j).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

end AlgebraicGeometry.Scheme.Modules
