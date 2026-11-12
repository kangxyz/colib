/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.ComplexEmpty
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedRestrictionModel

/-!
# The original support-forgetful Waldhausen isomorphism for an empty open

When the actual open source has no points, every original evaluated complex is
acyclic there. The original support inclusion is therefore an isomorphism of the
existing Waldhausen categories. Its inverse retains every original global section,
map, and chosen zero, adding only the proved support property. Exactness is
proved using the reverse inclusion of the original geometric full subcategories;
in particular their admissible quotients retain the same support condition.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Complex
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
attribute [local instance] Abelian.hasFiniteBiproducts
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

variable {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} [IsEmpty U]
    (j : U ⟶ X.unop) [IsOpenImmersion j]

/-- Every original global section is supported on the complement of the empty open. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:35"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
theorem supported_of_isEmpty (S : BoundedAboveFlatGlobalSections X) :
    boundedAboveFlatGlobalSectionSupported j S :=
  restrict_acyclic_of_isEmpty j _

/-- The support inverse retains the original section and adds its proved support property. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:39"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
def emptySupportedLift : BoundedAboveFlatGlobalSections X ⥤
    (boundedAboveFlatGlobalSectionSupported j).FullSubcategory :=
  (boundedAboveFlatGlobalSectionSupported j).lift (𝟭 _) (supported_of_isEmpty j)

/-- The original support inclusion has this literal section-preserving inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:43"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
def emptySupportedEquivalence : (boundedAboveFlatGlobalSectionSupported j).FullSubcategory ≌
    BoundedAboveFlatGlobalSections X where
  functor := (boundedAboveFlatGlobalSectionSupported j).ι
  inverse := emptySupportedLift j
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by cat_disch

/-- The evaluated inverse is exact for the original supported geometric classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:51"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
theorem emptySupportedLift_evaluation_exact :
    IsExact (boundedAboveFlatGlobalSectionWaldhausen X).cof
      (boundedAboveFlatGlobalSectionWaldhausen X).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (emptySupportedLift j ⋙ boundedAboveFlatGlobalSupportedEvaluation j) := by
  let := boundedAboveFlatPerfectComplex_containsZero (X := X.unop.toRingedSpace)
  let := boundedAboveFlatPerfectComplex_closedUnderIsomorphisms (X := X.unop.toRingedSpace)
  let : (CategoryTheory.ExactCategory.abelianExactStructure
      (CochainComplex X.unop.Modules ℤ)).IsExtensionClosed
        (boundedAboveFlatPerfectComplex X.unop.toRingedSpace) :=
    boundedAboveFlatPerfectComplex_extensionClosed (X := X.unop.toRingedSpace)
  let := boundedAboveFlatPerfectComplex_closedUnderFiniteProducts (X := X.unop.toRingedSpace)
  let h : boundedAboveFlatPerfectComplex X.unop.toRingedSpace ≤
      boundedAboveFlatPerfectSupported j :=
    fun K hK => ⟨hK, restrict_acyclic_of_isEmpty j K⟩
  have he := (boundedAboveFlatGlobalSectionEvaluation_exact X).comp
    (subcategoryInclusion_exact (A := X.unop.Modules) _ _ h)
  exact he

/-- The literal inverse is exact for the unchanged global and supported Waldhausen structures. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:63"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
theorem emptySupportedLift_exact :
    IsExact (boundedAboveFlatGlobalSectionWaldhausen X).cof
      (boundedAboveFlatGlobalSectionWaldhausen X).weq
      (boundedAboveFlatGlobalSupportedWaldhausen j).cof
      (boundedAboveFlatGlobalSupportedWaldhausen j).weq
      (emptySupportedLift j) where
  zero hz := IsZero.of_full_of_faithful_of_isZero (boundedAboveFlatGlobalSupportedEvaluation j) _
    ((emptySupportedLift_evaluation_exact j).zero hz)
  cofibration f hf := (emptySupportedLift_evaluation_exact j).cofibration f hf
  weak f hf := (emptySupportedLift_evaluation_exact j).weak f hf
  pushout hi hp := IsPushout.of_map_of_faithful (boundedAboveFlatGlobalSupportedEvaluation j)
    ((emptySupportedLift_evaluation_exact j).pushout hi hp)

/-- The exact inverse preserves the original chosen global zero literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:75"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
def emptySupportedInverse : boundedAboveFlatGlobalSectionModel X ⟶
    boundedAboveFlatGlobalSupportedSectionModel j :=
  ⟨⟨emptySupportedLift j, emptySupportedLift_exact j⟩, by
    apply ObjectProperty.FullSubcategory.ext
    rfl⟩

/-- Forgetting empty-open support and restoring its proved property is literally identity. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:81"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
theorem supportedForget_emptySupportedInverse :
    boundedAboveFlatGlobalSupportedForget j ≫ emptySupportedInverse j =
      𝟙 (boundedAboveFlatGlobalSupportedSectionModel j) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  rfl

/-- Adding the proved empty-open support property and forgetting it is literally identity. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:87"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
theorem emptySupportedInverse_supportedForget :
    emptySupportedInverse j ≫ boundedAboveFlatGlobalSupportedForget j =
      𝟙 (boundedAboveFlatGlobalSectionModel X) := by
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  rfl

/-- The original support-forgetful arrow is an actual isomorphism of the existing Models. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:93"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
def emptySupportedModelIso : boundedAboveFlatGlobalSupportedSectionModel j ≅
    boundedAboveFlatGlobalSectionModel X where
  hom := boundedAboveFlatGlobalSupportedForget j
  inv := emptySupportedInverse j
  hom_inv_id := supportedForget_emptySupportedInverse j
  inv_hom_id := emptySupportedInverse_supportedForget j

/-- The forward Waldhausen isomorphism is the original support-forgetful arrow. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:100"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
theorem emptySupportedModelIso_hom :
    (emptySupportedModelIso j).hom = boundedAboveFlatGlobalSupportedForget j := rfl

/-- Bottom-open support gives the same actual support-forgetful Waldhausen isomorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:104"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
def bottomSupportedModelIso (X : Scheme.{u}ᵒᵖ) :
    boundedAboveFlatGlobalSupportedSectionModel (X := X) (⊥ : X.unop.Opens).ι ≅
      boundedAboveFlatGlobalSectionModel X :=
  emptySupportedModelIso (⊥ : X.unop.Opens).ι

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
