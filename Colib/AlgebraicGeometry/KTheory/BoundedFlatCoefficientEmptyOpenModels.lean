/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.ComplexEmpty
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportModels

/-! # Empty support for the original coefficient Models -/
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
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
namespace AlgebraicGeometry.Scheme.Modules.CoefficientEmptyOpen

variable {R : CommRingCat.{u}} {i : Index R} {U : Scheme.{u}} [IsEmpty U]
    (j : U ⟶ space i) [IsOpenImmersion j]

/-- Every original global section is supported on the complement of the empty open. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:35"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
theorem supported_of_isEmpty (S : BoundedAboveFlatCoefficientSections i) :
    boundedAboveFlatCoefficientSectionSupported j S :=
  restrict_acyclic_of_isEmpty j _

/-- The support inverse retains the original section and adds its proved support property. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:39"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
def emptySupportedLift : BoundedAboveFlatCoefficientSections i ⥤
    (boundedAboveFlatCoefficientSectionSupported j).FullSubcategory :=
  (boundedAboveFlatCoefficientSectionSupported j).lift (𝟭 _) (supported_of_isEmpty j)

/-- The original support inclusion has this literal section-preserving inverse. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:43"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
def emptySupportedEquivalence : (boundedAboveFlatCoefficientSectionSupported j).FullSubcategory ≌
    BoundedAboveFlatCoefficientSections i where
  functor := (boundedAboveFlatCoefficientSectionSupported j).ι
  inverse := emptySupportedLift j
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp := by cat_disch

private theorem emptySupportedLift_comp_inclusion :
    emptySupportedLift j ⋙ (boundedAboveFlatCoefficientSectionSupported j).ι = 𝟭 _ :=
  ObjectProperty.lift_comp_ι _ _ _

private def evaluationLiftIsoWhisker
    (h : boundedAboveFlatPerfectComplex (space i).toRingedSpace ≤
      boundedAboveFlatPerfectSupported j) :
    (emptySupportedLift j ⋙ boundedAboveFlatCoefficientSupportedEvaluation j) ⋙
        (boundedAboveFlatPerfectSupported j).ι ≅
      (boundedAboveFlatCoefficientOriginalEvaluation i ⋙ ObjectProperty.ιOfLE h) ⋙
        (boundedAboveFlatPerfectSupported j).ι := by
  let I := (boundedAboveFlatPerfectSupported j).ι
  let L := emptySupportedLift j
  let J := (boundedAboveFlatCoefficientSectionSupported j).ι
  let E := boundedAboveFlatCoefficientOriginalEvaluation i
  let U := (boundedAboveFlatPerfectComplex (space i).toRingedSpace).ι
  let F := boundedAboveFlatCoefficientSupportedEvaluation j
  let e₁ : (L ⋙ F) ⋙ I ≅ L ⋙ J ⋙ E ⋙ U :=
    Functor.associator L F I ≪≫
      Functor.isoWhiskerLeft L (eqToIso (boundedAboveFlatCoefficientSupportedEvaluation_forget j))
  let e₂ : L ⋙ J ⋙ E ⋙ U ≅ E ⋙ U :=
    (Functor.associator L J (E ⋙ U)).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (emptySupportedLift_comp_inclusion j)) (E ⋙ U) ≪≫
      Functor.leftUnitor (E ⋙ U)
  let e₃ : (E ⋙ ObjectProperty.ιOfLE h) ⋙ I ≅ E ⋙ U :=
    Functor.associator E _ I ≪≫ Functor.isoWhiskerLeft E (ObjectProperty.ιOfLECompιIso h)
  exact e₁ ≪≫ e₂ ≪≫ e₃.symm

private def evaluationLiftIso
    (h : boundedAboveFlatPerfectComplex (space i).toRingedSpace ≤
      boundedAboveFlatPerfectSupported j) :
    emptySupportedLift j ⋙ boundedAboveFlatCoefficientSupportedEvaluation j ≅
      boundedAboveFlatCoefficientOriginalEvaluation i ⋙ ObjectProperty.ιOfLE h := by
  let H := ((CategoryTheory.Functor.whiskeringRight (BoundedAboveFlatCoefficientSections i)
      (boundedAboveFlatPerfectSupported j).FullSubcategory
      (CochainComplex (space i).Modules ℤ)).obj (boundedAboveFlatPerfectSupported j).ι)
  let e : H.obj (emptySupportedLift j ⋙ boundedAboveFlatCoefficientSupportedEvaluation j) ≅
      H.obj (boundedAboveFlatCoefficientOriginalEvaluation i ⋙ ObjectProperty.ιOfLE h) :=
    evaluationLiftIsoWhisker j h
  exact ((boundedAboveFlatPerfectSupported j).fullyFaithfulι.whiskeringRight _).preimageIso e

/-- The evaluated inverse is exact for the original supported geometric classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:51"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
theorem emptySupportedLift_evaluation_exact :
    IsExact (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatPerfectSupportedWaldhausen j).cof
      (boundedAboveFlatPerfectSupportedWaldhausen j).weq
      (emptySupportedLift j ⋙ boundedAboveFlatCoefficientSupportedEvaluation j) := by
  let := boundedAboveFlatPerfectComplex_containsZero (X := (space i).toRingedSpace)
  let := boundedAboveFlatPerfectComplex_closedUnderIsomorphisms (X := (space i).toRingedSpace)
  let : (CategoryTheory.ExactCategory.abelianExactStructure
      (CochainComplex (space i).Modules ℤ)).IsExtensionClosed
        (boundedAboveFlatPerfectComplex (space i).toRingedSpace) :=
    boundedAboveFlatPerfectComplex_extensionClosed (X := (space i).toRingedSpace)
  let := boundedAboveFlatPerfectComplex_closedUnderFiniteProducts (X := (space i).toRingedSpace)
  let h : boundedAboveFlatPerfectComplex (space i).toRingedSpace ≤
      boundedAboveFlatPerfectSupported j :=
    fun K hK => ⟨hK, restrict_acyclic_of_isEmpty j K⟩
  exact ExtensionCategory.isExact_of_natIso
    (boundedAboveFlatCoefficientSectionWaldhausen i)
    (boundedAboveFlatPerfectSupportedWaldhausen j)
    ((boundedAboveFlatCoefficientOriginalEvaluation_exact i).comp
      (subcategoryInclusion_exact (A := (space i).Modules) _ _ h))
    (evaluationLiftIso j h).symm

/-- The literal inverse is exact for the unchanged original section structures. -/
theorem emptySupportedLift_exact :
    IsExact (boundedAboveFlatCoefficientSectionWaldhausen i).cof
      (boundedAboveFlatCoefficientSectionWaldhausen i).weq
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).cof
      (boundedAboveFlatCoefficientSupportedSectionWaldhausen j).weq
      (emptySupportedLift j) := by
  let e := boundedAboveFlatCoefficientSupportedSectionEquivalence j
  let W := boundedAboveFlatCoefficientSupportedSectionWaldhausen j
  let V := boundedAboveFlatCoefficientSectionWaldhausen i
  let F := boundedAboveFlatPerfectSupportedWaldhausen j
  let L := emptySupportedLift j
  let ε : L ⋙ e.functor ≅ L ⋙ boundedAboveFlatCoefficientSupportedEvaluation j :=
    Functor.isoWhiskerLeft L
      (eqToIso (boundedAboveFlatCoefficientSupportedSectionEquivalence_functor j))
  let p : IsExact V.cof V.weq F.cof F.weq (L ⋙ e.functor) :=
    ExtensionCategory.isExact_of_natIso V F (emptySupportedLift_evaluation_exact j) ε.symm
  let q : IsExact F.cof F.weq W.cof W.weq e.inverse :=
    boundedAboveFlatCoefficientSupportedSectionEquivalence_inverse_exact j
  exact ExtensionCategory.isExact_of_natIso V W (p.comp q)
    ((Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft L e.unitIso.symm ≪≫
      Functor.rightUnitor L)

/-- The exact inverse preserves the original chosen global zero literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalEmptySupportedModels.lean:75"
  "adaptation" "Original empty-support equivalence with unchanged sections, arrows and zero."]
def emptySupportedInverse : boundedAboveFlatCoefficientSectionModel i ⟶
    boundedAboveFlatCoefficientSupportedSectionModel j :=
  ⟨⟨emptySupportedLift j, emptySupportedLift_exact j⟩, by
    apply ObjectProperty.FullSubcategory.ext
    rfl⟩

variable (forget : boundedAboveFlatCoefficientSupportedSectionModel j ⟶
    boundedAboveFlatCoefficientSectionModel i)
  (hforget : forget.hom.toFunctor = (boundedAboveFlatCoefficientSectionSupported j).ι)

include hforget in
/-- The actual support-forgetting arrow over an empty open is an isomorphism. -/
theorem supportedForget_isIso : IsIso forget := by
  refine ⟨⟨emptySupportedInverse j, ?_, ?_⟩⟩
  · apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change forget.hom.toFunctor ⋙ emptySupportedLift j = 𝟭 _
    exact congrArg (fun F => F ⋙ emptySupportedLift j) hforget
  · apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change emptySupportedLift j ⋙ forget.hom.toFunctor = 𝟭 _
    exact congrArg (fun F => emptySupportedLift j ⋙ F) hforget

end AlgebraicGeometry.Scheme.Modules.CoefficientEmptyOpen
