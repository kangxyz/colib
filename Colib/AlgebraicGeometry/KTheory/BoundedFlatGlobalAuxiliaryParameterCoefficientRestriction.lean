/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientDiagrams


/-! # The original auxiliary supported full-open restriction square -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The ambient pair map is the original full-open map with its actual weak-change factor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRestriction.lean:26"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem ambientMap_eq_fullRestriction :
    ParameterAuxiliarySupport.ambientMap f.left =
      GlobalParameterCoefficient.parameterFullRestriction f := by
  apply NatTrans.ext
  funext a
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  rfl

omit [IsOpenImmersion f.left] in
/-- The original joint section restriction square holds before realization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRestriction.lean:36"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem originalRestriction_square :
    globalOpenFineRestriction f ≫ rowRestriction P =
      rowRestriction Q ≫ boundedAboveFlatCoefficientSectionModelRestriction f := by
  apply NatTrans.ext
  funext a
  exact (boundedAboveFlatGlobalCoefficientModelRestriction _).naturality
    (show (op Q, a) ⟶ (op P, a) from (f.op, 𝟙 a))

/-- The actual parameter comparison commutes with full ambient restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRestriction.lean:45"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem ambientRestriction_square :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.ambientMap f.left) ≫
        parameterCoefficientRestriction P =
      parameterCoefficientRestriction Q ≫ boundedAboveFlatCoefficientSectionModelRestriction f := by
  rw [ambientMap_eq_fullRestriction]
  unfold parameterCoefficientRestriction
  rw [← Category.assoc, GlobalParameterCoefficient.fullRestriction_model_square,
    Category.assoc, originalRestriction_square, ← Category.assoc]

@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRestriction.lean:54"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
private theorem reflectInclusion {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) (F G : C ⥤ P.FullSubcategory) (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  have hF : P.lift (F ⋙ P.ι) (fun X => (F.obj X).property) = F := rfl
  have hG : P.lift (G ⋙ P.ι) (fun X => (G.obj X).property) = G := rfl
  rw [← hF, ← hG]
  have liftCongr {F G : C ⥤ D} (e : F = G)
      (hF : ∀ X, P (F.obj X)) (hG : ∀ X, P (G.obj X)) :
      P.lift F hF = P.lift G hG := by
    subst e
    rfl
  exact liftCongr h _ _

omit [IsOpenImmersion f.left] in
/-- The actual old supported full restriction retains its original ambient section map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRestriction.lean:63"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem fineRestriction_forget (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((boundedAboveFlatCoefficientSupportedOpenChangeWeakModelMap f T a) ≫
        boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι).ι =
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
      a).ι).ι ⋙
      ((boundedAboveFlatCoefficientSectionModelRestriction f).app a).hom.toFunctor := rfl

/-- The complete supported restriction square preserves the original G7 fine/coarse/full factor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRestriction.lean:72"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem restriction_square (T : Q.left.Opens) :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.restriction f.left T) ≫
        openComparison f T =
      ambientComparison Q T ≫
        (boundedAboveFlatCoefficientSupportedOpenChangeWeakModelTransformation f T ≫
          boundedAboveFlatCoefficientSupportedOpenRestrictionModelTransformation f T) := by
  apply NatTrans.ext
  funext a
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  apply reflectInclusion
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f T
      a).ι)
  have hs := congrArg (fun η => (η.app (specUnder.obj a)).hom.toFunctor)
    (ParameterAuxiliarySupport.restriction_forget f.left T)
  change ((ParameterAuxiliarySupport.restriction f.left T).app (specUnder.obj a)).hom.toFunctor ⋙
      ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj a)).hom.toFunctor =
    ((ParameterModels.forget T.ι).app (specUnder.obj a)).hom.toFunctor ⋙
      ((ParameterAuxiliarySupport.ambientMap f.left).app (specUnder.obj a)).hom.toFunctor at hs
  have hr := congrArg (fun η => (η.app a).hom.toFunctor) (ambientRestriction_square f)
  change ((ParameterAuxiliarySupport.ambientMap f.left).app (specUnder.obj a)).hom.toFunctor ⋙
      ((parameterCoefficientRestriction P).app a).hom.toFunctor =
    ((parameterCoefficientRestriction Q).app a).hom.toFunctor ⋙
      ((boundedAboveFlatCoefficientSectionModelRestriction f).app a).hom.toFunctor at hr
  change ((ParameterAuxiliarySupport.restriction f.left T).app (specUnder.obj a)).hom.toFunctor ⋙
      (openComponent f T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f
          T a).ι).ι =
    (ambientComponent Q T a).hom.toFunctor ⋙
      ((boundedAboveFlatCoefficientSupportedOpenChangeWeakModelMap f T a) ≫
        boundedAboveFlatCoefficientSupportedOpenRestrictionModelMap f T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f
          T a).ι).ι
  rw [openComponent_forget, fineRestriction_forget]
  rw [← Functor.assoc, hs, Functor.assoc, hr, ← Functor.assoc, ← ambientComponent_forget]
  rfl

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
