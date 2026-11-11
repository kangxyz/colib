/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientTransport
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedFiberLocalizationModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientRestriction


/-! # The three original G7 coefficient rows and the actual support inclusion square -/
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

@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientDiagrams.lean:25"
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

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- Original fiber reindexing retains its literal full-subcategory inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientDiagrams.lean:36"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem fineFiberMap_forget {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedFiberModelMap f T g).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported
          (boundedAboveFlatCoefficientFiberSupportOpen f T b).ι).ι =
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen f
        T a).ι).ι ⋙
        ((boundedAboveFlatCoefficientSectionModelRow Q).map g).hom.toFunctor := rfl

/-- The actual original fiber comparison is coefficient-natural before evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientDiagrams.lean:44"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem fiberComponent_naturality {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    (ParameterAuxiliarySupport.fiber f.left T).map (specUnder.map g) ≫ fiberComponent f T b =
      fiberComponent f T a ≫ (boundedAboveFlatCoefficientSupportedFiberModelFunctor f T).map g := by
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  apply reflectInclusion
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen f T
      b).ι)
  have hs := congrArg (fun m => m.hom.toFunctor)
    ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).naturality (specUnder.map g))
  have hr := congrArg (fun m => m.hom.toFunctor) ((parameterCoefficientRestriction Q).naturality g)
  change ((ParameterAuxiliarySupport.fiber f.left T).map (specUnder.map g)).hom.toFunctor ⋙
      ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj b)).hom.toFunctor =
    ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj a)).hom.toFunctor ⋙
      ((ParameterModels.ambient Q.left).map (specUnder.map g)).hom.toFunctor at hs
  change ((ParameterModels.ambient Q.left).map (specUnder.map g)).hom.toFunctor ⋙
      ((parameterCoefficientRestriction Q).app b).hom.toFunctor =
    ((parameterCoefficientRestriction Q).app a).hom.toFunctor ⋙
      ((boundedAboveFlatCoefficientSectionModelRow Q).map g).hom.toFunctor at hr
  change ((ParameterAuxiliarySupport.fiber f.left T).map (specUnder.map g)).hom.toFunctor ⋙
      (fiberComponent f T b).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported
          (boundedAboveFlatCoefficientFiberSupportOpen f T b).ι).ι =
    (fiberComponent f T a).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSupportedFiberModelMap f T g).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen
          f T b).ι).ι
  rw [fiberComponent_forget, fineFiberMap_forget]
  rw [← Functor.assoc, hs, Functor.assoc, hr, ← Functor.assoc, ← fiberComponent_forget]
  rfl

/-- The full original fiber row comparison, retaining the old G7 model diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientDiagrams.lean:74"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
def fiberComparison :
    specUnder ⋙ ParameterAuxiliarySupport.fiber f.left T ⟶
      boundedAboveFlatCoefficientSupportedFiberModelFunctor f T where
  app := fiberComponent f T
  naturality _ _ g := fiberComponent_naturality f T g

omit [IsOpenImmersion f.left] in
/-- Original full-open reindexing retains its literal full-subcategory inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientDiagrams.lean:82"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem fineOpenMap_forget {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedFullOpenModelMap f T g).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f
          T b).ι).ι =
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f T
        a).ι).ι ⋙
        ((boundedAboveFlatCoefficientSectionModelRow P).map g).hom.toFunctor := rfl

omit [IsOpenImmersion f.left] in
/-- The actual original full-open comparison is coefficient-natural before evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientDiagrams.lean:90"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem openComponent_naturality {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    (ParameterAuxiliarySupport.openModel f.left T).map (specUnder.map g) ≫ openComponent f T b =
      openComponent f T a ≫ (boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T).map g
        := by
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  apply reflectInclusion
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f T
      b).ι)
  have hs := congrArg (fun m => m.hom.toFunctor)
    ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).naturality (specUnder.map g))
  have hr := congrArg (fun m => m.hom.toFunctor) ((parameterCoefficientRestriction P).naturality g)
  change ((ParameterAuxiliarySupport.openModel f.left T).map (specUnder.map g)).hom.toFunctor ⋙
      ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj b)).hom.toFunctor =
    ((ParameterModels.forget (f.left ⁻¹ᵁ T).ι).app (specUnder.obj a)).hom.toFunctor ⋙
      ((ParameterModels.ambient P.left).map (specUnder.map g)).hom.toFunctor at hs
  change ((ParameterModels.ambient P.left).map (specUnder.map g)).hom.toFunctor ⋙
      ((parameterCoefficientRestriction P).app b).hom.toFunctor =
    ((parameterCoefficientRestriction P).app a).hom.toFunctor ⋙
      ((boundedAboveFlatCoefficientSectionModelRow P).map g).hom.toFunctor at hr
  change ((ParameterAuxiliarySupport.openModel f.left T).map (specUnder.map g)).hom.toFunctor ⋙
      (openComponent f T b).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f
          T b).ι).ι =
    (openComponent f T a).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSupportedFullOpenModelMap f T g).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientOpenSupportOpen f
          T b).ι).ι
  rw [openComponent_forget, fineOpenMap_forget]
  rw [← Functor.assoc, hs, Functor.assoc, hr, ← Functor.assoc, ← openComponent_forget]
  rfl

/-- The full original supported-open row comparison, with its actual native target. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientDiagrams.lean:119"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
def openComparison :
    specUnder ⋙ ParameterAuxiliarySupport.openModel f.left T ⟶
      boundedAboveFlatCoefficientSupportedFullOpenModelFunctor f T where
  app := openComponent f T
  naturality _ _ g := openComponent_naturality f T g

/-- The original support enlargement square commutes as complete Model transformations. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientDiagrams.lean:126"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem enlargement_square :
    Functor.whiskerLeft specUnder (ParameterAuxiliarySupport.enlargement f.left T) ≫
        ambientComparison Q T =
      fiberComparison f T ≫ boundedAboveFlatCoefficientSupportedFiberForgetModelTransformation f T
        := by
  apply NatTrans.ext
  funext a
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  apply reflectInclusion
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T a).ι)
  have he := congrArg (fun η => (η.app (specUnder.obj a)).hom.toFunctor)
    (ParameterAuxiliarySupport.enlargement_forget f.left T)
  change ((ParameterAuxiliarySupport.enlargement f.left T).app (specUnder.obj a)).hom.toFunctor ⋙
      ((ParameterModels.forget T.ι).app (specUnder.obj a)).hom.toFunctor =
    ((ParameterModels.forget (T ⊔ f.left.opensRange).ι).app (specUnder.obj a)).hom.toFunctor at he
  change ((ParameterAuxiliarySupport.enlargement f.left T).app (specUnder.obj a)).hom.toFunctor ⋙
      (ambientComponent Q T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
          a).ι).ι =
    (fiberComponent f T a).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSupportedFiberForgetModelMap f T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
          a).ι).ι
  rw [ambientComponent_forget, ← Functor.assoc, he]
  change _ = (fiberComponent f T a).hom.toFunctor ⋙
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientFiberSupportOpen f T
      a).ι).ι
  exact (fiberComponent_forget f T a).symm

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
