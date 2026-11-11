/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalAuxiliaryParameterCoefficientModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientModels


/-! # Whole coefficient naturality of the original auxiliary support comparisons -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
open CategoryTheory.Waldhausen.SmallWaldhausenCategory

@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRows.lean:25"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
private theorem subcategoryFunctor_ext {C D : Type*} [Category* C] [Category* D]
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

variable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) (T : Q.left.Opens)

/-- Forgetting auxiliary support gives the exact original ambient coefficient comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRows.lean:35"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem ambientComponent_forget (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (ambientComponent Q T a).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
          a).ι).ι =
      ((ParameterModels.forget T.ι).app (specUnder.obj a)).hom.toFunctor ⋙
        ((parameterCoefficientRestriction Q).app a).hom.toFunctor := by
  have hr : ((parameterCoefficientRestriction Q).app a).hom.toFunctor =
      (boundedAboveFlatGlobalSectionModelFunctor.map (canonicalRowIso Q a).hom.op ≫
        (rowRestriction Q).app a).hom.toFunctor := by
    unfold parameterCoefficientRestriction
    rw [NatTrans.comp_app, parameterRowModelIso_hom_app]
  rw [hr]
  have hp := boundedAboveFlatGlobalSupportedPairReindex_forget (parameterSupportPairIso Q T a).hom
  dsimp only [supportOpenPair] at hp
  rw [parameterSupportPairIso_hom_right] at hp
  exact congrArg (fun F => F ⋙ ((boundedAboveFlatGlobalCoefficientModelRestriction _).app (op Q,
    a)).hom.toFunctor) hp

/-- Original auxiliary-supported coefficient reindexing retains its full-subcategory inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRows.lean:51"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem fineAmbientMap_forget {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (boundedAboveFlatCoefficientSupportedAmbientModelMap T g).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
          b).ι).ι =
      (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
        a).ι).ι ⋙
        ((boundedAboveFlatCoefficientSectionModelRow Q).map g).hom.toFunctor := rfl

/-- The actual component comparison is natural for every original coefficient morphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRows.lean:58"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
theorem ambientComponent_naturality {a b : Under (CommRingCat.of (ULift.{u} ℤ))}
    (g : a ⟶ b) :
    (ParameterAuxiliarySupport.ambient T).map (specUnder.map g) ≫ ambientComponent Q T b =
      ambientComponent Q T a ≫ (boundedAboveFlatCoefficientSupportedAmbientModelFunctor T).map g
        := by
  apply WideSubcategory.hom_ext
  apply CategoryTheory.Waldhausen.SmallWaldhausenCategory.Hom.ext
  apply subcategoryFunctor_ext
    (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T b).ι)
  have hs := congrArg (fun m => m.hom.toFunctor) ((ParameterModels.forget T.ι).naturality
    (specUnder.map g))
  have hr := congrArg (fun m => m.hom.toFunctor) ((parameterCoefficientRestriction Q).naturality g)
  change ((ParameterAuxiliarySupport.ambient T).map (specUnder.map g)).hom.toFunctor ⋙
      ((ParameterModels.forget T.ι).app (specUnder.obj b)).hom.toFunctor =
    ((ParameterModels.forget T.ι).app (specUnder.obj a)).hom.toFunctor ⋙
      ((ParameterModels.ambient Q.left).map (specUnder.map g)).hom.toFunctor at hs
  change ((ParameterModels.ambient Q.left).map (specUnder.map g)).hom.toFunctor ⋙
      ((parameterCoefficientRestriction Q).app b).hom.toFunctor =
    ((parameterCoefficientRestriction Q).app a).hom.toFunctor ⋙
      ((boundedAboveFlatCoefficientSectionModelRow Q).map g).hom.toFunctor at hr
  change ((ParameterAuxiliarySupport.ambient T).map (specUnder.map g)).hom.toFunctor ⋙
      (ambientComponent Q T b).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
          b).ι).ι =
    (ambientComponent Q T a).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientSupportedAmbientModelMap T g).hom.toFunctor ⋙
        (boundedAboveFlatCoefficientSectionSupported (boundedAboveFlatCoefficientSupportOpen Q T
          b).ι).ι
  rw [ambientComponent_forget, fineAmbientMap_forget]
  rw [← Functor.assoc, hs, Functor.assoc, hr, ← Functor.assoc,
    ← ambientComponent_forget]
  rfl

/-- The complete parameter auxiliary support row maps to the unchanged original G7 ambient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalAuxiliaryParameterCoefficientRows.lean:87"
  "adaptation" "Original whole auxiliary coefficient rows and exact support-forget squares"]
def ambientComparison :
    specUnder ⋙ ParameterAuxiliarySupport.ambient T ⟶
      boundedAboveFlatCoefficientSupportedAmbientModelFunctor T where
  app := ambientComponent Q T
  naturality _ _ g := ambientComponent_naturality Q T g

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
