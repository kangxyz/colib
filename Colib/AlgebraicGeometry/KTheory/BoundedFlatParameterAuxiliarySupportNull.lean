/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatParameterAuxiliarySupportTrack
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenPairNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterLaurentNull

/-! # The original selected-zero null for the auxiliary-supported parameter diagram -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.RingedSpace
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Functor.IdentityAutomorphism
open Topology.LoopPrespectrum KTheory.Bass
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
open GlobalSupportedParameter ParameterLaurentTrack
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f] (T : Q.Opens)

/-- The original localization open as an open-pair object. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:28"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
def localizationPair : Scheme.OpenPairs.{u} :=
  MorphismProperty.Arrow.mk f inferInstance

/-- The localization open factors through the union by its original image isomorphism. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:32"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
def vanishingPair : localizationPair f ⟶ supportOpenPair (unionOpen f T) :=
  MorphismProperty.Arrow.homMk
    (f.isoOpensRange.hom ≫ Q.homOfLE (show f.opensRange ≤ unionOpen f T from le_sup_right))
    (𝟙 Q) (by
      change (f.isoOpensRange.hom ≫ Q.homOfLE _) ≫ (unionOpen f T).ι = f ≫ 𝟙 Q
      rw [Category.assoc, Scheme.homOfLE_ι, f.isoOpensRange_hom_ι, Category.comp_id])

/-- Union support retains actual vanishing on the original localization open. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:40"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
def toBasic : fiber f T ⟶ ParameterModels.supported f := by
  let h := supportedMap (vanishingPair f T)
  dsimp only [localizationPair, supportOpenPair] at h
  exact h

/-- This vanishing comparison leaves the underlying original section unchanged. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:46"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
theorem toBasic_forget :
    toBasic f T ≫ ParameterModels.forget f = ParameterModels.forget (unionOpen f T).ι := by
  have h := supportedMap_forget (vanishingPair f T)
  change toBasic f T ≫ ParameterModels.forget f =
    ParameterModels.forget (unionOpen f T).ι ≫ ambientMap (𝟙 Q) at h
  simpa only [ambientMap_id, Category.comp_id] using h

/-- The auxiliary composite has exactly the original full-open underlying functor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:54"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
theorem composite_forget :
    (enlargement f T ≫ restriction f T) ≫ ParameterModels.forget (inverseOpen f T).ι =
      toBasic f T ≫ (ParameterModels.forget f ≫ ambientMap f) := by
  rw [Category.assoc, restriction_forget, ← Category.assoc, enlargement_forget,
    ← toBasic_forget f T, Category.assoc]

/-- Its original evaluation is acyclic on the full open scheme, not just on its support open. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:61"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
theorem composite_acyclic (X : Scheme.{u}ᵒᵖ) (S : ((fiber f T).obj X).obj.Obj) :
    (((boundedAboveFlatGlobalSectionEvaluation (op ((pair f X.unop).left))).obj
      (((ParameterModels.forget (inverseOpen f T).ι).app X).hom.toFunctor.obj
        (((enlargement f T).app X ≫ (restriction f T).app X).hom.toFunctor.obj
          S))).obj).Acyclic := by
  have h := congrArg (fun k => k.hom.toFunctor.obj S)
    (NatTrans.congr_app (composite_forget f T) X)
  have ha := pairRestriction_acyclic (pair f X.unop) (((toBasic f T).app X).hom.toFunctor.obj S)
  exact (congrArg
    (fun Y => (((boundedAboveFlatGlobalSectionEvaluation
      (op ((pair f X.unop).left))).obj Y).obj).Acyclic) h).mpr ha

/-- The unique arrow from the actual chosen supported zero to the original composite. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:72"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
def zeroToFull (X : Scheme.{u}ᵒᵖ) :
    (zeroHom ((fiber f T).obj X) ((openModel f T).obj X)).hom.toFunctor ⟶
      ((enlargement f T).app X ≫ (restriction f T).app X).hom.toFunctor where
  app S := ((openModel f T).obj X).obj.waldhausen.isZero.to_
    (((enlargement f T).app X ≫ (restriction f T).app X).hom.toFunctor.obj S)
  naturality _ _ _ := ((openModel f T).obj X).obj.waldhausen.isZero.eq_of_src _ _

/-- Actual union support makes the original zero-to-composite arrow weak in the fine target. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:80"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
theorem zeroToFull_weak (X : Scheme.{u}ᵒᵖ) (S : ((fiber f T).obj X).obj.Obj) :
    ((openModel f T).obj X).obj.waldhausen.weq ((zeroToFull f T X).app S) := by
  let j := (pair (inverseOpen f T).ι X.unop).hom
  have hZ := (boundedAboveFlatPerfectSupported j).ι.map_isZero
    ((boundedAboveFlatGlobalSupportedEvaluation_exact j).zero
      ((openModel f T).obj X).obj.waldhausen.isZero)
  change QuasiIso ((boundedAboveFlatGlobalSupportedEvaluation j).map ((zeroToFull f T X).app S)).hom
  rw [quasiIso_iff]
  intro n
  exact (quasiIsoAt_iff_exactAt _ n
    (HomologicalComplex.acyclic_of_isZero _ hZ n)).mpr (composite_acyclic f T X S n)

/-- Reverse the original weak zero transformation with its unchanged whole time parameter. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:92"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
def fullNull : DiagramNullHomotopy
    (Functor.whiskerRight (enlargement f T) prespectrumFunctor)
    (Functor.whiskerRight (restriction f T) prespectrumFunctor) :=
  modelDiagramZeroNull (enlargement f T) (restriction f T)
    (zeroToFull f T) (zeroToFull_weak f T)

/-- Every value is the unchanged reversed selected-zero transformation at its original time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:99"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
theorem fullNull_level (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : (prespectrum ((fiber f T).obj X)).space n) :
    ((fullNull f T).homotopy X).level n (r, x) =
      (prespectrumTransformationHomotopy (zeroToFull f T X)
        (zeroToFull_weak f T X)).level n (unitInterval.symm r, x) := rfl

/-- The auxiliary composite preserves the same original lifted scalar. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:106"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
theorem composite_unit (X : Scheme.{u}ᵒᵖ) :
    Preserves (((enlargement f T).app (laurent.op.obj X) ≫
      (restriction f T).app (laurent.op.obj X)).hom.toFunctor)
      (supportedUnit (unionOpen f T).ι X) (supportedUnit (inverseOpen f T).ι X) := by
  intro S
  exact (congrArg (((restriction f T).app (laurent.op.obj X)).hom.toFunctor.map)
    (supportedMap_unit (enlargementPair f T) X S)).trans
      (supportedMap_unit (supportRestrictionPair f T) X
        (((enlargement f T).app (laurent.op.obj X)).hom.toFunctor.obj S))

/-- The same reversed original zero-null preserves compatible identity units. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:117"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
theorem fullNull_unitCompatible (X : Scheme.{u}ᵒᵖ) :
    ZeroNullUnitCompatible ((enlargement f T).app X) ((restriction f T).app X)
      ((fullNull f T).homotopy X) :=
  prespectrumCompositeZeroNullHomotopy_unitCompatible
    ((enlargement f T).app X) ((restriction f T).app X)
    (zeroToFull f T X) (zeroToFull_weak f T X)

/-- Null time and original Laurent action time remain independent on the whole support diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/ParameterAuxiliarySupportNull.lean:125"
  "adaptation" "Original auxiliary selected-zero null and independent-time Laurent compatibility."]
theorem fullNull_laurentInterchange (X : Scheme.{u}ᵒᵖ) :
    TrackInterchange ((fullNull f T).homotopy X)
      ((fullNull f T).homotopy (laurent.op.obj X))
      ((supportedTrack (unionOpen f T).ι).homotopy X)
      ((supportedTrack (inverseOpen f T).ι).homotopy X) :=
  modelDiagramNull_coefficientCompatible
    (r := enlargement f T) (q := restriction f T) (fullNull f T) (coefficient.app X)
    (supportedUnit (unionOpen f T).ι X) (supportedUnit (inverseOpen f T).ι X)
    (fullNull_unitCompatible f T (laurent.op.obj X) _ _ (composite_unit f T X))

end AlgebraicGeometry.Scheme.Modules.GlobalSupportedSection.ParameterAuxiliarySupport
