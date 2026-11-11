/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterCoefficientModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenPairNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFullRestrictionTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLocalizationNull

/-!
# Integral Spec-row transport of the original full-open localization null

The two original weak zero transformations are postcomposed with their actual
full-open restrictions. Their common chosen-zero source and the strict full
Model square identify every original reversed time, without comparing the two
relative-open weak structures.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection

private theorem zero_postcomp {V W U : WideSubcategory preservesZero.{u}} (J : W ⟶ U) :
    zeroHom V U = zeroHom V W ≫ J := by
  simpa only [Category.id_comp] using (zeroHom_square (𝟙 V) J).symm

private def zeroPostcomp {V W U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶ U)
    (η : (zeroHom V W).hom.toFunctor ⟶ F.hom.toFunctor) :
    (zeroHom V U).hom.toFunctor ⟶ (F ≫ J).hom.toFunctor :=
  eqToHom (congrArg (fun k : V ⟶ U => k.hom.toFunctor) (zero_postcomp J)) ≫ Functor.whiskerRight η
    J.hom.toFunctor

private theorem zeroPostcomp_weak {V W U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W ⟶
  U)
    (η : (zeroHom V W).hom.toFunctor ⟶ F.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X)) (X : V.obj.Obj) :
    U.obj.waldhausen.weq ((zeroPostcomp F J η).app X) := by
  apply U.obj.waldhausen.weq.comp_mem
  · exact U.obj.waldhausen.weq_iso _ (by infer_instance)
  · exact J.hom.isExact.weak _ (hη X)

private theorem zeroPostcomp_level {V W U : WideSubcategory preservesZero.{u}} (F : V ⟶ W) (J : W
  ⟶ U)
    (η : (zeroHom V W).hom.toFunctor ⟶ F.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X)) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := zeroHom V U) (G := F ≫ J)
      (zeroPostcomp F J η)
      (zeroPostcomp_weak F J η hη)).level n =
      ((prespectrumTransformationHomotopy (F := zeroHom V W) (G := F) η hη).postcomp
        (prespectrumMap J)).level n :=
  (prespectrumTransformationHomotopy_source_transport_level
    (F := zeroHom V U) (F' := zeroHom V W ≫ J) (G := F ≫ J) (zero_postcomp J)
    (Functor.whiskerRight η J.hom.toFunctor) (fun X => J.hom.isExact.weak _ (hη X))
    (zeroPostcomp_weak F J η hη) n).trans
      (prespectrumTransformationHomotopy_postcomp_level (F := zeroHom V W) (G := F) η hη J n)

private theorem fullNull_naturality {V W T U V' W' T' U' : WideSubcategory preservesZero.{u}}
    (f : V ⟶ W) (g : W ⟶ T) (J : T ⟶ U)
    (f' : V' ⟶ W') (g' : W' ⟶ T') (J' : T' ⟶ U')
    (a : V ⟶ V') (b : U ⟶ U')
    (h : ((f ≫ g) ≫ J) ≫ b = a ≫ ((f' ≫ g') ≫ J'))
    (η : (zeroHom V T).hom.toFunctor ⟶ (f ≫ g).hom.toFunctor)
    (η' : (zeroHom V' T').hom.toFunctor ⟶ (f' ≫ g').hom.toFunctor)
    (hη : ∀ X, T.obj.waldhausen.weq (η.app X))
    (hη' : ∀ X, T'.obj.waldhausen.weq (η'.app X))
    (n : ℕ) (s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumMap b).map n ((prespectrumMap J).map n
      ((prespectrumCompositeZeroNullHomotopy f g η hη).level n (s, x))) =
    (prespectrumMap J').map n
      ((prespectrumCompositeZeroNullHomotopy f' g' η' hη').level n
        (s, (prespectrumMap a).map n x)) := by
  have hn := prespectrumZeroTransformationHomotopy_naturality
    ((f ≫ g) ≫ J) ((f' ≫ g') ≫ J') a b h
    (zeroPostcomp (f ≫ g) J η) (zeroPostcomp (f' ≫ g') J' η')
    (zeroPostcomp_weak (f ≫ g) J η hη)
    (zeroPostcomp_weak (f' ≫ g') J' η' hη') n
  have hv := congrArg (fun H => H (unitInterval.symm s, x)) hn
  change (prespectrumMap b).map n
    ((prespectrumTransformationHomotopy _ _).level n (unitInterval.symm s, x)) =
      (prespectrumTransformationHomotopy _ _).level n
        (unitInterval.symm s, (prespectrumMap a).map n x) at hv
  rw [zeroPostcomp_level, zeroPostcomp_level] at hv
  exact hv

private theorem map_comp_apply {V W U : WideSubcategory preservesZero.{u}} (f : V ⟶ W) (g : W ⟶ U)
    (n : ℕ) (x : (prespectrum V).space n) :
    (prespectrumMap (f ≫ g)).map n x =
      (prespectrumMap g).map n ((prespectrumMap f).map n x) :=
  congrArg (fun k => k.map n x) (prespectrumFunctor.map_comp f g)

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The supported Spec row retains the complete original full-open composite Model map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientNull.lean:101"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem supportedFullRestriction_model_square :
    (Functor.whiskerLeft specUnder (ParameterModels.forget f.left) ≫
        Functor.whiskerLeft specUnder (parameterFullRestriction f)) ≫
        (parameterRowModelIso P).hom =
      (parameterSupportedRowIso f).hom ≫
        ((supportedRowForget f ≫ openRowChangeWeak f) ≫ globalOpenRestriction f) := by
  rw [Category.assoc, fullRestriction_model_square, ← Category.assoc,
    ← parameterSupportedRowIso_forget, Category.assoc,
    Category.assoc, globalFullRestriction_factor]

/-- Every original null time agrees under the actual supported and full-open Spec-row maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientNull.lean:112"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fullNull_row_square (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((ParameterModels.supported f.left).obj (specUnder.obj a))).space n) :
    (prespectrumMap ((parameterRowModelIso P).hom.app a)).map n
      ((prespectrumMap ((ParameterModels.openRestriction f.left).app (specUnder.obj a))).map n
        (((ParameterModels.supportedOpenNull f.left).homotopy (specUnder.obj a)).level n
          (s, x))) =
      (prespectrumMap ((globalOpenRestriction f).app a)).map n
        (((globalSupportedOpenNull f).homotopy a).level n
          (s, (prespectrumMap ((parameterSupportedRowIso f).hom.app a)).map n x)) := by
  apply fullNull_naturality
    ((ParameterModels.forget f.left).app (specUnder.obj a))
    ((ParameterModels.changeWeak f.left).app (specUnder.obj a))
    ((ParameterModels.openRestriction f.left).app (specUnder.obj a))
    ((supportedRowForget f).app a) ((openRowChangeWeak f).app a)
    ((globalOpenRestriction f).app a)
    ((parameterSupportedRowIso f).hom.app a) ((parameterRowModelIso P).hom.app a)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, parameterFullRestriction,
    Category.assoc] using congrArg (fun k => k.app a)
      (supportedFullRestriction_model_square f)

/-- The same complete null agrees with the original fine coefficient localization null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterCoefficientNull.lean:134"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem fullNull_coefficient_square (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((ParameterModels.supported f.left).obj (specUnder.obj a))).space n) :
    (prespectrumMap ((parameterCoefficientRestriction P).app a)).map n
      ((prespectrumMap ((ParameterModels.openRestriction f.left).app (specUnder.obj a))).map n
        (((ParameterModels.supportedOpenNull f.left).homotopy (specUnder.obj a)).level n
          (s, x))) =
      (prespectrumMap (boundedAboveFlatCoefficientOpenRestrictionModelMap f a)).map n
        (((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level n
          (s, (prespectrumMap (((parameterSupportedRowIso f).hom.app a) ≫
            (supportedRowRestriction f).app a)).map n x)) := by
  have hr := fullNull_row_square f a n s x
  have h := congrArg (fun y => (prespectrumMap ((rowRestriction P).app a)).map n y) hr
  have hs := congrArg (fun k => (prespectrumMap (k.app a)).map n
    (((globalSupportedOpenNull f).homotopy a).level n
      (s, (prespectrumMap ((parameterSupportedRowIso f).hom.app a)).map n x)))
        (globalOpenRestriction_square f)
  simp only [NatTrans.comp_app, map_comp_apply] at hs
  have hn := globalSupportedOpenNull_restriction f a n s
    ((prespectrumMap ((parameterSupportedRowIso f).hom.app a)).map n x)
  simpa only [parameterCoefficientRestriction, NatTrans.comp_app, map_comp_apply] using
    h.trans (hs.trans (congrArg
      (fun y => (prespectrumMap (boundedAboveFlatCoefficientOpenRestrictionModelMap f a)).map n y)
        hn))

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

