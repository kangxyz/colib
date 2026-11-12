/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedRow
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalOpenModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedCoarseNull
/-! # The actual global supported zero-to-image null and complete restriction comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
open AlgebraicGeometry.Scheme.Modules.Complex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The unique map from the original global zero to the unchanged supported inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNull.lean:32"
  "adaptation" "Original supported global zero-to-image whole null and exact restriction"]
def globalZeroToOpen (a : Under R) :
    (Functor.const ((supportedRow f).obj a).obj.Obj).obj ((globalRow Q).obj a).obj.waldhausen.zero ⟶
      ((supportedRowForget f).app a).hom.toFunctor where
  app S := ((globalRow Q).obj a).obj.waldhausen.isZero.to_ S.obj
  naturality _ _ _ := ((globalRow Q).obj a).obj.waldhausen.isZero.eq_of_src _ _

@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNull.lean:38"
  "adaptation" "Original supported global zero-to-image whole null and exact restriction"]
private theorem weak_of_zero_source {C : Type*} [Category* C] (W : Structure C)
    {Z X : C} (hZ : IsZero Z) (g : Z ⟶ X) (h : W.weq (W.isZero.to_ X)) : W.weq g := by
  have he : g = (hZ.iso W.isZero).hom ≫ W.isZero.to_ X := hZ.eq_of_src _ _
  rw [he]
  exact W.weq.comp_mem _ _ (W.weq_iso _ (by infer_instance)) h

/-- Original support makes this original zero-to-image map coarse weak. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNull.lean:45"
  "adaptation" "Original supported global zero-to-image whole null and exact restriction"]
theorem globalZeroToOpen_weak (a : Under R) (S : ((supportedRow f).obj a).obj.Obj) :
    (openModel f a).obj.waldhausen.weq ((globalZeroToOpen f a).app S) := by
  apply (Structure.withInverseImageWeak_weq_iff
    ((openSourceTransformation f).app a).hom.isExact _).mpr
  apply weak_of_zero_source (boundedAboveFlatCoefficientOpenModel f a).obj.waldhausen
    (((openSourceTransformation f).app a).hom.isExact.zero
      ((globalRow Q).obj a).obj.waldhausen.isZero)
  exact boundedAboveFlatCoefficientSupportedZeroToOpen_weak f a
    (((supportedRowRestriction f).app a).hom.toFunctor.obj S)

/-- Reverse precisely the actual global weak zero-to-inclusion realization. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNull.lean:56"
  "adaptation" "Original supported global zero-to-image whole null and exact restriction"]
def globalSupportedOpenNull :
    DiagramNullHomotopy (Functor.whiskerRight (supportedRowForget f) prespectrumFunctor)
      (Functor.whiskerRight (openRowChangeWeak f) prespectrumFunctor) :=
  modelDiagramZeroNull (supportedRowForget f) (openRowChangeWeak f)
    (globalZeroToOpen f) (globalZeroToOpen_weak f)

/-- The two actual strict Model squares give the exact composite localization square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNull.lean:63"
  "adaptation" "Original supported global zero-to-image whole null and exact restriction"]
theorem globalSupportedOpen_restriction :
    (supportedRowForget f ≫ openRowChangeWeak f) ≫ openRowRestriction f =
      supportedRowRestriction f ≫
        (boundedAboveFlatCoefficientSupportedForgetModelTransformation f ≫
          boundedAboveFlatCoefficientOpenChangeWeakModelTransformation f) := by
  rw [Category.assoc, openRowRestriction_changeWeak, ← Category.assoc,
    ← supportedRowRestriction_forget, Category.assoc]

/-- Restriction retains every value of the original null at the identical reversed time. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionLocalizationNull.lean:72"
  "adaptation" "Original supported global zero-to-image whole null and exact restriction"]
theorem globalSupportedOpenNull_restriction (a : Under R) (n : ℕ) (s : unitInterval)
    (x : (prespectrum ((supportedRow f).obj a)).space n) :
    (prespectrumMap ((openRowRestriction f).app a)).map n
        (((globalSupportedOpenNull f).homotopy a).level n (s, x)) =
      ((boundedAboveFlatCoefficientSupportedOpenDiagramNull f).homotopy a).level n
        (s, (prespectrumMap ((supportedRowRestriction f).app a)).map n x) :=
  prespectrumCompositeZeroNullHomotopy_naturality
    ((supportedRowForget f).app a) ((openRowChangeWeak f).app a)
    (boundedAboveFlatCoefficientSupportedForgetModelMap f a)
    (boundedAboveFlatCoefficientOpenChangeWeakModelMap f a)
    ((supportedRowRestriction f).app a) ((openRowRestriction f).app a)
    (congrArg (fun η => η.app a) (globalSupportedOpen_restriction f))
    (globalZeroToOpen f a) (boundedAboveFlatCoefficientSupportedZeroToOpen f a)
    (globalZeroToOpen_weak f a) (boundedAboveFlatCoefficientSupportedZeroToOpen_weak f a) n s x

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
