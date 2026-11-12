/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionEvaluationNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTower
public import Colib.AlgebraicGeometry.KTheory.Bass.NegativeGroups

/-!
# Original K-zero at the bottom of the native ambient Bass family

The original perfect K-zero functor on quasi-compact schemes is naturally the
actual finite stage-zero group. The comparison uses the existing original
normalized evaluation and bounded-flat inclusion, retaining arbitrary coefficient
pullbacks. Polynomial/Laurent geometry and successor comparisons remain separate. This
comparison uses the original perfect K-zero and does not redefine the original
negative groups. Supported comparisons and TT identification remain separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry.RingedSpace
open CategoryTheory AlgebraicGeometry Opposite Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Original perfect K-zero computes degree zero of the original localized spectrum. -/
def perfectKZeroLocalizedStableIso (X : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ) :
    Bass.perfectKZeroFunctor.obj X ≅
      (perfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor 0).obj X :=
  (originalKStableEquiv (perfectComplexesWaldhausen X.unop.obj.toRingedSpace) 0).toAddCommGrpIso

/-- The comparison preserves every original derived-pullback K-zero map. -/
@[reassoc]
theorem perfectKZeroLocalizedStableIso_naturality
    {X Y : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ} (f : X ⟶ Y) :
    Bass.perfectKZeroFunctor.map f ≫ (perfectKZeroLocalizedStableIso Y).hom =
      (perfectKZeroLocalizedStableIso X).hom ≫
        (perfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor 0).map f := by
  ext a
  exact perfectLocalizedPullback_originalK_naturality f.unop.hom 0 a.toMul

/-- The unchanged original scheme K-zero functor retains all its original maps. -/
def perfectKZeroLocalizedStableNatIso :
    Bass.perfectKZeroFunctor.{u} ≅
      perfectLocalizedSpectrumFunctor ⋙ localizedStableHomotopyFunctor 0 :=
  NatIso.ofComponents perfectKZeroLocalizedStableIso
    (fun f ↦ perfectKZeroLocalizedStableIso_naturality f)

/-- Original perfect K-zero on each compact native fiber is the actual stage-zero bottom. -/
def boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso
    {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] :
    boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Bass.perfectKZeroFunctor ≅
      boundedAboveFlatCoefficientAmbientBassDiagram P 0 ⋙ stableHomotopyFunctor 0 :=
  Functor.isoWhiskerLeft (boundedAboveFlatCoefficientQuasiCompactRow P)
      perfectKZeroLocalizedStableNatIso ≪≫
    (Functor.isoWhiskerRight
      (boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P)
      (localizedStableHomotopyFunctor 0)).symm

/-- The comparison keeps the actual evaluation and original perfect K-zero representative. -/
@[reassoc]
theorem boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso_evaluation
    {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R) :
    (boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso P).hom.app a ≫
      (stableHomotopyFunctor 0).map
        (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)) =
    (perfectKZeroLocalizedStableIso ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a)).hom
      := by
  let A := Functor.isoWhiskerLeft (boundedAboveFlatCoefficientQuasiCompactRow P)
    perfectKZeroLocalizedStableNatIso
  let E := Functor.isoWhiskerRight
    (boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P)
    (localizedStableHomotopyFunctor 0)
  have hE : E.hom.app a = (stableHomotopyFunctor 0).map
      (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)) := by
    simp only [E, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso_hom_app,
      localizedStableHomotopyFunctor_original_map]
  change (A.hom.app a ≫ E.inv.app a) ≫ _ = _
  rw [← hE, Category.assoc, ← NatTrans.comp_app, E.inv_hom_id,
    NatTrans.id_app]
  exact Category.comp_id (A.hom.app a)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassKZeroComparison.lean:32"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectKZeroLocalizedStableIso

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassKZeroComparison.lean:39"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectKZeroLocalizedStableIso_naturality

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassKZeroComparison.lean:48"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  perfectKZeroLocalizedStableNatIso

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassKZeroComparison.lean:55"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassKZeroComparison.lean:66"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientAmbientBassBottomZeroNatIso_evaluation


end AlgebraicGeometry.Scheme.Modules
