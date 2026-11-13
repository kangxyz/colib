/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionSpectrumComparison
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumPullback
public import Colib.AlgebraicGeometry.KTheory.PerfectLocalizedPullback
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.CategoryTheory.Waldhausen.AsSmall.Whiskering

/-!
# Actual geometric comparison of the original joint coefficient evaluation

The original cocartesian evaluation transition, common-universe lifting and both
actual zero normalizations give a whole based prespectrum homotopy for every joint
scheme/coefficient arrow. Its image in the stable localization is a genuine natural
isomorphism of the original joint diagrams. Every native coefficient row is obtained
by restriction of that same family. Perfect comparison uses the original bounded-flat
inclusion and arbitrary derived pullback on a quasi-compact row; no flatness is needed.
These connective comparisons do not assert Laurent-seed or telescope compatibility.
-/
@[expose] public section

open CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open AlgebraicGeometry.RingedSpace Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}}
attribute [local irreducible] boundedAboveFlatCoefficientOriginalEvaluation

/-- The original geometric pullback Model map, with its original canonical zero normalization. -/
def boundedAboveFlatCoefficientOriginalModelMap {i k : Index R} (f : i ⟶ k) :
    asSmallCategory (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen (space k).toRingedSpace) :=
  asSmallCategoryMap _ _ (boundedAboveFlatPerfectPullback_isExact
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)).rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)

set_option maxHeartbeats 1200000 in
-- Elaborating both concrete lifted normalization composites exceeds the standard budget.
/-- The comparison retains the actual original evaluation transition and both chosen-zero paths. -/
def boundedAboveFlatCoefficientSectionEvaluationIso {i k : Index R} (f : i ⟶ k) :
    (boundedAboveFlatCoefficientSectionModelMap f ≫
      boundedAboveFlatCoefficientSectionEvaluationModelMap k).hom.toFunctor ≅
      (boundedAboveFlatCoefficientSectionEvaluationModelMap i ≫
        boundedAboveFlatCoefficientOriginalModelMap f).hom.toFunctor := by
  let p := boundedAboveFlatPerfectPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
  let h := boundedAboveFlatPerfectPullback_isExact
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f)
  let z := CategoryTheory.rebaseFunctorIso p
    (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).zero
    (boundedAboveFlatPerfectWaldhausen (space k).toRingedSpace).zero
    ((h.zero (boundedAboveFlatPerfectWaldhausen (space i).toRingedSpace).isZero).iso
      (boundedAboveFlatPerfectWaldhausen (space k).toRingedSpace).isZero)
  let e := asSmallWhiskerIso
    (C := BoundedAboveFlatCoefficientSections i)
    (D := (boundedAboveFlatPerfectComplex (space i).toRingedSpace).FullSubcategory)
    (E := (boundedAboveFlatPerfectComplex (space k).toRingedSpace).FullSubcategory)
    (boundedAboveFlatCoefficientOriginalEvaluation i)
    (boundedAboveFlatCoefficientSectionsMap f ⋙ boundedAboveFlatCoefficientOriginalEvaluation k)
    p _ (boundedAboveFlatCoefficientSectionReindexIso f) z
  change (boundedAboveFlatCoefficientSectionsMap f ⋙
      (boundedAboveFlatCoefficientSectionEvaluationModelMap k).hom.toFunctor) ≅
    ((boundedAboveFlatCoefficientSectionEvaluationModelMap i).hom.toFunctor ⋙
      (boundedAboveFlatCoefficientOriginalModelMap f).hom.toFunctor)
  exact isoWhiskerLeft (boundedAboveFlatCoefficientSectionsMap f)
      (boundedAboveFlatCoefficientSectionEvaluationNormalizationIso k).symm ≪≫
    (Functor.associator (boundedAboveFlatCoefficientSectionsMap f)
      (boundedAboveFlatCoefficientOriginalEvaluation k) AsSmall.up).symm ≪≫ e ≪≫
    isoWhiskerRight (boundedAboveFlatCoefficientSectionEvaluationNormalizationIso i) _

/-- The whole original coefficient/scheme comparison retains every original structure map. -/
def boundedAboveFlatCoefficientSectionEvaluationHomotopy {i k : Index R} (f : i ⟶ k) :
    Homotopy
      ((boundedAboveFlatCoefficientSectionPrespectrumFunctor R).map f ≫
        boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap k)
      (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap i ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
          :=
  (prespectrumTransformationHomotopy
    (V := boundedAboveFlatCoefficientSectionModel i)
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen (space k).toRingedSpace))
    (F := boundedAboveFlatCoefficientSectionModelMap f ≫
      boundedAboveFlatCoefficientSectionEvaluationModelMap k)
    (G := boundedAboveFlatCoefficientSectionEvaluationModelMap i ≫
      boundedAboveFlatCoefficientOriginalModelMap f)
    (boundedAboveFlatCoefficientSectionEvaluationIso f).hom
    (fun _ ↦ (boundedAboveFlatPerfectWaldhausen (space k).toRingedSpace).asSmall.weq_iso _
      inferInstance)).cast
      (prespectrumFunctor.map_comp _ _) (prespectrumFunctor.map_comp _ _)

/-- The same original joint section prespectra in the genuine stable localization. -/
def boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor (R : CommRingCat.{u}) :
    Index R ⥤ StableLocalization.{u+1} :=
  boundedAboveFlatCoefficientSectionPrespectrumFunctor R ⋙ toStableLocalization

/-- Actual evaluation is inverted only by its proved all-signed stable equivalence. -/
def boundedAboveFlatCoefficientSectionEvaluationLocalizedIso (i : Index R) :
    (boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor R).obj i ≅
      boundedAboveFlatLocalizedSpectrum (space i) :=
  stableLocalizationIso (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap i)
    (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap_isStableEquivalence i)

/-- The forward localized comparison is precisely the original normalized evaluation map. -/
@[simp] theorem boundedAboveFlatCoefficientSectionEvaluationLocalizedIso_hom (i : Index R) :
    (boundedAboveFlatCoefficientSectionEvaluationLocalizedIso i).hom =
      toStableLocalization.map (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap i) := rfl

/-- Every joint square commutes in the localization by its actual whole comparison track. -/
theorem boundedAboveFlatCoefficientSectionEvaluationLocalizedIso_naturality {i k : Index R}
    (f : i ⟶ k) :
    (boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor R).map f ≫
        (boundedAboveFlatCoefficientSectionEvaluationLocalizedIso k).hom =
      (boundedAboveFlatCoefficientSectionEvaluationLocalizedIso i).hom ≫
        boundedAboveFlatLocalizedPullback (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map
      f) := by
  change toStableLocalization.map
      ((boundedAboveFlatCoefficientSectionPrespectrumFunctor R).map f) ≫
      toStableLocalization.map (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap k) =
    toStableLocalization.map (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap i) ≫
      toStableLocalization.map
        (boundedAboveFlatPerfectPullbackPrespectrumMap
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map f))
  have h := toStableLocalization_map_eq_of_homotopy
    (boundedAboveFlatCoefficientSectionEvaluationHomotopy f)
  simpa only [Functor.map_comp] using h

/-- The actual joint evaluation family is a genuine natural isomorphism. -/
def boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso (R : CommRingCat.{u}) :
    boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor R ≅
      AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R ⋙
        boundedAboveFlatLocalizedSpectrumFunctor :=
  NatIso.ofComponents boundedAboveFlatCoefficientSectionEvaluationLocalizedIso
    boundedAboveFlatCoefficientSectionEvaluationLocalizedIso_naturality

/-- The exact original forward evaluation is retained at every joint component. -/
@[simp] theorem boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso_hom_app
    (i : Index R) :
    (boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso R).hom.app i =
      toStableLocalization.map (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap i) := rfl

/-- Restrict the same original family to an arbitrary actual coefficient row. -/
def boundedAboveFlatCoefficientSectionRowEvaluationLocalizedNatIso (P : Over (Spec R)) :
    row P ⋙ boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor R ≅
      row P ⋙ AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R ⋙
        boundedAboveFlatLocalizedSpectrumFunctor :=
  isoWhiskerLeft (row P) (boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso R)

/-- The unchanged native coefficient fibers as quasi-compact schemes with all original maps. -/
def boundedAboveFlatCoefficientQuasiCompactRow (P : Over (Spec R)) [CompactSpace P.left] :
    Under R ⥤ AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ where
  obj a := op ⟨space (op P, a), compactSpace_space (op P, a)⟩
  map g := (ObjectProperty.homMk
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (𝟙 (op P), g))).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op P, a)
  map_comp {a b c} g h := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_comp
      (i := (op P, a)) (k := (op P, b)) (l := (op P, c))
      (𝟙 (op P), g) (𝟙 (op P), h)

/-- The quasi-compact lift retains precisely the original native geometric row. -/
theorem boundedAboveFlatCoefficientQuasiCompactRow_inclusion (P : Over (Spec R))
    [CompactSpace P.left] :
    boundedAboveFlatCoefficientQuasiCompactRow P ⋙
      AlgebraicGeometry.Scheme.quasiCompactSchemesInclusion.op =
      row P ⋙ AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R := rfl

/-- Original perfect spectra and arbitrary derived pullbacks on the actual compact native row. -/
def boundedAboveFlatCoefficientperfectLocalizedSpectrumFunctor (P : Over (Spec R))
    [CompactSpace P.left] : Under R ⥤ StableLocalization.{u+1} :=
  boundedAboveFlatCoefficientQuasiCompactRow P ⋙ perfectLocalizedSpectrumFunctor

/-- The original bounded-flat inclusion is natural for arbitrary derived pullback. -/
def boundedAboveFlatCoefficientPerfectInclusionLocalizedNatIso (P : Over (Spec R))
    [CompactSpace P.left] :
    row P ⋙ AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R ⋙
        boundedAboveFlatLocalizedSpectrumFunctor ≅
      boundedAboveFlatCoefficientperfectLocalizedSpectrumFunctor P :=
  isoWhiskerLeft (boundedAboveFlatCoefficientQuasiCompactRow P)
      boundedAboveFlatPerfectSpectrumNatIso

/-- The same evaluation and literal inclusion compare perfect spectra on a quasi-compact row. -/
def boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso (P : Over (Spec R))
    [CompactSpace P.left] :
    row P ⋙ boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor R ≅
      boundedAboveFlatCoefficientperfectLocalizedSpectrumFunctor P :=
  boundedAboveFlatCoefficientSectionRowEvaluationLocalizedNatIso P ≪≫
    boundedAboveFlatCoefficientPerfectInclusionLocalizedNatIso P

/-- Every perfect component is the same actual normalized evaluation followed by inclusion. -/
@[simp] theorem boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso_hom_app
    (P : Over (Spec R)) [CompactSpace P.left] (a : Under R) :
    (boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso P).hom.app a =
      toStableLocalization.map
        (boundedAboveFlatCoefficientSectionPerfectEvaluationPrespectrumMap (op P, a)) := by
  change toStableLocalization.map
      (boundedAboveFlatCoefficientSectionEvaluationPrespectrumMap (op P, a)) ≫
    toStableLocalization.map (exactOriginalPrespectrumMap _ _
      (boundedAboveFlatPerfectInclusion_isExact (space (op P, a)).toRingedSpace)) = _
  rw [← Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:41"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientOriginalModelMap

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:51"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationIso

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:80"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationHomotopy

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:99"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionLocalizedSpectrumFunctor

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:104"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationLocalizedIso

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:111"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationLocalizedIso_hom

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:116"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationLocalizedIso_naturality

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:133"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:141"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionEvaluationLocalizedNatIso_hom_app

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:147"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionRowEvaluationLocalizedNatIso

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:154"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientQuasiCompactRow

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:171"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientQuasiCompactRow_inclusion

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:178"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientperfectLocalizedSpectrumFunctor

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:183"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientPerfectInclusionLocalizedNatIso

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:191"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso

attribute [colib_ref "quillen"
  "PerfectComplexes/BoundedFlat/CoefficientSectionEvaluationNaturality.lean:199"
  "adaptation" "Actual coefficient evaluation, original K-classes and geometric pullback."]
  boundedAboveFlatCoefficientSectionPerfectRowEvaluationLocalizedNatIso_hom_app


end AlgebraicGeometry.Scheme.Modules
