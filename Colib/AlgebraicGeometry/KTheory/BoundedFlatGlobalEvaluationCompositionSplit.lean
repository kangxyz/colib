/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationCompositionModels
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitTracks
public import Colib.KTheory.Waldhausen.Iterated.SmallModelNativeNormalizationCompositionHomotopy

/-!
# The actual split track for normalized global pullback

The total small-model composition track is compared with the original geometric
track followed by binary chosen-zero normalization, without changing either endpoint.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.GrothendieckSections
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

private theorem evaluationUnliftedCompIso_split_hom {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationUnliftedCompIso f g).hom =
      normalizedWeakTransformation (boundedAboveFlatPerfectPullback_isExact (f ≫ g))
        ((boundedAboveFlatPerfectPullback_isExact g).comp
          (boundedAboveFlatPerfectPullback_isExact f))
        (boundedAboveFlatPerfectPullbackCompIso f g).hom ≫
      (exactNormalizationCompIso (boundedAboveFlatPerfectPullback_isExact g)
        (boundedAboveFlatPerfectPullback_isExact f)).hom := by
  rw [normalizedWeakTransformation_comp_exactNormalizationCompIso]
  simp only [evaluationUnliftedCompIso, normalizedCoefficientCompIso, Iso.trans_hom,
    Iso.symm_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom]
  rfl

/-- Realize the actual total small-model normalized pullback comparison. -/
def evaluationRawCompHomotopy {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Homotopy (boundedAboveFlatPerfectPullbackPrespectrumMap (f ≫ g))
      (boundedAboveFlatPerfectPullbackPrespectrumMap g ≫
        boundedAboveFlatPerfectPullbackPrespectrumMap f) :=
  (prespectrumTransformationHomotopy
    (F := evaluationRawMap (f ≫ g)) (G := evaluationRawMap g ≫ evaluationRawMap f)
    (evaluationRawCompIso f g).hom
    (fun x ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationRawCompIso f g).hom.app x))))).cast rfl
      (prespectrumFunctor.map_comp _ _)

/-- The actual chosen normalized composition retains the original split geometric track. -/
@[no_expose]
def evaluationRawCompTotalSplit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationRawCompHomotopy f g).RelHomotopy
      (boundedAboveFlatPerfectPullbackPrespectrumCompHomotopy f g) := by
  refine nativeModelAsSmallNormalizationCompTrackComparison
    (W := boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)
    (V := boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
    (U := boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (hH := boundedAboveFlatPerfectPullback_isExact (f ≫ g))
    (hF := boundedAboveFlatPerfectPullback_isExact g)
    (hG := boundedAboveFlatPerfectPullback_isExact f)
    (i := boundedAboveFlatPerfectPullbackCompIso f g)
    (i' := evaluationUnliftedCompIso f g)
    (hcomp := evaluationUnliftedCompIso_split_hom f g)
    (A := evaluationRawMap g) (B := evaluationRawMap f) (K := evaluationRawMap (f ≫ g))
    (hA := rfl) (hB := rfl) (hK := rfl)
    (hSource := rfl) (hTarget := rfl)
    (μ := evaluationRawCompIso f g) (hμ := ?_)
    (hweak := fun x ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationRawCompIso f g).hom.app x))))
    (hf := rfl) (hg := prespectrumFunctor.map_comp _ _)
  apply Iso.ext
  simp only [evaluationRawCompIso_eq_asSmall, modelAsSmallCompositionIso,
    Functor.transportIso_hom, eqToHom_refl, Category.id_comp, Category.comp_id]

private theorem ofLevels_continuousMap_eq
    {E F : Topology.LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    {H L : Homotopy f g} (J : H.RelHomotopy L) (H' L' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hL : ∀ n, L'.level n = L.level n)
    (n : ℕ) :
    ((J.ofLevels H' L' hH hL).level n).toContinuousMap = (J.level n).toContinuousMap :=
  rfl

/-- The existing normalized global comparison remains the geometric binary triangle. -/
theorem evaluationRawCompTotalSplit_level {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    ((evaluationRawCompTotalSplit f g).level n).toContinuousMap =
      ((boundedAboveFlatPerfectNormalizedCompTrackComparison f g).level n).toContinuousMap := by
  unfold evaluationRawCompTotalSplit boundedAboveFlatPerfectNormalizedCompTrackComparison
  rw [ofLevels_continuousMap_eq]
  exact nativeModelAsSmallNormalizationCompTrackComparison_level
    (W := boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)
    (V := boundedAboveFlatPerfectWaldhausen Y.toRingedSpace)
    (U := boundedAboveFlatPerfectWaldhausen X.toRingedSpace)
    (hH := boundedAboveFlatPerfectPullback_isExact (f ≫ g))
    (hF := boundedAboveFlatPerfectPullback_isExact g)
    (hG := boundedAboveFlatPerfectPullback_isExact f)
    (i := boundedAboveFlatPerfectPullbackCompIso f g)
    (i' := evaluationUnliftedCompIso f g)
    (hcomp := evaluationUnliftedCompIso_split_hom f g)
    (A := evaluationRawMap g) (B := evaluationRawMap f) (K := evaluationRawMap (f ≫ g))
    (hA := rfl) (hB := rfl) (hK := rfl)
    (hSource := rfl) (hTarget := rfl)
    (μ := evaluationRawCompIso f g) (hμ := by
      apply Iso.ext
      simp only [evaluationRawCompIso_eq_asSmall, modelAsSmallCompositionIso,
        Functor.transportIso_hom, eqToHom_refl, Category.id_comp, Category.comp_id])
    (hweak := fun x ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationRawCompIso f g).hom.app x))))
    (hf := rfl) (hg := prespectrumFunctor.map_comp _ _) n

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
