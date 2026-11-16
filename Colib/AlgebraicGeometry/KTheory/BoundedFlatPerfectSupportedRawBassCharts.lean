/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedRawBassStep
public import Colib.KTheory.Waldhausen.Iterated.NormalizationCompositionHomotopy

/-!
# Normalized chart comparisons of the supported point-set Bass seed

The normalized total track for the original geometric composition compares with the already
specified two-part split track. The comparison leaves the native exact pair maps and the
independent parameters unchanged.
-/
@[expose] public noncomputable section

open CategoryTheory Topology Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.SupportedRawBass

/-- Realize the total canonically normalized transformation of the actual supported pullbacks. -/
def normalizedPullbackCompTrack {A B C : Scheme.OpenPairs.{u}} (p : A ⟶ B) (q : B ⟶ C) :
    Homotopy (pullbackMap (p ≫ q)) (pullbackMap q ≫ pullbackMap p) := by
  let W := boundedAboveFlatPerfectSupportedWaldhausen C.hom
  let V := boundedAboveFlatPerfectSupportedWaldhausen B.hom
  let U := boundedAboveFlatPerfectSupportedWaldhausen A.hom
  let hH := boundedAboveFlatPerfectSupportedPullback_isExact (p ≫ q)
  let hF := boundedAboveFlatPerfectSupportedPullback_isExact q
  let hG := boundedAboveFlatPerfectSupportedPullback_isExact p
  let i := boundedAboveFlatPerfectSupportedPullbackCompIso p q
  exact (originalPrespectrumTransformationHomotopy W U hH.rebase (hF.rebase.comp hG.rebase)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    ((congrArg (CategoryTheory.rebaseFunctor (boundedAboveFlatPerfectSupportedPullback p)
      V.zero U.zero ((hG.zero V.isZero).iso U.isZero)).obj
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
    (normalizedWeakTransformation hH (hF.comp hG) i.hom ≫
      (exactNormalizationCompIso hF hG).hom)
    (fun K ↦ U.weq.comp_mem _ _
      (normalizedWeakTransformation_weak hH (hF.comp hG) i.hom
        (fun _ ↦ U.weq_iso _ inferInstance) K)
      (U.weq_iso _ inferInstance))).cast rfl
    (originalPrespectrumMap_comp W V U hF.rebase hG.rebase
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
      (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))

/-- The full native normalization triangle compares the total and original split tracks. -/
def normalizedPullbackCompComparison {A B C : Scheme.OpenPairs.{u}} (p : A ⟶ B) (q : B ⟶ C) :
    (normalizedPullbackCompTrack p q).RelHomotopy (pullbackCompositionHomotopy p q) :=
  exactNormalizationCompTrackComparison
    (boundedAboveFlatPerfectSupportedPullback_isExact (p ≫ q))
    (boundedAboveFlatPerfectSupportedPullback_isExact q)
    (boundedAboveFlatPerfectSupportedPullback_isExact p)
    (boundedAboveFlatPerfectSupportedPullbackCompIso p q)

/-- The normalization triangle is unchanged as an entire two-time continuous map. -/
theorem normalizedPullbackCompComparison_level {A B C : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : B ⟶ C) (n : ℕ) :
    ((normalizedPullbackCompComparison p q).level n).toContinuousMap =
      ((exactNormalizationCompTrackComparison
          (boundedAboveFlatPerfectSupportedPullback_isExact (p ≫ q))
          (boundedAboveFlatPerfectSupportedPullback_isExact q)
          (boundedAboveFlatPerfectSupportedPullback_isExact p)
          (boundedAboveFlatPerfectSupportedPullbackCompIso p q)).level n).toContinuousMap := rfl

variable (A : Scheme.QuasiCompactOpenPairs.{u})

/-- The total normalized track of the actual positive projection triangle. -/
def plusNormalizedHomotopy :
    Homotopy (pullbackMap (laurentProjection A))
      (pullbackMap (projection A) ≫ pullbackMap (plus A)) :=
  (normalizedPullbackCompTrack (plus A) (projection A)).cast
    (congrArg pullbackMap (plus_projection A)) rfl

/-- The total normalized track of the actual inverse projection triangle. -/
def minusNormalizedHomotopy :
    Homotopy (pullbackMap (laurentProjection A))
      (pullbackMap (projection A) ≫ pullbackMap (minus A)) :=
  (normalizedPullbackCompTrack (minus A) (projection A)).cast
    (congrArg pullbackMap (minus_projection A)) rfl

/-- The original positive split track is recovered by the entire native relative triangle. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRawSquare.lean:115-118"
  "adaptation" "The actual positive chart keeps its normalized and split tracks."]
def plusComparison : (plusNormalizedHomotopy A).RelHomotopy (plusHomotopy A) :=
  (normalizedPullbackCompComparison (plus A) (projection A)).cast
    (congrArg pullbackMap (plus_projection A)) rfl

/-- The inverse chart keeps its separate entire comparison, with no change of endpoints. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRawSquare.lean:120-123"
  "adaptation" "The inverse chart keeps its own normalized and split tracks."]
def minusComparison : (minusNormalizedHomotopy A).RelHomotopy (minusHomotopy A) :=
  (normalizedPullbackCompComparison (minus A) (projection A)).cast
    (congrArg pullbackMap (minus_projection A)) rfl

end AlgebraicGeometry.Scheme.Modules.SupportedRawBass
