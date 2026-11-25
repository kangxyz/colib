/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumAssociativity
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleMiddle
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitTracks
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels
public import Colib.Topology.Prespectrum.RelativeHomotopyHorizontal
public import Colib.Topology.Prespectrum.RelativeHomotopyComposition
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Original associativity tracks for three bounded-flat pullbacks

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/TripleTrack.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RingedSpace Topology
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

/-- The first route of the genuine geometric comparison is the literal postcomposed track. -/
theorem boundedAboveFlatPerfectNormalizedTripleLeftTrack_level {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (n : ℕ) :
    (boundedAboveFlatPerfectNormalizedTripleLeftTrack f g h).level n =
      ((BoundedFlatPerfectSplitTripleSimplex.normalizedMiddlePasting f g h).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x) =
    ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact DFunLike.congr_fun (boundedAboveFlatPerfectNormalizedCompTrack_level f (g ≫ h) n) _
  · change (boundedAboveFlatPerfectPullbackPrespectrumMap f).map n
      ((boundedAboveFlatPerfectNormalizedCompTrack g h).level n _) = _
    rw [boundedAboveFlatPerfectNormalizedCompTrack_level]
    symm
    exact DFunLike.congr_fun
      (originalPrespectrumTransformationHomotopy_postcomp_level
        (boundedAboveFlatPerfectNormalizedPullback_exact (g ≫ h))
        ((boundedAboveFlatPerfectNormalizedPullback_exact h).comp
          (boundedAboveFlatPerfectNormalizedPullback_exact g))
        (boundedAboveFlatPerfectNormalizedPullback_exact f)
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero _) _
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero _)
        (boundedAboveFlatPerfectNormalizedPullbackCompIso g h).hom
        (fun _ ↦ (W Y).weq_iso _ inferInstance) n) _

/-- The second route retains the original precomposed track and both associativity transports. -/
theorem boundedAboveFlatPerfectNormalizedTripleRightTrack_level {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (n : ℕ) :
    (boundedAboveFlatPerfectNormalizedTripleRightTrack f g h).level n =
      ((BoundedFlatPerfectSplitTripleSimplex.normalizedMiddlePasting f g h).at 1).level n := by
  rw [boundedAboveFlatPerfectNormalizedTripleRightTrack, Homotopy.cast_level,
    Homotopy.RelHomotopy.at_one]
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  change ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x) =
    ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (s, x)
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact DFunLike.congr_fun (boundedAboveFlatPerfectNormalizedCompTrack_level (f ≫ g) h n) _
  · change (boundedAboveFlatPerfectNormalizedCompTrack f g).level n
      (_, (boundedAboveFlatPerfectPullbackPrespectrumMap h).map n x) = _
    rw [boundedAboveFlatPerfectNormalizedCompTrack_level]
    symm
    exact DFunLike.congr_fun
      (originalPrespectrumTransformationHomotopy_precomp_level
        (boundedAboveFlatPerfectNormalizedPullback_exact h)
        (boundedAboveFlatPerfectNormalizedPullback_exact (f ≫ g))
        ((boundedAboveFlatPerfectNormalizedPullback_exact g).comp
          (boundedAboveFlatPerfectNormalizedPullback_exact f))
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero _)
        (boundedAboveFlatPerfectNormalizedPullback_obj_zero _) _
        (boundedAboveFlatPerfectNormalizedPullbackCompIso f g).hom
        (fun _ ↦ (W X).weq_iso _ inferInstance) n) _

namespace BoundedFlatPerfectSplitTripleSimplex

private theorem ofLevels_continuousMap_eq
    {E F : LoopPrespectrum.{u}} {f g f' g' : E ⟶ F}
    {H K : Homotopy f g} (J : H.RelHomotopy K) (H' K' : Homotopy f' g')
    (hH : ∀ n, H'.level n = H.level n) (hK : ∀ n, K'.level n = K.level n)
    (n : ℕ) :
    ((J.ofLevels H' K' hH hK).level n).toContinuousMap = (J.level n).toContinuousMap :=
  rfl

/-- The normalized middle simplex uses the exact level of the native associativity pasting. -/
theorem normalized_middle_pasting_level {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (n : ℕ) :
    ((normalizedMiddlePasting f g h).level n).toContinuousMap =
      ((boundedAboveFlatPerfectNormalizedTripleTrackComparison f g h).level n).toContinuousMap := by
  -- Unfold the checked comparison, so its existing endpoint witnesses are inferred
  -- from the occurrence of `ofLevels` rather than synthesized as new obligations.
  unfold boundedAboveFlatPerfectNormalizedTripleTrackComparison
  rw [ofLevels_continuousMap_eq]

/-- Both independent parameters evaluate to the comparison on the actual normalized tracks. -/
theorem normalized_native_comparison {X Y Z T : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (n : ℕ) (r s : unitInterval) (x : (originalPrespectrum (W T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n
      ((BoundedFlatPerfectSplitTripleParameters.normalizedLeftParameter.symm.trans
        BoundedFlatPerfectSplitTripleParameters.normalizedRightParameter) (r, s), x) =
      (boundedAboveFlatPerfectNormalizedTripleTrackComparison f g h).level n (r, (s, x)) :=
  (normalized_native f g h n r s x).trans
    (DFunLike.congr_fun (normalized_middle_pasting_level f g h n) (r, (s, x)))

end BoundedFlatPerfectSplitTripleSimplex

end AlgebraicGeometry.Scheme.Modules
