/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectSupportedRawPullbackTrack
public import Colib.KTheory.Waldhausen.Iterated.ExactCoherence
public import Colib.Topology.Prespectrum.HomotopyPushout
public import Colib.Topology.Prespectrum.HomotopyLoop
public import Colib.Topology.Prespectrum.MappingCone

/-!
# Point-set Bass seed of a quasi-compact open pair

The positive and inverse native pullback tracks glue the actual supported double cylinder.
The source null uses the positive split track and then contracts the original positive cone leg.
-/
@[expose] public noncomputable section

open CategoryTheory Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.SupportedRawBass

open Scheme.Bass

/-- The native original iterated-S prespectrum of a supported open pair. -/
abbrev rawSpectrum (A : Scheme.OpenPairs.{u}) : LoopPrespectrum.{u+1} :=
  originalPrespectrum (boundedAboveFlatPerfectSupportedWaldhausen A.hom)

/-- The original exact pullback on the native supported prespectrum. -/
abbrev pullbackMap {A B : Scheme.OpenPairs.{u}} (p : A ⟶ B) :
    rawSpectrum B ⟶ rawSpectrum A :=
  boundedAboveFlatPerfectSupportedPullbackPrespectrumMap p

/-- The two original composition tracks with the original concatenation clock. -/
def pullbackCompositionHomotopy {A B C : Scheme.OpenPairs.{u}} (p : A ⟶ B) (q : B ⟶ C) :
    Homotopy (pullbackMap (p ≫ q)) (pullbackMap q ≫ pullbackMap p) :=
  (exactOriginalPrespectrumIsoHomotopy _ _
    (boundedAboveFlatPerfectSupportedPullback_isExact (p ≫ q))
    ((boundedAboveFlatPerfectSupportedPullback_isExact q).comp
      (boundedAboveFlatPerfectSupportedPullback_isExact p))
    (boundedAboveFlatPerfectSupportedPullbackCompIso p q)).trans
    (exactOriginalPrespectrumMapCompHomotopy _ _ _
      (boundedAboveFlatPerfectSupportedPullback_isExact q)
      (boundedAboveFlatPerfectSupportedPullback_isExact p))

variable (A : Scheme.QuasiCompactOpenPairs.{u})

/-- Polynomial projection on the given supported pair. -/
abbrev projection := (pairPolynomialProjection.app A).hom
/-- Laurent projection on the given supported pair. -/
abbrev laurentProjection := (pairLaurentProjection.app A).hom
/-- Positive polynomial chart of the Laurent product of the supported pair. -/
abbrev plus := (pairPlus.app A).hom
/-- Inverse polynomial chart of the Laurent product of the supported pair. -/
abbrev minus := (pairMinus.app A).hom

/-- The positive chart projection triangle on the actual open-pair morphisms. -/
theorem plus_projection : plus A ≫ projection A = laurentProjection A :=
  congrArg (fun f ↦ f.hom) (pairPlus_projection A)

/-- The inverse chart projection triangle on the actual open-pair morphisms. -/
theorem minus_projection : minus A ≫ projection A = laurentProjection A :=
  congrArg (fun f ↦ f.hom) (pairMinus_projection A)

/-- The actual positive composition track, not a strict cone path. -/
def plusHomotopy :
    Homotopy (pullbackMap (laurentProjection A))
      (pullbackMap (projection A) ≫ pullbackMap (plus A)) :=
  (pullbackCompositionHomotopy (plus A) (projection A)).cast
    (congrArg pullbackMap (plus_projection A)) rfl

/-- The independent inverse chart retains its own original composition track. -/
def minusHomotopy :
    Homotopy (pullbackMap (laurentProjection A))
      (pullbackMap (projection A) ≫ pullbackMap (minus A)) :=
  (pullbackCompositionHomotopy (minus A) (projection A)).cast
    (congrArg pullbackMap (minus_projection A)) rfl

/-- The supported span is the native reduced double cylinder. -/
def span : LoopPrespectrum.{u+1} :=
  HomotopyPushout.prespectrum (pullbackMap (projection A)) (pullbackMap (projection A))

/-- Descend the unchanged overlap, with positive time reversed and inverse time forward. -/
def comparison : span A ⟶ rawSpectrum (pairLaurentFunctor.obj A).obj :=
  HomotopyPushout.desc (pullbackMap (projection A)) (pullbackMap (projection A))
    (pullbackMap (plus A)) (pullbackMap (minus A))
    ((plusHomotopy A).symm.trans (minusHomotopy A))

/-- The positive polynomial source leg into the actual double cylinder. -/
def sourceLeg : rawSpectrum A.obj ⟶ span A :=
  pullbackMap (projection A) ≫ HomotopyPushout.inl _ _

/-- The actual source leg reaches the geometric positive composite. -/
theorem sourceLeg_comparison :
    sourceLeg A ≫ comparison A = pullbackMap (projection A) ≫ pullbackMap (plus A) := by
  simp only [sourceLeg, comparison, Category.assoc, HomotopyPushout.inl_desc]

/-- Keep the positive split track and literal cone contraction on their original halves. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRawStep.lean:49-57"
  "adaptation" "Keep the chosen positive split track and specified cone null in the two halves."]
def sourceNull :
    Homotopy (pullbackMap (laurentProjection A) ≫ mappingConeInclusion (comparison A))
      (zeroHom (rawSpectrum A.obj) (mappingCone (comparison A))) :=
  ((plusHomotopy A).postcomp (mappingConeInclusion (comparison A))).trans
    (((mappingConeHomotopy (comparison A)).precomp (sourceLeg A)).cast
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun f ↦ f ≫ mappingConeInclusion (comparison A))
          (sourceLeg_comparison A))) rfl)

/-- Every null time uses the original positive or cone half-clock on its whole region. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRawStep.lean:60-72"
  "adaptation" "The piecewise point-set null retains both original time coordinates."]
theorem sourceNull_apply (n : ℕ) (s : unitInterval) (x : (rawSpectrum A.obj).space n) :
    (sourceNull A).level n (s, x) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        (mappingConeInclusion (comparison A)).map n
          ((plusHomotopy A).level n
            (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x))
      else (mappingConeHomotopy (comparison A)).level n
        (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 hs).le, s.2.2⟩⟩, (sourceLeg A).map n x) := by
  change (ContinuousMap.HomotopyRel.trans _ _) (s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

/-- The forward Laurent track conjugated by this exact chosen source null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRawStep.lean:105-113"
  "adaptation" "Conjugate the original forward Laurent track by the same two-part null."]
def transition : rawSpectrum A.obj ⟶ parameterLooping (mappingCone (comparison A)) :=
  ((boundedAboveFlatPerfectSupportedLaurentProjectionUnitHomotopy A).postcomp
    (mappingConeInclusion (comparison A))).nullLoopMap (sourceNull A)

/-- All independent loop times retain the underlying forward Laurent track and both null legs. -/
theorem transition_apply (n : ℕ) (x : (rawSpectrum A.obj).space n) (s : unitInterval) :
    Path.toContinuousMap ((transition A).map n x) s =
      (((boundedAboveFlatPerfectSupportedLaurentProjectionUnitHomotopy A).postcomp
        (mappingConeInclusion (comparison A))).conjugateToZero (sourceNull A)).level n (s, x) := rfl

end AlgebraicGeometry.Scheme.Modules.SupportedRawBass
