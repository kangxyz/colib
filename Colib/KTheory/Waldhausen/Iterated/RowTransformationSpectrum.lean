/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Iterated.RowTransformationRealization
public import Colib.KTheory.Waldhausen.Iterated.RowLoopHomotopy

/-! # The whole spectrum cell of an independently realized first row

Positive levels retain the row and transformation times. Degree zero retains the additional
original input-loop coordinate. This does not assert a standard tensor-product qualification.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory SSet Topology
variable {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))

/-- The original track with its actual first-row-compatible target. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationSpectrum.lean:28"
  "adaptation" "Original ordered row and transformation cylinders on native Waldhausen objects."]
def rowTransformationSpectrumHomotopy :
    LoopPrespectrum.Homotopy (prespectrumMap F ≫ rowStabilizationMap W)
      (prespectrumMap G ≫ rowStabilizationMap W) :=
  (prespectrumTransformationHomotopy η hη).postcomp (rowStabilizationMap W)

/-- Positive levels agree with the independent double-cylinder realization. -/
@[colib_tag "COL-0530", colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationSpectrum.lean:34"
  "adaptation" "Original ordered row and transformation cylinders on native Waldhausen objects."]
theorem rowTransformationSpectrumHomotopy_succ (k : ℕ) (t s : unitInterval)
    (x : stageSpace k V) :
    Path.toContinuousMap ((rowTransformationSpectrumHomotopy η hη).level (k + 1) (t, x)) s =
      rowTransformationRealization η hη k (s, (t, x)) :=
  (rowTransformationRealization_structure η hη k s t x).symm

/-- Degree zero retains the source loop separately from both cell coordinates. -/
@[colib_tag "COL-0530", colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/RowTransformationSpectrum.lean:41"
  "adaptation" "Original ordered row and transformation cylinders on native Waldhausen objects."]
theorem rowTransformationSpectrumHomotopy_zero (t a s : unitInterval)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    Path.toContinuousMap
      (Path.toContinuousMap ((rowTransformationSpectrumHomotopy η hη).level 0 (t, γ)) a) s =
      rowTransformationRealization η hη 0 (s, (t, γ a)) :=
  (rowTransformationRealization_structure η hη 0 s t (γ a)).symm

end CategoryTheory.Waldhausen.IteratedS
