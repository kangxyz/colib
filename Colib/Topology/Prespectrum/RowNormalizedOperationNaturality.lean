/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.RowNormalizedOperation
public import Colib.Topology.Prespectrum.RowRefinementMap

/-!
# Whole naturality of row-normalized operations under actual row maps

An actual spectrum map with its specified interchange square preserves the entire original
inverse-prefix normalization. The strict comparison includes the explicit degree-zero loop
extension and keeps the unit, row, and source-structure coordinates separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowRefinement
variable {D E F : LoopPrespectrum.{u}}
  (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
  (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
  (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
  (a : E ⟶ F)
  (ha : ∀ k x, qF k (a.map (k + 3) x) = a.map (k + 3) (qE k x))
  (f : D ⟶ spectrum E qE hE) (H : Homotopy f f)

/-- Every positive normalized cell is natural under the actual underlying based map. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizedOperationNaturality.lean:36"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
theorem normalizedStage_postcomp (k : ℕ) (x : D.space (k + 1)) (t s : unitInterval) :
    a.map (k + 2) (normalizedStage qE hE f H k x t s) =
      normalizedStage qF hF (f ≫ map qE qF hE hF a ha)
        (H.postcomp (map qE qF hE hF a ha)) k x t s := by
  rw [normalizedStage_apply, normalizedStage_apply]
  exact loopNormalizedSelfTrack_pointwise (a.map (k + 2)) id _ _ _ _
    (fun _ => rfl) (fun _ _ => rfl) t s

/-- The original normalization commutes strictly with the whole actual row-refinement map. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/RowNormalizedOperationNaturality.lean:45"
  "adaptation" "Original whole-null refinement and normalized boundary comparison"]
theorem normalizedOperation_postcomp :
    normalizedOperation qE hE f H ≫ parameterLoopingMap (map qE qF hE hF a ha) =
      normalizedOperation qF hF (f ≫ map qE qF hE hF a ha)
        (H.postcomp (map qE qF hE hF a ha)) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero =>
    apply Path.ext
    funext t
    apply Path.ext
    funext r
    apply Path.ext
    funext s
    exact normalizedStage_postcomp qE qF hE hF a ha f H 0 (D.structureMap 0 x r) t s
  | succ k =>
    apply Path.ext
    funext t
    apply Path.ext
    funext s
    exact normalizedStage_postcomp qE qF hE hF a ha f H k x t s

end Topology.LoopPrespectrum.RowRefinement
