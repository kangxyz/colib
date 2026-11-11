/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RowRefinementMap

/-! Identity and composition for the actual row-refinement maps, including degree zero. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.RowRefinement
variable {E F G : LoopPrespectrum.{u}}

/-- The identity spectrum map acts identically on every actual distinguished row. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementFunctoriality.lean:19-31"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem map_id (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
    (h : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))
    (hi : ∀ k x, q k ((𝟙 E : E ⟶ E).map (k + 3) x) = (𝟙 E : E ⟶ E).map (k + 3) (q k x)) :
    map q q h h (𝟙 E) hi = 𝟙 (spectrum E q h) := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero => apply Path.ext; funext r; apply Path.ext; funext s; rfl
  | succ k => apply Path.ext; funext r; rfl

/-- Whole-map composition preserves both loop coordinates at the explicit zero level. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementFunctoriality.lean:32-51"
  "adaptation" "Original row refinement, including degree zero and independent whole-track time"]
theorem map_comp
    (qE : ∀ k, C(E.space (k + 3), E.space (k + 3)))
    (qF : ∀ k, C(F.space (k + 3), F.space (k + 3)))
    (qG : ∀ k, C(G.space (k + 3), G.space (k + 3)))
    (hE : ∀ k, qE k (E.point (k + 3)) = E.point (k + 3))
    (hF : ∀ k, qF k (F.point (k + 3)) = F.point (k + 3))
    (hG : ∀ k, qG k (G.point (k + 3)) = G.point (k + 3))
    (a : E ⟶ F) (b : F ⟶ G)
    (ha : ∀ k x, qF k (a.map (k + 3) x) = a.map (k + 3) (qE k x))
    (hb : ∀ k x, qG k (b.map (k + 3) x) = b.map (k + 3) (qF k x))
    (hab : ∀ k x, qG k ((a ≫ b).map (k + 3) x) = (a ≫ b).map (k + 3) (qE k x)) :
    map qE qG hE hG (a ≫ b) hab = map qE qF hE hF a ha ≫ map qF qG hF hG b hb := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  cases n with
  | zero => apply Path.ext; funext r; apply Path.ext; funext s; rfl
  | succ k => apply Path.ext; funext r; rfl

end Topology.LoopPrespectrum.RowRefinement
