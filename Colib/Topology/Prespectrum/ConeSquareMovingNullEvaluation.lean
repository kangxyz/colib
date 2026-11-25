/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.ConeSquareMapMovingCoherence

/-! The exact two half-cells of the original initial moving-null square. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

/-- Original path pasting keeps the chart half followed by the full cone interchange half. -/
theorem coneSquareNullMovingSquare_apply
    {E F E' F' : LoopPrespectrum.{u}} (f : E ⟶ F) (g : E' ⟶ F')
    {a₀ a₁ : E ⟶ E'} {b₀ b₁ : F ⟶ F'}
    (H : Homotopy (f ≫ b₀) (a₀ ≫ g)) (K : Homotopy (f ≫ b₁) (a₁ ≫ g))
    (A : Homotopy a₀ a₁) (B : Homotopy b₀ b₁)
    (Q : H.Square K (Homotopy.precomp f B) (A.postcomp g))
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (coneSquareNullMovingSquare f g H K A B Q).level n (r, (s, x)) =
      if hs : (s : ℝ) ≤ 1 / 2 then
        (mappingConeInclusion g).map n
          (Q.level n (r, (⟨2 * s,
            (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, x)))
      else ReducedMappingCone.cylinder (E'.point n) (F'.point n) (g.map n)
        (⟨2 * s - 1,
          unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩,
          A.level n (r, x)) := by
  unfold coneSquareNullMovingSquare Homotopy.Square.pastePaths
  exact ContinuousMap.Homotopy.trans_apply _ _ _

end Topology.LoopPrespectrum
