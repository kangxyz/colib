/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.KTheory.Waldhausen.Iterated.ScalarRectangleLiftOps

/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/ScalarRouteExtraction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
/-! Recover each original constituent track from the complete two-half route lifts. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.SimplexParameters
variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
  (S : ModelSimplex V W k)
variable {a b c : StdSimplex ℝ (Fin (k + 1))}
variable {f g h : prespectrum V ⟶ prespectrum W}
variable {p : Path a b} {q : Path b c}
variable {H : Homotopy f g} {K : Homotopy g h}

/-- A lift of the literal concatenation determines its first half at every original time. -/
theorem PathLift.trans_left (h : PathLift S (p.trans q) (H.trans K)) :
    PathLift S p H := by
  intro n t x
  let z : unitInterval := ⟨(t : ℝ) / 2, by
    constructor <;> nlinarith [t.property.1, t.property.2]⟩
  have hz : (z : ℝ) ≤ 1 / 2 := by
    dsimp [z]
    nlinarith [t.property.2]
  have htz : (⟨2 * (z : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
      ⟨z.property.1, hz⟩⟩ : unitInterval) = t := by
    apply Subtype.ext
    dsimp [z]
    ring
  have hp : (p.trans q) z = p t := by
    rw [Path.trans_apply]
    simp only [dite_eq_left hz, htz]
  have hH : (H.trans K).level n (z, x) = H.level n (t, x) := by
    change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (z, x) = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    simp only [dite_eq_left hz, htz]
    rfl
  calc
    prespectrumSimplexFamily S n (p t, x) =
        prespectrumSimplexFamily S n ((p.trans q) z, x) := by rw [hp]
    _ = (H.trans K).level n (z, x) := h n z x
    _ = H.level n (t, x) := hH

/-- A lift of the literal concatenation determines its second half, including the midpoint. -/
theorem PathLift.trans_right (h : PathLift S (p.trans q) (H.trans K)) :
    PathLift S q K := by
  intro n t x
  let z : unitInterval := ⟨((t : ℝ) + 1) / 2, by
    constructor <;> nlinarith [t.property.1, t.property.2]⟩
  by_cases ht : t = 0
  · subst t
    have hz : (z : ℝ) ≤ 1 / 2 := by
      dsimp [z]
      norm_num
    have htz : (⟨2 * (z : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
        ⟨z.property.1, hz⟩⟩ : unitInterval) = 1 := by
      apply Subtype.ext
      dsimp [z]
      norm_num
    have hp : (p.trans q) z = q 0 := by
      rw [Path.trans_apply]
      simp only [dite_eq_left hz, htz]
      exact p.target.trans q.source.symm
    have hK : (H.trans K).level n (z, x) = K.level n (0, x) := by
      change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (z, x) = _
      rw [ContinuousMap.HomotopyRel.trans_apply]
      simp only [dite_eq_left hz, htz]
      exact (H.at_one n x).trans (K.at_zero n x).symm
    calc
      prespectrumSimplexFamily S n (q 0, x) =
          prespectrumSimplexFamily S n ((p.trans q) z, x) := by rw [hp]
      _ = (H.trans K).level n (z, x) := h n z x
      _ = K.level n (0, x) := hK
  · have hpos : 0 < (t : ℝ) := by
      have ht0 : (t : ℝ) ≠ 0 := by
        intro he
        exact ht (Subtype.ext he)
      exact lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0)
    have hz : ¬ (z : ℝ) ≤ 1 / 2 := by
      dsimp [z]
      linarith
    have htz : (⟨2 * (z : ℝ) - 1,
        unitInterval.two_mul_sub_one_mem_iff.2
          ⟨(not_le.1 hz).le, z.property.2⟩⟩ : unitInterval) = t := by
      apply Subtype.ext
      dsimp [z]
      ring
    have hp : (p.trans q) z = q t := by
      rw [Path.trans_apply]
      simp only [dite_eq_right hz, htz]
    have hK : (H.trans K).level n (z, x) = K.level n (t, x) := by
      change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (z, x) = _
      rw [ContinuousMap.HomotopyRel.trans_apply]
      simp only [dite_eq_right hz, htz]
      rfl
    calc
      prespectrumSimplexFamily S n (q t, x) =
          prespectrumSimplexFamily S n ((p.trans q) z, x) := by rw [hp]
      _ = (H.trans K).level n (z, x) := h n z x
      _ = K.level n (t, x) := hK
end CategoryTheory.Waldhausen.IteratedS.SimplexParameters
