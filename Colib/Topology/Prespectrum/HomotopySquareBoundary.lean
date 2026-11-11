/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.HomotopySquareOfPasting

/-! A genuine moving square gives its actual three-sided endpoint-relative boundary comparison. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/HomotopySquareBoundary.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and independent parameters
are retained using native Colib and Mathlib objects. -/
@[expose] public section
noncomputable section
open CategoryTheory Topology.ThreeSideSquare
universe u
namespace Topology.LoopPrespectrum.Homotopy.Square

private theorem boundary_time_cases (s : unitInterval) :
    (∃ r, s = leftTime r) ∨ (∃ r, s = topTime r) ∨ (∃ r, s = rightTime r) := by
  by_cases h : (s : ℝ) ≤ 1 / 4
  · left
    refine ⟨⟨4 * s, by constructor <;> linarith [s.2.1]⟩, ?_⟩
    apply Subtype.ext
    dsimp [leftTime]
    ring
  · by_cases h' : (s : ℝ) ≤ 1 / 2
    · right; left
      refine ⟨⟨4 * s - 1, by constructor <;> linarith⟩, ?_⟩
      apply Subtype.ext
      dsimp [topTime]
      ring
    · right; right
      refine ⟨⟨2 - 2 * s, by constructor <;> linarith [s.2.2]⟩, ?_⟩
      apply Subtype.ext
      dsimp [rightTime]
      ring

variable {E F : LoopPrespectrum.{u}} {a₀ b₀ a₁ b₁ : E ⟶ F}
  {H₀ : Homotopy a₀ b₀} {H₁ : Homotopy a₁ b₁}
  {L : Homotopy a₀ a₁} {M : Homotopy b₀ b₁}

/-- The original square evaluated along its collapsed upper edge is the literal pasted boundary. -/
lemma collapse_top (S : H₀.Square H₁ L M) (n : ℕ) (s : unitInterval) (x : E.space n) :
    S.level n ((collapse (1, s)).1, ((collapse (1, s)).2, x)) =
      ((L.trans H₁).trans M.symm).level n (s, x) := by
  rcases boundary_time_cases s with ⟨r, rfl⟩ | ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [collapse_leftTime]
    exact (S.left n r x).trans (Homotopy.pasted_left H₁ L M n r x).symm
  · rw [collapse_topTime]
    exact (S.at_one n r x).trans (Homotopy.pasted_top H₁ L M n r x).symm
  · rw [collapse_rightTime]
    exact (S.right n r x).trans (Homotopy.pasted_right H₁ L M n r x).symm

/-- Retain every point of the actual square to produce its three-sided relative boundary. -/
def toBoundary (S : H₀.Square H₁ L M) :
    H₀.RelHomotopy ((L.trans H₁).trans M.symm) where
  level n := {
    toFun := fun z ↦ S.level n ((collapse (z.1, z.2.1)).1,
      ((collapse (z.1, z.2.1)).2, z.2.2))
    continuous_toFun := by
      have hc : Continuous (fun z : unitInterval × (unitInterval × E.space n) ↦
          collapse (z.1, z.2.1)) :=
        continuous_collapse.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
      exact (S.level n).continuous.comp
        (hc.fst.prodMk (hc.snd.prodMk (continuous_snd.comp continuous_snd)))
    map_zero_left := by
      rintro ⟨s, x⟩
      simp only [collapse_zero]
      exact S.at_zero n s x
    map_one_left := by
      rintro ⟨s, x⟩
      exact collapse_top S n s x
    prop' := by
      intro r z hz
      rcases z with ⟨s, x⟩
      change s = 0 ∨ s = 1 ∨ x = E.point n at hz
      change S.level n ((collapse (r, s)).1, ((collapse (r, s)).2, x)) = H₀.level n (s, x)
      rcases hz with hs | hs | hx
      · subst s
        simp only [collapse_left]
        exact S.at_zero n 0 x
      · subst s
        simp only [collapse_right]
        exact S.at_zero n 1 x
      · subst x
        exact (S.at_point n _ _).trans (H₀.at_point n s).symm }
  comm n r s x t := S.comm n _ _ x t

/-- The boundary comparison retains the whole original moving square under the fixed collapse. -/
lemma toBoundary_apply (S : H₀.Square H₁ L M) (n : ℕ) (r s : unitInterval) (x : E.space n) :
    S.toBoundary.level n (r, (s, x)) =
      S.level n ((collapse (r, s)).1, ((collapse (r, s)).2, x)) := rfl

end Topology.LoopPrespectrum.Homotopy.Square

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/HomotopySquareBoundary.lean:54-91"
  "adaptation" "The original moving square gives its endpoint-relative three-side boundary"]
  Topology.LoopPrespectrum.Homotopy.Square.toBoundary
