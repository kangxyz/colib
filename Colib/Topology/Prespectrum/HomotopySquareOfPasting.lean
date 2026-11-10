/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.HomotopySquare
public import Colib.Topology.Prespectrum.RelativeHomotopy
public import Colib.Topology.Prespectrum.HomotopyLoop
public import Colib.Topology.Homotopy.ThreeSideSquareLift

/-! # Literal square fillers from boundary-pasted relative homotopies

The relative comparison to `(L.trans H₁).trans M.symm` descends through an explicit compact-square
quotient. Its four boundary tracks and independent structure coordinate remain unchanged.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/HomotopySquareOfPasting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and independent parameters
are retained using native Colib and Mathlib objects. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.Homotopy
open Topology.ThreeSideSquare
variable {E F : LoopPrespectrum.{u}} {a₀ b₀ a₁ b₁ : E ⟶ F}
  (H₀ : Homotopy a₀ b₀) (H₁ : Homotopy a₁ b₁)
  (L : Homotopy a₀ a₁) (M : Homotopy b₀ b₁)

/-- The first quarter of the pasted boundary is the original left track. -/
lemma pasted_left (n : ℕ) (r : unitInterval) (x : E.space n) :
    ((L.trans H₁).trans M.symm).level n (leftTime r, x) = L.level n (r, x) := by
  change (((L.trans H₁).levelHomotopy n).trans (M.symm.levelHomotopy n)) (leftTime r, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change ((L.levelHomotopy n).trans (H₁.levelHomotopy n)) _ = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    split
    · apply congrArg (L.level n)
      apply Prod.ext
      · apply Subtype.ext
        dsimp [leftTime]
        ring
      · rfl
    · rename_i h
      dsimp [leftTime] at h
      linarith [r.2.2]
  · rename_i h
    dsimp [leftTime] at h
    linarith [r.2.2]

/-- The second quarter of the pasted boundary is the original upper track. -/
lemma pasted_top (n : ℕ) (s : unitInterval) (x : E.space n) :
    ((L.trans H₁).trans M.symm).level n (topTime s, x) = H₁.level n (s, x) := by
  change (((L.trans H₁).levelHomotopy n).trans (M.symm.levelHomotopy n)) (topTime s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change ((L.levelHomotopy n).trans (H₁.levelHomotopy n)) _ = _
    rw [ContinuousMap.HomotopyRel.trans_apply]
    split
    · rename_i h
      have hs : s = 0 := by
        apply Subtype.ext
        change (s : ℝ) = 0
        dsimp [topTime] at h
        linarith [s.2.1]
      subst s
      trans L.level n (1, x)
      · apply congrArg (L.level n)
        apply Prod.ext
        · apply Subtype.ext
          norm_num [topTime]
        · rfl
      · exact (L.at_one n x).trans (H₁.at_zero n x).symm
    · apply congrArg (H₁.level n)
      apply Prod.ext
      · apply Subtype.ext
        dsimp [topTime]
        ring
      · rfl
  · rename_i h
    dsimp [topTime] at h
    linarith [s.2.2]

/-- The last half of the pasted boundary is the original right track in reverse. -/
lemma pasted_right (n : ℕ) (r : unitInterval) (x : E.space n) :
    ((L.trans H₁).trans M.symm).level n (rightTime r, x) = M.level n (r, x) := by
  change (((L.trans H₁).levelHomotopy n).trans (M.symm.levelHomotopy n)) (rightTime r, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i h
    have hr : r = 1 := by
      apply Subtype.ext
      change (r : ℝ) = 1
      dsimp [rightTime] at h
      linarith [r.2.2]
    subst r
    trans (L.trans H₁).level n (1, x)
    · apply congrArg ((L.trans H₁).level n)
      apply Prod.ext
      · apply Subtype.ext
        norm_num [rightTime]
      · rfl
    · exact ((L.trans H₁).at_one n x).trans (M.at_one n x).symm
  · change M.level n (unitInterval.symm _, x) = _
    apply congrArg (M.level n)
    apply Prod.ext
    · apply Subtype.ext
      dsimp [rightTime, unitInterval.symm]
      ring
    · rfl

variable {H₀ H₁ L M}

/-- A proved relative comparison to the left-associated boundary pasting supplies the actual
moving-endpoint square, with no additional filler hypothesis. -/
def RelHomotopy.toSquare (J : H₀.RelHomotopy ((L.trans H₁).trans M.symm)) :
    H₀.Square H₁ L M := by
  let A (n : ℕ) : C((unitInterval × unitInterval) × E.space n, F.space n) :=
    ⟨fun z ↦ J.level n (z.1.1, (z.1.2, z.2)), by fun_prop⟩
  have h₀ (n : ℕ) (r : unitInterval) (x : E.space n) :
      A n ((r, 0), x) = A n ((0, 0), x) :=
    ((J.level n).eq_fst r (Or.inl rfl)).trans ((J.level n).apply_zero (0, x)).symm
  have h₁ (n : ℕ) (r : unitInterval) (x : E.space n) :
      A n ((r, 1), x) = A n ((0, 1), x) :=
    ((J.level n).eq_fst r (Or.inr (Or.inl rfl))).trans ((J.level n).apply_zero (1, x)).symm
  let B (n : ℕ) := liftFamily (A n) (h₀ n) (h₁ n)
  refine {
    level := fun n ↦ ⟨fun z ↦ B n ((z.1, z.2.1), z.2.2), by fun_prop⟩
    at_zero := ?_
    at_one := ?_
    left := ?_
    right := ?_
    at_point := ?_
    comm := ?_ }
  · intro n s x
    exact (liftFamily_zero (A n) (h₀ n) (h₁ n) s x).trans ((J.level n).apply_zero (s, x))
  · intro n s x
    exact (liftFamily_top (A n) (h₀ n) (h₁ n) s x).trans
      (((J.level n).apply_one (topTime s, x)).trans (pasted_top H₁ L M n s x))
  · intro n r x
    exact (liftFamily_left (A n) (h₀ n) (h₁ n) r x).trans
      (((J.level n).apply_one (leftTime r, x)).trans (pasted_left H₁ L M n r x))
  · intro n r x
    exact (liftFamily_right (A n) (h₀ n) (h₁ n) r x).trans
      (((J.level n).apply_one (rightTime r, x)).trans (pasted_right H₁ L M n r x))
  · intro n r s
    exact (J.at (Function.surjInv collapse_surjective (r, s)).1).at_point n
      (Function.surjInv collapse_surjective (r, s)).2
  · intro n r s x t
    exact J.comm n (Function.surjInv collapse_surjective (r, s)).1
      (Function.surjInv collapse_surjective (r, s)).2 x t

/-- Pulling the constructed square back along the actual parameter collapse recovers every point
of the original two-parameter comparison. -/
theorem RelHomotopy.toSquare_collapse
    (J : H₀.RelHomotopy ((L.trans H₁).trans M.symm))
    (n : ℕ) (z : unitInterval × unitInterval) (x : E.space n) :
    J.toSquare.level n ((collapse z).1, ((collapse z).2, x)) = J.level n (z.1, (z.2, x)) := by
  exact liftFamily_collapse
    (⟨fun z : (unitInterval × unitInterval) × E.space n ↦
      J.level n (z.1.1, (z.1.2, z.2)), by fun_prop⟩ :
        C((unitInterval × unitInterval) × E.space n, F.space n))
    (fun r x ↦ ((J.level n).eq_fst r (Or.inl rfl)).trans
      ((J.level n).apply_zero (0, x)).symm)
    (fun r x ↦ ((J.level n).eq_fst r (Or.inr (Or.inl rfl))).trans
      ((J.level n).apply_zero (1, x)).symm) z x

end Topology.LoopPrespectrum.Homotopy

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/HomotopySquareOfPasting.lean:116-166"
  "adaptation" "Actual three-side quotient lifting from a proved pasted boundary"]
  Topology.LoopPrespectrum.Homotopy.RelHomotopy.toSquare
