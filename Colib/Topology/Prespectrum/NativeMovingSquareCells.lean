/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.Topology.HomotopyLifting.PausedHomotopy
public import Colib.Topology.Prespectrum.PushoutIdentityFromUnitSquare

/-! # Cells of the identical-leg moving square

Pasting along the path coordinate preserves both halves, including the common endpoint.
The identical-leg square restricts to the left inclusion, the moving cylinder, and the
right inclusion with the path coordinate reversed.
-/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/NativeMovingSquareCells.lean` and the two homotopy restriction
lemmas in `Quillen/Topology/Path/ScalarRectangleConcatenation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u

namespace Topology

section
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g h : C(Y, X)}
  (F : ContinuousMap.Homotopy f g) (G : ContinuousMap.Homotopy g h)

private theorem trans_firstHalfTime (s : unitInterval) (x : Y) :
    (F.trans G) (firstHalfTime s, x) = F (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · change F (⟨2 * (firstHalfTime s : ℝ), _⟩, x) = F (s, x)
    exact congrArg (fun t : unitInterval ↦ F (t, x))
      (Subtype.ext (by dsimp [firstHalfTime]; ring))
  · rename_i hs
    exfalso
    apply hs
    exact firstHalfTime_le_half s

private theorem trans_secondHalfTime (s : unitInterval) (x : Y) :
    (F.trans G) (secondHalfTime s, x) = G (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change (1 + (s : ℝ)) / 2 ≤ 1 / 2 at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    change F (⟨2 * (secondHalfTime 0 : ℝ), _⟩, x) = G (0, x)
    calc
      _ = F (1, x) := congrArg (fun t : unitInterval ↦ F (t, x))
        (Subtype.ext (by norm_num [secondHalfTime]))
      _ = _ := (F.map_one_left x).trans (G.map_zero_left x).symm
  · change G (⟨2 * (secondHalfTime s : ℝ) - 1, _⟩, x) = G (s, x)
    exact congrArg (fun t : unitInterval ↦ G (t, x))
      (Subtype.ext (by dsimp [secondHalfTime]; ring))
end

end Topology

namespace Topology.LoopPrespectrum.Homotopy.Square
variable {E F : LoopPrespectrum.{u}} {f₀ g₀ h₀ f₁ g₁ h₁ : E ⟶ F}
  {H₀ : Homotopy f₀ g₀} {H₁ : Homotopy f₁ g₁}
  {K₀ : Homotopy g₀ h₀} {K₁ : Homotopy g₁ h₁}
  {L : Homotopy f₀ f₁} {M : Homotopy g₀ g₁} {N : Homotopy h₀ h₁}
  (S : H₀.Square H₁ L M) (T : K₀.Square K₁ M N)

/-- The original whole first half of a pasted square retains the exact first square. -/
theorem nativePastePaths_lower (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (S.pastePaths T).level n (r, (firstHalfTime s, x)) = S.level n (r, (s, x)) := by
  change ContinuousMap.Homotopy.trans _ _ (firstHalfTime s, (r, x)) = _
  exact trans_firstHalfTime _ _ s (r, x)

/-- The whole other half includes the shared point and retains the second native square. -/
theorem nativePastePaths_upper (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (S.pastePaths T).level n (r, (secondHalfTime s, x)) = T.level n (r, (s, x)) := by
  change ContinuousMap.Homotopy.trans _ _ (secondHalfTime s, (r, x)) = _
  exact trans_secondHalfTime _ _ s (r, x)
end Topology.LoopPrespectrum.Homotopy.Square

namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B A' B' : LoopPrespectrum.{u}} (f : A ⟶ B) (f' : A' ⟶ B')
  {a₀ a₁ : A ⟶ A'} {b₀ b₁ : B ⟶ B'}
  (H₀ : Homotopy (f ≫ b₀) (a₀ ≫ f')) (H₁ : Homotopy (f ≫ b₁) (a₁ ≫ f'))
  (L : Homotopy a₀ a₁) (M : Homotopy b₀ b₁)
  (S : H₀.Square H₁ (Homotopy.precomp f M) (L.postcomp f'))

/-- The first half is exactly the original polynomial square on the native left chart. -/
theorem identicalMoving_lower (n : ℕ) (r t : unitInterval) (x : A.space n) :
    (identicalLegMovingSquare f f' H₀ H₁ L M S).level n (r, (firstHalfTime t, x)) =
      (inl f' f').map n (S.level n (r, (t, x))) := by
  unfold identicalLegMovingSquare
  rw [Homotopy.Square.nativePastePaths_lower]
  rfl

/-- The middle quarter retains both independent times in the original moving cylinder. -/
theorem identicalMoving_middle (n : ℕ) (r t : unitInterval) (x : A.space n) :
    (identicalLegMovingSquare f f' H₀ H₁ L M S).level n (r, (secondHalfTime (firstHalfTime t), x)) =
      cylinder f' f' n (t, L.level n (r, x)) := by
  unfold identicalLegMovingSquare
  rw [Homotopy.Square.nativePastePaths_upper, Homotopy.Square.nativePastePaths_lower]
  rfl

/-- The final quarter keeps the original reversed polynomial path on the distinct right chart. -/
theorem identicalMoving_upper (n : ℕ) (r t : unitInterval) (x : A.space n) :
    (identicalLegMovingSquare f f' H₀ H₁ L M S).level n
      (r, (secondHalfTime (secondHalfTime t), x)) =
      (inr f' f').map n (S.level n (r, (unitInterval.symm t, x))) := by
  unfold identicalLegMovingSquare
  rw [Homotopy.Square.nativePastePaths_upper, Homotopy.Square.nativePastePaths_upper]
  rfl

end Topology.LoopPrespectrum.HomotopyPushout
