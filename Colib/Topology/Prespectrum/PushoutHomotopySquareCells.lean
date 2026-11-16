/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Topology.HomotopyLifting.PausedHomotopy
public import Colib.Topology.Prespectrum.PushoutHomotopySquare

/-!
# Whole parameter cells of pasted prespectrum homotopies

The native affine half clocks evaluate both original tracks of a pasted square
and all three cells of the original homotopy-pushout map. The last cell reverses
only the second square clock, not the structure parameter or the input point.

## Implementation provenance

Adapted from the cell lemmas in Quillen
`Quillen/Topology/Prespectrum/NativeHomotopyCells.lean`,
`Quillen/Topology/Prespectrum/NativeH1CellOps.lean`, and the original pasting in
`Quillen/Topology/Prespectrum/ConeSquareMapComposition.lean`, revision
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Topology.LoopPrespectrum

namespace Homotopy

variable {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}
  (H : Homotopy f g) (K : Homotopy g h)

/-- The first half evaluates the original first track at every time. -/
theorem trans_firstHalfTime (n : ℕ) (s : unitInterval) (x : E.space n) :
    (H.trans K).level n (firstHalfTime s, x) = H.level n (s, x) := by
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (firstHalfTime s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change H.level n (⟨2 * (firstHalfTime s : ℝ), _⟩, x) = H.level n (s, x)
    exact congrArg (fun t : unitInterval ↦ H.level n (t, x))
      (Subtype.ext (by dsimp [firstHalfTime]; ring))
  · rename_i hs
    exfalso
    apply hs
    change (s : ℝ) / 2 ≤ 1 / 2
    linarith [s.2.2]

/-- The second half evaluates the original second track, including at the seam. -/
theorem trans_secondHalfTime (n : ℕ) (s : unitInterval) (x : E.space n) :
    (H.trans K).level n (secondHalfTime s, x) = K.level n (s, x) := by
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (secondHalfTime s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change (1 + (s : ℝ)) / 2 ≤ 1 / 2 at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    change H.level n (⟨2 * (secondHalfTime 0 : ℝ), _⟩, x) = K.level n (0, x)
    calc
      _ = H.level n (1, x) := congrArg (fun t : unitInterval ↦ H.level n (t, x))
        (Subtype.ext (by norm_num [secondHalfTime]))
      _ = _ := (H.at_one n x).trans (K.at_zero n x).symm
  · change K.level n (⟨2 * (secondHalfTime s : ℝ) - 1, _⟩, x) = K.level n (s, x)
    exact congrArg (fun t : unitInterval ↦ K.level n (t, x))
      (Subtype.ext (by dsimp [secondHalfTime]; ring))

end Homotopy

section ConeSquare

variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a : E ⟶ E') (b : F ⟶ F') (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))

/-- The two original square tracks are pasted in their specified order. -/
def coneSquarePastedHomotopy : Homotopy (f ≫ (b ≫ d)) ((a ≫ c) ≫ h) :=
  ((H.postcomp d).trans ((Homotopy.precomp a K).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)).cast
      (Category.assoc _ _ _) rfl

/-- The first comparison half postcomposes the first square by the original second map. -/
theorem coneSquarePastedHomotopy_firstHalfTime (n : ℕ) (s : unitInterval) (x : E.space n) :
    (coneSquarePastedHomotopy f g h a b c d H K).level n (firstHalfTime s, x) =
      d.map n (H.level n (s, x)) :=
  Homotopy.trans_firstHalfTime (H.postcomp d)
    ((Homotopy.precomp a K).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
    n s x

/-- The second comparison half precomposes the second square by the original first map. -/
theorem coneSquarePastedHomotopy_secondHalfTime (n : ℕ) (s : unitInterval) (x : E.space n) :
    (coneSquarePastedHomotopy f g h a b c d H K).level n (secondHalfTime s, x) =
      K.level n (s, a.map n x) :=
  Homotopy.trans_secondHalfTime (H.postcomp d)
    ((Homotopy.precomp a K).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
    n s x

end ConeSquare

namespace HomotopyPushout

variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

/-- The first cylinder half is the original first leg square, without added pauses. -/
theorem mapOfHomotopies_firstHalfTime (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n (cylinder f g n (firstHalfTime t, x)) =
      (inl f' g').map n (Hf.level n (t, x)) :=
  mapOfHomotopies_first_half f g f' g' a b c Hf Hg n t x

/-- The middle quarter is the original whole target cylinder on the overlap image. -/
theorem mapOfHomotopies_middleQuarter (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (secondHalfTime (firstHalfTime t), x)) =
      cylinder f' g' n (t, a.map n x) := by
  (simp only [mapOfHomotopies_cylinder, mapSquareHomotopy, Homotopy.trans_secondHalfTime,
    Homotopy.trans_firstHalfTime]; rfl)

/-- The last quarter evaluates the original second leg square at the reversed clock. -/
theorem mapOfHomotopies_lastQuarter (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (secondHalfTime (secondHalfTime t), x)) =
      (inr f' g').map n (Hg.level n (unitInterval.symm t, x)) := by
  (simp only [mapOfHomotopies_cylinder, mapSquareHomotopy, Homotopy.trans_secondHalfTime]; rfl)

end HomotopyPushout

end Topology.LoopPrespectrum
