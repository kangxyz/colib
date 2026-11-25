/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.Topology.Prespectrum.PushoutHomotopySquare
public import Colib.Topology.Prespectrum.ConeSquareMapComposition
public import Colib.Topology.Prespectrum.ConeSquareCompositionCells
public import Colib.Topology.Path.CarrierHalfPaths

/-! The three original cylinder cells of a homotopy-pushout map, with their literal clocks. -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Path.CarrierHalfPaths
open scoped Topology unitInterval
universe u

namespace Topology.LoopPrespectrum
namespace Homotopy

variable {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}
  (H : Homotopy f g) (K : Homotopy g h)

/-- The original lower half retains the first native track. -/
theorem trans_lower_cell (n : ℕ) (s : unitInterval) (x : E.space n) :
    (H.trans K).level n (lower s, x) = H.level n (s, x) := by
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (lower s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · change H.level n (⟨2 * (lower s : ℝ), _⟩, x) = H.level n (s, x)
    exact congrArg (fun t : unitInterval ↦ H.level n (t, x))
      (Subtype.ext (by dsimp [lower]; ring))
  · rename_i hs
    exfalso
    apply hs
    change (s : ℝ) / 2 ≤ 1 / 2
    linarith [s.2.2]

/-- The entire second half, including its shared initial point, retains the second native track. -/
theorem trans_upper_cell (n : ℕ) (s : unitInterval) (x : E.space n) :
    (H.trans K).level n (upper s, x) = K.level n (s, x) := by
  change ((H.levelHomotopy n).trans (K.levelHomotopy n)) (upper s, x) = _
  rw [ContinuousMap.HomotopyRel.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change ((s : ℝ) + 1) / 2 ≤ 1 / 2 at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    change H.level n (⟨2 * (upper 0 : ℝ), _⟩, x) = K.level n (0, x)
    calc
      _ = H.level n (1, x) := congrArg (fun t : unitInterval ↦ H.level n (t, x))
        (Subtype.ext (by norm_num [upper]))
      _ = _ := (H.at_one n x).trans (K.at_zero n x).symm
  · change K.level n (⟨2 * (upper s : ℝ) - 1, _⟩, x) = K.level n (s, x)
    exact congrArg (fun t : unitInterval ↦ K.level n (t, x))
      (Subtype.ext (by dsimp [upper]; ring))

end Homotopy

section ConePasting

variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a : E ⟶ E') (b : F ⟶ F') (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))

/-- The original first pasted half retains the first track followed by the output map. -/
theorem coneSquarePasted_lower_cell (n : ℕ) (s : unitInterval) (x : E.space n) :
    (coneSquarePastedHomotopy f g h a b c d H K).level n (lower s, x) =
      d.map n (H.level n (s, x)) :=
  Homotopy.trans_lower_cell (H.postcomp d)
    ((Homotopy.precomp a K).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
    n s x

/-- The original second pasted half retains the input map followed by the second track. -/
theorem coneSquarePasted_upper_cell (n : ℕ) (s : unitInterval) (x : E.space n) :
    (coneSquarePastedHomotopy f g h a b c d H K).level n (upper s, x) =
      K.level n (s, a.map n x) :=
  Homotopy.trans_upper_cell (H.postcomp d)
    ((Homotopy.precomp a K).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
    n s x

end ConePasting

namespace HomotopyPushout
variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

/-- The whole first cylinder cell is the supplied original first square. -/
theorem mapOfHomotopies_lower_cell (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n (cylinder f g n (lower t, x)) =
      (inl f' g').map n (Hf.level n (t, x)) :=
  Homotopy.trans_lower_cell ((Hf.postcomp (inl f' g')).cast
      (Category.assoc _ _ _) (Category.assoc _ _ _))
    ((Homotopy.precomp a (glue f' g')).trans
      ((Hg.symm.postcomp (inr f' g')).cast
        (Category.assoc _ _ _) (Category.assoc _ _ _))) n t x

/-- The final quarter is exactly the original reversed second square, in the other chart. -/
theorem mapOfHomotopies_upper_cell (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (upper (upper t), x)) =
      (inr f' g').map n (Hg.level n (unitInterval.symm t, x)) :=
  (Homotopy.trans_upper_cell ((Hf.postcomp (inl f' g')).cast
      (Category.assoc _ _ _) (Category.assoc _ _ _))
    ((Homotopy.precomp a (glue f' g')).trans
      ((Hg.symm.postcomp (inr f' g')).cast
        (Category.assoc _ _ _) (Category.assoc _ _ _))) n (upper t) x).trans
    (Homotopy.trans_upper_cell (Homotopy.precomp a (glue f' g'))
      ((Hg.symm.postcomp (inr f' g')).cast (Category.assoc _ _ _) (Category.assoc _ _ _)) n t x)

end HomotopyPushout
end Topology.LoopPrespectrum
