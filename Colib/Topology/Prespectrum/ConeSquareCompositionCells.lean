/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.Topology.Prespectrum.ConeSquareMapComposition
public import Colib.Topology.Prespectrum.HomotopyHalfCells
public import Colib.Topology.Prespectrum.PushoutHomotopySquare

/-!
# Exact level values of the pasted comparison and pushout overlap

The two halves are those of the actual cone-square pasting. The middle
quarter of the pushout map is the actual target cylinder along the given
overlap map. Adapted from `Quillen/Topology/Prespectrum/NativeH1CellOps.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory FundamentalGroupoid.OpenCover
open scoped Topology unitInterval

universe u

namespace Topology.LoopPrespectrum

variable {E F E' F' E'' F'' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (h : E'' ⟶ F'')
  (a : E ⟶ E') (b : F ⟶ F') (c : E' ⟶ E'') (d : F' ⟶ F'')
  (H : Homotopy (f ≫ b) (a ≫ g)) (K : Homotopy (g ≫ d) (c ≫ h))

/-- The first pasted half is the supplied first square homotopy followed by the target map. -/
theorem coneSquarePasted_leftHalf (n : ℕ) (s : unitInterval) (x : E.space n) :
    (coneSquarePastedHomotopy f g h a b c d H K).level n (leftHalf s, x) =
      d.map n (H.level n (s, x)) :=
  Homotopy.trans_leftHalf (H.postcomp d)
    ((Homotopy.precomp a K).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
    n s x

/-- The second pasted half is the supplied second square homotopy on the overlap image. -/
theorem coneSquarePasted_rightHalf (n : ℕ) (s : unitInterval) (x : E.space n) :
    (coneSquarePastedHomotopy f g h a b c d H K).level n (rightHalf s, x) =
      K.level n (s, a.map n x) :=
  Homotopy.trans_rightHalf (H.postcomp d)
    ((Homotopy.precomp a K).cast (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)
    n s x

namespace HomotopyPushout

variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

/-- The middle quarter is precisely the original target cylinder after the overlap map. -/
theorem mapOfHomotopies_middle_cell (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (rightHalf (leftHalf t), x)) = cylinder f' g' n (t, a.map n x) :=
  let L := (Hf.postcomp (inl f' g')).cast (Category.assoc _ _ _) (Category.assoc _ _ _)
  let M := Homotopy.precomp a (glue f' g')
  let R := (Hg.symm.postcomp (inr f' g')).cast (Category.assoc _ _ _) (Category.assoc _ _ _)
  (Homotopy.trans_rightHalf L (M.trans R) n (leftHalf t) x).trans
    (Homotopy.trans_leftHalf M R n t x)

/-- The original first half gives the left chart with the first square homotopy unchanged. -/
theorem mapOfHomotopies_leftHalf (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (leftHalf t, x)) = (inl f' g').map n (Hf.level n (t, x)) := by
  have ht : leftHalf t =
      ⟨(t : ℝ) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩ :=
    Subtype.ext (coe_leftHalf t)
  rw [ht]
  exact mapOfHomotopies_first_half f g f' g' a b c Hf Hg n t x

/-- The last quarter gives the right chart with the original reversed time. -/
theorem mapOfHomotopies_last_quarter (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (rightHalf (rightHalf t), x)) =
      (inr f' g').map n (Hg.level n (unitInterval.symm t, x)) :=
  let L := (Hf.postcomp (inl f' g')).cast (Category.assoc _ _ _) (Category.assoc _ _ _)
  let M := Homotopy.precomp a (glue f' g')
  let R := (Hg.symm.postcomp (inr f' g')).cast (Category.assoc _ _ _) (Category.assoc _ _ _)
  (Homotopy.trans_rightHalf L (M.trans R) n (rightHalf t) x).trans
    (Homotopy.trans_rightHalf M R n t x)

end HomotopyPushout
end Topology.LoopPrespectrum
