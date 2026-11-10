/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.HomotopyPushout

/-!
# Row interchange through finite homotopy pushouts

Three actual based level interchanges and the two original arrow squares act on the original
reduced double mapping cylinder. The overlap height is never changed. The two-structure
identity descends cellwise, and a comparison into a fourth spectrum is equivariant precisely
using its prescribed whole overlap track. No Model or Omega-spectrum hypothesis is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowInterchange
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  (qA : ∀ k, C(A.space (k + 3), A.space (k + 3)))
  (qB : ∀ k, C(B.space (k + 3), B.space (k + 3)))
  (qC : ∀ k, C(C.space (k + 3), C.space (k + 3)))
  (hA : ∀ k, qA k (A.point (k + 3)) = A.point (k + 3))
  (hB : ∀ k, qB k (B.point (k + 3)) = B.point (k + 3))
  (hf : ∀ k x, qB k (f.map (k + 3) x) = f.map (k + 3) (qA k x))
  (hg : ∀ k x, qC k (g.map (k + 3) x) = g.map (k + 3) (qA k x))

/-- The actual three interchanges descend on the original reduced double mapping cylinder. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeHomotopyPushout.lean:34-62"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
def pushout (k : ℕ) :
    C((HomotopyPushout.prespectrum f g).space (k + 3),
      (HomotopyPushout.prespectrum f g).space (k + 3)) where
  toFun := Quot.lift
    (Sum.elim (Sum.elim
      (fun y => HomotopyPushout.left f g (k + 3) (qB k y))
      (fun z => HomotopyPushout.right f g (k + 3) (qC k z)))
      (fun z => HomotopyPushout.cylinder f g (k + 3) (z.1, qA k z.2))) (by
    intro x y h
    cases h with
    | left x =>
      dsimp only [Sum.elim]
      rw [HomotopyPushout.cylinder_zero]
      exact congrArg (HomotopyPushout.left f g (k + 3)) (hf k x).symm
    | right x =>
      dsimp only [Sum.elim]
      rw [HomotopyPushout.cylinder_one]
      exact congrArg (HomotopyPushout.right f g (k + 3)) (hg k x).symm
    | base s =>
      change HomotopyPushout.cylinder f g (k + 3) (s, qA k (A.point (k + 3))) =
        HomotopyPushout.left f g (k + 3) (qB k (B.point (k + 3)))
      rw [hA, hB]
      exact HomotopyPushout.cylinder_point f g (k + 3) s)
  continuous_toFun := continuous_quot_lift _
    (((HomotopyPushout.left f g (k + 3)).continuous.comp (qB k).continuous).sumElim
      ((HomotopyPushout.right f g (k + 3)).continuous.comp (qC k).continuous) |>.sumElim
        (by fun_prop))

/-- The original left cell retains its own prescribed row action. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeHomotopyPushout.lean:63-67"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem pushout_left (k : ℕ) (y : B.space (k + 3)) :
    pushout f g qA qB qC hA hB hf hg k (HomotopyPushout.left f g (k + 3) y) =
      HomotopyPushout.left f g (k + 3) (qB k y) := rfl

/-- The original right cell retains its own prescribed row action. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeHomotopyPushout.lean:68-72"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem pushout_right (k : ℕ) (y : C.space (k + 3)) :
    pushout f g qA qB qC hA hB hf hg k (HomotopyPushout.right f g (k + 3) y) =
      HomotopyPushout.right f g (k + 3) (qC k y) := rfl

/-- The whole overlap keeps the original overlap coordinate. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeHomotopyPushout.lean:73-77"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem pushout_cylinder (k : ℕ) (t : unitInterval) (x : A.space (k + 3)) :
    pushout f g qA qB qC hA hB hf hg k (HomotopyPushout.cylinder f g (k + 3) (t, x)) =
      HomotopyPushout.cylinder f g (k + 3) (t, qA k x) := rfl

/-- The original reduced pushout point is fixed. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeHomotopyPushout.lean:78-83"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem pushout_point (k : ℕ) :
    pushout f g qA qB qC hA hB hf hg k ((HomotopyPushout.prespectrum f g).point (k + 3)) =
      (HomotopyPushout.prespectrum f g).point (k + 3) :=
  congrArg (HomotopyPushout.left f g (k + 3)) (hB k)

/-- Three actual involutions descend to an involution, with no new quotient choices. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeHomotopyPushout.lean:84-96"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem pushout_involutive (k : ℕ) (hiA : Function.Involutive (qA k))
    (hiB : Function.Involutive (qB k)) (hiC : Function.Involutive (qC k)) :
    Function.Involutive (pushout f g qA qB qC hA hB hf hg k) := by
  intro x
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl y => exact congrArg (HomotopyPushout.left f g (k + 3)) (hiB y)
      | inr y => exact congrArg (HomotopyPushout.right f g (k + 3)) (hiC y)
    | inr z =>
      exact congrArg (fun y => HomotopyPushout.cylinder f g (k + 3) (z.1, y)) (hiA z.2)

/-- The two original structure times interchange on all three original cells. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeHomotopyPushout.lean:97-126"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem pushout_structure
    (hsA : ∀ k (x : A.space (k + 1)) (s t : unitInterval),
      qA k (A.structureMap (k + 2) (A.structureMap (k + 1) x s) t) =
        A.structureMap (k + 2) (A.structureMap (k + 1) x t) s)
    (hsB : ∀ k (x : B.space (k + 1)) (s t : unitInterval),
      qB k (B.structureMap (k + 2) (B.structureMap (k + 1) x s) t) =
        B.structureMap (k + 2) (B.structureMap (k + 1) x t) s)
    (hsC : ∀ k (x : C.space (k + 1)) (s t : unitInterval),
      qC k (C.structureMap (k + 2) (C.structureMap (k + 1) x s) t) =
        C.structureMap (k + 2) (C.structureMap (k + 1) x t) s)
    (k : ℕ) (x : (HomotopyPushout.prespectrum f g).space (k + 1)) (s t : unitInterval) :
    pushout f g qA qB qC hA hB hf hg k
      ((HomotopyPushout.prespectrum f g).structureMap (k + 2)
        ((HomotopyPushout.prespectrum f g).structureMap (k + 1) x s) t) =
      (HomotopyPushout.prespectrum f g).structureMap (k + 2)
        ((HomotopyPushout.prespectrum f g).structureMap (k + 1) x t) s := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl y => exact congrArg (HomotopyPushout.left f g (k + 3)) (hsB k y s t)
      | inr y => exact congrArg (HomotopyPushout.right f g (k + 3)) (hsC k y s t)
    | inr z =>
      exact congrArg (fun y => HomotopyPushout.cylinder f g (k + 3) (z.1, y)) (hsA k z.2 s t)

variable {D : LoopPrespectrum.{u}} (b : B ⟶ D) (c : C ⟶ D)
  (H : Homotopy (f ≫ b) (g ≫ c))
  (qD : ∀ k, C(D.space (k + 3), D.space (k + 3)))

/-- The actual comparison uses its full specified overlap square as well as its two vertex squares.
-/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowInterchangeHomotopyPushout.lean:127-142"
  "adaptation" "Original quotient maps and independent Bass-stage and spectrum-level indices"]
theorem pushout_desc
    (hb : ∀ k x, qD k (b.map (k + 3) x) = b.map (k + 3) (qB k x))
    (hc : ∀ k x, qD k (c.map (k + 3) x) = c.map (k + 3) (qC k x))
    (hH : ∀ k t x, qD k (H.level (k + 3) (t, x)) = H.level (k + 3) (t, qA k x))
    (k : ℕ) (x : (HomotopyPushout.prespectrum f g).space (k + 3)) :
    qD k ((HomotopyPushout.desc f g b c H).map (k + 3) x) =
      (HomotopyPushout.desc f g b c H).map (k + 3)
        (pushout f g qA qB qC hA hB hf hg k x) := by
  induction x using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl y => exact hb k y
      | inr y => exact hc k y
    | inr z => exact hH k z.1 z.2

end Topology.LoopPrespectrum.RowInterchange
