/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.RowRefinementHomotopy
public import Colib.Topology.Prespectrum.RowRefinementFunctoriality
public import Colib.Topology.Prespectrum.RowInterchangeHomotopyPushout

/-!
# Actual row strength for the original reduced homotopy pushout

The two original inclusions and the entire original overlap give a map from the pushout of
row refinements to the refinement of the original pushout. Every row value keeps the same
quotient generator and overlap height. No stability or inverse is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.RowRefinement
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)
  (qA : ∀ k, C(A.space (k + 3), A.space (k + 3)))
  (qB : ∀ k, C(B.space (k + 3), B.space (k + 3)))
  (qC : ∀ k, C(C.space (k + 3), C.space (k + 3)))
  (hA : ∀ k, qA k (A.point (k + 3)) = A.point (k + 3))
  (hB : ∀ k, qB k (B.point (k + 3)) = B.point (k + 3))
  (hC : ∀ k, qC k (C.point (k + 3)) = C.point (k + 3))
  (hf : ∀ k x, qB k (f.map (k + 3) x) = f.map (k + 3) (qA k x))
  (hg : ∀ k x, qC k (g.map (k + 3) x) = g.map (k + 3) (qA k x))

/-- The whole original left inclusion acts pointwise on the distinguished row. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementPushout.lean:36-41"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def pushoutLeft : spectrum B qB hB ⟶ spectrum (HomotopyPushout.prespectrum f g)
    (RowInterchange.pushout f g qA qB qC hA hB hf hg)
    (RowInterchange.pushout_point f g qA qB qC hA hB hf hg) :=
  map qB _ hB _ (HomotopyPushout.inl f g) (fun _ _ => rfl)

/-- The whole original right inclusion acts pointwise on the distinguished row. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementPushout.lean:42-47"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def pushoutRight : spectrum C qC hC ⟶ spectrum (HomotopyPushout.prespectrum f g)
    (RowInterchange.pushout f g qA qB qC hA hB hf hg)
    (RowInterchange.pushout_point f g qA qB qC hA hB hf hg) :=
  map qC _ hC _ (HomotopyPushout.inr f g) (fun _ _ => rfl)

/-- The original overlap gives the whole row homotopy with unchanged overlap time. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementPushout.lean:48-57"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def pushoutGlue :
    Homotopy (map qA qB hA hB f hf ≫ pushoutLeft f g qA qB qC hA hB hf hg)
      (map qA qC hA hC g hg ≫ pushoutRight f g qA qB qC hA hB hC hf hg) :=
  (homotopy qA _ hA _
    (fun k x => congrArg (HomotopyPushout.left f g (k + 3)) (hf k x))
    (fun k x => congrArg (HomotopyPushout.right f g (k + 3)) (hg k x))
    (HomotopyPushout.glue f g) (fun _ _ _ => rfl)).cast
      (map_comp _ _ _ _ _ _ _ _ _ _ _) (map_comp _ _ _ _ _ _ _ _ _ _ _)

/-- Original quotient descent gives the forward whole row strength. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementPushout.lean:58-67"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
def pushoutStrength :
    HomotopyPushout.prespectrum (map qA qB hA hB f hf) (map qA qC hA hC g hg) ⟶
      spectrum (HomotopyPushout.prespectrum f g)
        (RowInterchange.pushout f g qA qB qC hA hB hf hg)
        (RowInterchange.pushout_point f g qA qB qC hA hB hf hg) :=
  HomotopyPushout.desc _ _ (pushoutLeft f g qA qB qC hA hB hf hg)
    (pushoutRight f g qA qB qC hA hB hC hf hg)
    (pushoutGlue f g qA qB qC hA hB hC hf hg)

/-- The actual left chart remains the original inclusion on every row value. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementPushout.lean:68-73"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem pushoutStrength_left :
    HomotopyPushout.inl (map qA qB hA hB f hf) (map qA qC hA hC g hg) ≫
      pushoutStrength f g qA qB qC hA hB hC hf hg =
        pushoutLeft f g qA qB qC hA hB hf hg := HomotopyPushout.inl_desc ..

/-- The actual right chart remains the original inclusion on every row value. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementPushout.lean:74-79"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem pushoutStrength_right :
    HomotopyPushout.inr (map qA qB hA hB f hf) (map qA qC hA hC g hg) ≫
      pushoutStrength f g qA qB qC hA hB hC hf hg =
        pushoutRight f g qA qB qC hA hB hC hf hg := HomotopyPushout.inr_desc ..

/-- At positive levels the entire overlap keeps its height and independent row coordinate. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementPushout.lean:80-86"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem pushoutStrength_overlap_succ (k : ℕ) (t s : unitInterval)
    (γ : Path (A.point (k + 2)) (A.point (k + 2))) :
    Path.toContinuousMap ((pushoutStrength f g qA qB qC hA hB hC hf hg).map (k + 1)
      (HomotopyPushout.cylinder (map qA qB hA hB f hf) (map qA qC hA hC g hg)
        (k + 1) (t, γ))) s = HomotopyPushout.cylinder f g (k + 2) (t, γ s) := rfl

/-- Degree zero retains both original loop coordinates and the independent overlap height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/RowRefinementPushout.lean:87-93"
  "adaptation" "Original quotient strength with independent row, loop and whole-track coordinates"]
theorem pushoutStrength_overlap_zero (t r s : unitInterval)
    (γ : Path (Path.refl (A.point 2)) (Path.refl (A.point 2))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((pushoutStrength f g qA qB qC hA hB hC hf hg).map 0
        (HomotopyPushout.cylinder (map qA qB hA hB f hf) (map qA qC hA hC g hg)
          0 (t, γ))) r) s = HomotopyPushout.cylinder f g 2 (t, γ r s) := rfl

end Topology.LoopPrespectrum.RowRefinement
