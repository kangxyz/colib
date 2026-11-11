/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Telescope
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.HomotopyLoop

/-!
# Telescope maps from original transition homotopies

Original stage maps that commute with the connecting maps through specified
whole prespectrum homotopies induce an actual map of the original reduced
telescopes. The construction retains each supplied homotopy as the second
part of its original cylinder track. It does not replace homotopy compatibility
by strict equality or assert higher functorial coherence.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
  (a : ∀ i, E i ⟶ E' i)
  (H : ∀ i, Homotopy (a i ≫ f' i) (f i ≫ a (i + 1)))

/-- The original target cylinder followed by the supplied transition homotopy. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMap.lean:36"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison."]
def mapCoconeHomotopy (i : ℕ) :
    Homotopy (a i ≫ inclusion E' f' i) (f i ≫ (a (i + 1) ≫ inclusion E' f' (i + 1))) :=
  (Homotopy.precomp (a i) (inclusionHomotopy E' f' i)).trans
    (((H i).postcomp (inclusion E' f' (i + 1))).cast
      (Category.assoc _ _ _) (Category.assoc _ _ _))

/-- Specified original transition homotopies induce a map of the original reduced telescopes. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMap.lean:43"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison."]
def mapOfHomotopies : prespectrum E f ⟶ prespectrum E' f' :=
  desc E f (fun i ↦ a i ≫ inclusion E' f' i) (mapCoconeHomotopy E f E' f' a H)

/-- The induced map agrees exactly with every original stage map after inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMap.lean:47"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison.", simp]
theorem inclusion_mapOfHomotopies (i : ℕ) :
    inclusion E f i ≫ mapOfHomotopies E f E' f' a H = a i ≫ inclusion E' f' i :=
  inclusion_desc E f _ _ i

/-- The entire source cylinder retains its original target-cylinder and supplied homotopy track. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMap.lean:52"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison.", simp]
theorem mapOfHomotopies_cylinder (k i : ℕ) (s : unitInterval) (x : (E i).space k) :
    (mapOfHomotopies E f E' f' a H).map k (cylinder E f k i (s, x)) =
      (mapCoconeHomotopy E f E' f' a H i).level k (s, x) := rfl

/-- The first half of the actual source cylinder is the original target cylinder. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMap.lean:57"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison."]
theorem mapOfHomotopies_first_half (k i : ℕ) (s : unitInterval)
    (hs : (s : ℝ) ≤ 1 / 2) (x : (E i).space k) :
    (mapOfHomotopies E f E' f' a H).map k (cylinder E f k i (s, x)) =
      cylinder E' f' k i
        (⟨2 * s, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, hs⟩⟩, (a i).map k x) := by
  rw [mapOfHomotopies_cylinder]
  exact (ContinuousMap.HomotopyRel.trans_apply
    ((Homotopy.precomp (a i) (inclusionHomotopy E' f' i)).levelHomotopy k)
    ((((H i).postcomp (inclusion E' f' (i + 1))).cast
      (Category.assoc _ _ _) (Category.assoc _ _ _)).levelHomotopy k) (s, x)).trans
      (dite_eq_left hs)

/-- The second half retains the whole supplied transition homotopy at the original next stage. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/TelescopeHomotopyMap.lean:70"
  "adaptation" "Original whole transition homotopies and actual stable telescope comparison."]
theorem mapOfHomotopies_second_half (k i : ℕ) (s : unitInterval)
    (hs : ¬(s : ℝ) ≤ 1 / 2) (x : (E i).space k) :
    (mapOfHomotopies E f E' f' a H).map k (cylinder E f k i (s, x)) =
      (inclusion E' f' (i + 1)).map k
        ((H i).level k
          (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) := by
  rw [mapOfHomotopies_cylinder]
  exact (ContinuousMap.HomotopyRel.trans_apply
    ((Homotopy.precomp (a i) (inclusionHomotopy E' f' i)).levelHomotopy k)
    ((((H i).postcomp (inclusion E' f' (i + 1))).cast
      (Category.assoc _ _ _) (Category.assoc _ _ _)).levelHomotopy k) (s, x)).trans
      (dite_eq_right hs)

end Topology.LoopPrespectrum.Telescope
