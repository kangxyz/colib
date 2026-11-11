/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentialization

/-!
# Original strict-map naturality of canonical zigzag sequentialization

Strict maps on both original vertex families give recursive maps on the actual finite
homotopy pushouts. The original comparison arrows and transitions commute strictly.
Whole factorization tracks which are natural at every time give the same timewise
naturality for the constructed comparison tracks. These facts retain the data needed
for naturality of nullhomotopies, without constructing a general homotopy-colimit category.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped unitInterval
universe u
namespace Topology.LoopPrespectrum.ZigzagSequentialization
variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)
    (E' V' : ℕ → LoopPrespectrum.{u})
    (a' : ∀ n, E' n ⟶ V' n) (b' : ∀ n, E' (n + 1) ⟶ V' n)
    (d : ∀ n, E n ⟶ E' n) (v : ∀ n, V n ⟶ V' n)
    (ha : ∀ n, a n ≫ v n = d n ≫ a' n)
    (hb : ∀ n, b n ≫ v n = d (n + 1) ≫ b' n)

/-- Each original positive-stage map carries its strict comparison-square witness. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationNaturality.lean:36"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
def stageMapWithComparison : (n : ℕ) →
    {m : stage E V a b (n + 1) ⟶ stage E' V' a' b' (n + 1) //
      comparison E V a b (n + 1) ≫ m = d (n + 1) ≫ comparison E' V' a' b' (n + 1)}
  | 0 => ⟨v 0, hb 0⟩
  | n + 1 =>
    let previous := stageMapWithComparison n
    ⟨HomotopyPushout.map (comparison E V a b (n + 1)) (a (n + 1))
      (comparison E' V' a' b' (n + 1)) (a' (n + 1))
      (d (n + 1)) previous.1 (v (n + 1)) previous.2 (ha (n + 1)), by
      change (b (n + 1) ≫ HomotopyPushout.inr _ _) ≫ _ =
        d (n + 1 + 1) ≫ (b' (n + 1) ≫ HomotopyPushout.inr _ _)
      apply Hom.ext
      funext k
      ext x
      exact congrArg (HomotopyPushout.right
        (comparison E' V' a' b' (n + 1)) (a' (n + 1)) k)
          (congrArg (fun m ↦ m.map k x) (hb (n + 1)))⟩

/-- The original vertex maps induce maps on the actual canonical sequential stages. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationNaturality.lean:55"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
def stageMap : (n : ℕ) → stage E V a b n ⟶ stage E' V' a' b' n
  | 0 => d 0
  | n + 1 => (stageMapWithComparison E V a b E' V' a' b' d v ha hb n).1

/-- The original comparison arrows commute strictly with recursive pushout maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationNaturality.lean:60"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
theorem comparison_naturality (n : ℕ) :
    comparison E V a b n ≫ stageMap E V a b E' V' a' b' d v ha hb n =
      d n ≫ comparison E' V' a' b' n := by
  cases n with
  | zero => simp [comparison, stageMap]
  | succ n => exact (stageMapWithComparison E V a b E' V' a' b' d v ha hb n).2

/-- Every original canonical transition commutes strictly with those same maps. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationNaturality.lean:68"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
theorem transition_naturality (n : ℕ) :
    transition E V a b n ≫ stageMap E V a b E' V' a' b' d v ha hb (n + 1) =
      stageMap E V a b E' V' a' b' d v ha hb n ≫ transition E' V' a' b' n := by
  cases n with
  | zero => exact ha 0
  | succ n =>
    exact HomotopyPushout.inl_map _ _ _ _ _ _ _
      (stageMapWithComparison E V a b E' V' a' b' d v ha hb n).2 (ha (n + 1))

/-- The canonical sequentialization is natural through its actual strict telescope map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationNaturality.lean:78"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
def inducedTelescopeMap :
    Telescope.prespectrum (stage E V a b) (transition E V a b) ⟶
      Telescope.prespectrum (stage E' V' a' b') (transition E' V' a' b') :=
  Telescope.map _ _ _ _ (stageMap E V a b E' V' a' b' d v ha hb)
    (fun n ↦ (transition_naturality E V a b E' V' a' b' d v ha hb n).symm)

variable (f : ∀ n, E n ⟶ E (n + 1)) (f' : ∀ n, E' n ⟶ E' (n + 1))
    (H : ∀ n, Homotopy (a n) (f n ≫ b n))
    (H' : ∀ n, Homotopy (a' n) (f' n ≫ b' n))
    (hH : ∀ n k s x, (v n).map k ((H n).level k (s, x)) =
      (H' n).level k (s, (d n).map k x))

include hH in
/-- Every time value of the constructed comparison track is strictly natural. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationNaturality.lean:92"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
theorem comparisonTrack_naturality (n k : ℕ) (s : unitInterval) (x : (E n).space k) :
    (stageMap E V a b E' V' a' b' d v ha hb (n + 1)).map k
        ((comparisonTrack E V a b f H n).level k (s, x)) =
      (comparisonTrack E' V' a' b' f' H' n).level k (s, (d n).map k x) := by
  cases n with
  | zero => exact hH 0 k s x
  | succ n =>
    change (HomotopyPushout.map _ _ _ _ _ _ _
        (stageMapWithComparison E V a b E' V' a' b' d v ha hb n).2 (ha (n + 1))).map k
        ((((HomotopyPushout.glue _ _).levelHomotopy k).trans
          (Homotopy.levelHomotopy _ k)) (s, x)) =
      (((HomotopyPushout.glue _ _).levelHomotopy k).trans
        (Homotopy.levelHomotopy _ k)) (s, (d (n + 1)).map k x)
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · rfl
    · exact congrArg (HomotopyPushout.right
        (comparison E' V' a' b' (n + 1)) (a' (n + 1)) k) (hH (n + 1) k _ x)

variable (hd : ∀ n, d n ≫ f' n = f n ≫ d (n + 1))

include hH in
/-- Strict input naturality and every original track time give a strict telescope square. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationNaturality.lean:115"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
theorem telescopeMap_naturality :
    Telescope.map E f E' f' d hd ≫ telescopeMap E' V' a' b' f' H' =
      telescopeMap E V a b f H ≫ inducedTelescopeMap E V a b E' V' a' b' d v ha hb := by
  apply Telescope.hom_ext
  intro k n s x
  change (Telescope.mapOfHomotopies E' f' (stage E' V' a' b') (transition E' V' a' b')
      (comparison E' V' a' b') (comparisonTrack E' V' a' b' f' H')).map k
        (Telescope.cylinder E' f' k n (s, (d n).map k x)) =
    (inducedTelescopeMap E V a b E' V' a' b' d v ha hb).map k
      ((Telescope.mapOfHomotopies E f (stage E V a b) (transition E V a b)
        (comparison E V a b) (comparisonTrack E V a b f H)).map k
          (Telescope.cylinder E f k n (s, x)))
  by_cases hs : (s : ℝ) ≤ 1 / 2
  · rw [Telescope.mapOfHomotopies_first_half _ _ _ _ _ _ _ _ _ hs,
      Telescope.mapOfHomotopies_first_half _ _ _ _ _ _ _ _ _ hs]
    exact congrArg (fun y ↦ Telescope.cylinder (stage E' V' a' b')
      (transition E' V' a' b') k n (_, y))
        (congrArg (fun m ↦ m.map k x)
          (comparison_naturality E V a b E' V' a' b' d v ha hb n)).symm
  · rw [Telescope.mapOfHomotopies_second_half _ _ _ _ _ _ _ _ _ hs,
      Telescope.mapOfHomotopies_second_half _ _ _ _ _ _ _ _ _ hs]
    exact congrArg (fun y ↦ (Telescope.inclusion (stage E' V' a' b')
      (transition E' V' a' b') (n + 1)).map k y)
        (comparisonTrack_naturality E V a b E' V' a' b' d v ha hb f f' H H' hH n k _ x).symm

end Topology.LoopPrespectrum.ZigzagSequentialization
