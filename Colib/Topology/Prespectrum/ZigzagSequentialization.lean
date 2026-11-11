/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.HomotopyPushout
public import Colib.Topology.Prespectrum.TelescopeHomotopyMap

/-!
# Sequentialization of a one-sided zigzag by its original homotopy pushouts

For original arrows `a n : E n ⟶ V n` and `b n : E (n + 1) ⟶ V n`, the first
sequential stage is `V 0`. Each following stage is the reduced homotopy pushout of the
previous comparison and the next forward arrow. The original `E 0` is retained as stage zero.
This is the canonical homotopy-pushout recurrence in Thomason--Trobaugh 6.4, with
`E n = F⁻ⁿ`, `V n = ΩΣF⁻⁽ⁿ⁺¹⁾`, `a n = Ωd ∘ (T ∪)` and `b n` the suspension unit.

A second tower on the same `E n` compares to this recurrence when supplied with whole
homotopies `a n ∼ f n ≫ b n`. Its actual telescope map uses those tracks and the original
pushout glue. There is no inverse-sequence choice and no assertion that the required tracks
exist for an arbitrary proposed Bass action.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.ZigzagSequentialization
variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)

/-- The positive sequential stage together with its original comparison arrow. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:34"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
def stageWithComparison : (n : ℕ) → Σ P : LoopPrespectrum.{u}, E (n + 1) ⟶ P
  | 0 => ⟨V 0, b 0⟩
  | n + 1 =>
    let previous := stageWithComparison n
    ⟨HomotopyPushout.prespectrum previous.2 (a (n + 1)),
      b (n + 1) ≫ HomotopyPushout.inr previous.2 (a (n + 1))⟩

/-- The literal canonical sequentialization, including the original initial object. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:42"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
def stage : ℕ → LoopPrespectrum.{u}
  | 0 => E 0
  | n + 1 => (stageWithComparison E V a b n).1

/-- The original arrows from the zigzag vertices to its sequential stages. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:47"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
def comparison : (n : ℕ) → E n ⟶ stage E V a b n
  | 0 => 𝟙 (E 0)
  | n + 1 => (stageWithComparison E V a b n).2

/-- The first solid forward arrow followed by the canonical left pushout inclusions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:52"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
def transition : (n : ℕ) → stage E V a b n ⟶ stage E V a b (n + 1)
  | 0 => a 0
  | n + 1 => HomotopyPushout.inl (comparison E V a b (n + 1)) (a (n + 1))

/-- Stage zero is the original initial vertex. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:56"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison.", simp]
theorem stage_zero : stage E V a b 0 = E 0 := rfl
/-- The first positive stage is the original middle vertex. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:57"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison.", simp]
theorem stage_one : stage E V a b 1 = V 0 := rfl
/-- The initial comparison is the identity on the original vertex. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:58"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison.", simp]
theorem comparison_zero : comparison E V a b 0 = 𝟙 (E 0) := rfl
/-- The first positive comparison is the original backward leg. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:59"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison.", simp]
theorem comparison_one : comparison E V a b 1 = b 0 := rfl
/-- The first transition is the original solid forward arrow. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:60"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison.", simp]
theorem transition_zero : transition E V a b 0 = a 0 := rfl

/-- The actual next object is the pushout of the previous comparison and next forward arrow. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:63"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
theorem stage_succ_succ (n : ℕ) : stage E V a b (n + 1 + 1) =
    HomotopyPushout.prespectrum (comparison E V a b (n + 1)) (a (n + 1)) := rfl

/-- The actual comparison is the suspension-unit leg followed by the right inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:67"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
theorem comparison_succ_succ (n : ℕ) : comparison E V a b (n + 1 + 1) =
    b (n + 1) ≫ HomotopyPushout.inr (comparison E V a b (n + 1)) (a (n + 1)) := rfl

/-- The actual next transition is the left inclusion of that same original pushout. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:71"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
theorem transition_succ (n : ℕ) : transition E V a b (n + 1) =
    HomotopyPushout.inl (comparison E V a b (n + 1)) (a (n + 1)) := rfl

variable (f : ∀ n, E n ⟶ E (n + 1))
    (H : ∀ n, Homotopy (a n) (f n ≫ b n))

/-- Original pushout glue followed by the specified whole factorization track. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:78"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
def comparisonTrack : (n : ℕ) →
    Homotopy (comparison E V a b n ≫ transition E V a b n)
      (f n ≫ comparison E V a b (n + 1))
  | 0 => (H 0).cast (Category.id_comp _).symm rfl
  | n + 1 =>
    (HomotopyPushout.glue (comparison E V a b (n + 1)) (a (n + 1))).trans
      (((H (n + 1)).postcomp
        (HomotopyPushout.inr (comparison E V a b (n + 1)) (a (n + 1)))).cast
          rfl (Category.assoc _ _ _))

/-- The original tower maps to the canonical pushout sequentialization by its whole tracks. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:89"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
def telescopeMap : Telescope.prespectrum E f ⟶
    Telescope.prespectrum (stage E V a b) (transition E V a b) :=
  Telescope.mapOfHomotopies E f (stage E V a b) (transition E V a b)
    (comparison E V a b) (comparisonTrack E V a b f H)

/-- Every original stage inclusion is retained by the actual homotopy-colimit comparison. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:95"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison.", simp]
theorem inclusion_telescopeMap (n : ℕ) :
    Telescope.inclusion E f n ≫ telescopeMap E V a b f H =
      comparison E V a b n ≫
        Telescope.inclusion (stage E V a b) (transition E V a b) n :=
  Telescope.inclusion_mapOfHomotopies E f _ _ _ _ n

/-- The full source telescope cylinder retains the supplied comparison track. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentialization.lean:102"
  "adaptation" "Original homotopy-pushout recurrence and supplied whole-track comparison."]
theorem telescopeMap_cylinder (k n : ℕ) (s : unitInterval) (x : (E n).space k) :
    (telescopeMap E V a b f H).map k (Telescope.cylinder E f k n (s, x)) =
      (Telescope.mapCoconeHomotopy E f (stage E V a b) (transition E V a b)
        (comparison E V a b) (comparisonTrack E V a b f H) n).level k (s, x) := rfl

end Topology.LoopPrespectrum.ZigzagSequentialization
