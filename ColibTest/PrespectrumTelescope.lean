/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Prespectrum.TelescopeHomotopy

/-!
# Actual telescope consumers

General tests retain independent stage, cylinder, homotopy and loop coordinates.
A real-line constant prespectrum gives an inhabited, nontrivial quotient consumer:
its telescope retracts onto the real line and doubling acts on the entire cylinders.
-/

open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval

noncomputable section

namespace ColibTest.PrespectrumTelescope

universe u

section General

variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

example (k i : ℕ) (s t : unitInterval) (x : (E i).space k) :
    (Telescope.prespectrum E f).structureMap k (Telescope.cylinder E f k i (s, x)) t =
      Telescope.cylinder E f (k + 1) i (s, (E i).structureMap k x t) := rfl

example (k : ℕ) (x : (E 0).space k) :
    (Telescope.inclusionHomotopy E f 0).level k (1, x) =
      (Telescope.inclusion E f 1).map k ((f 0).map k x) :=
  Telescope.cylinder_one E f k 0 x

example (k i : ℕ) (s t : unitInterval) (x : (E i).space k) :
    (Telescope.inclusionHomotopy E f i).level (k + 1)
        (s, (E i).structureMap k x t) =
      (Telescope.prespectrum E f).structureMap k
        ((Telescope.inclusionHomotopy E f i).level k (s, x)) t := rfl

example : Telescope.desc E f (Telescope.inclusion E f)
    (Telescope.inclusionHomotopy E f) = 𝟙 (Telescope.prespectrum E f) := by
  apply Telescope.hom_ext
  intro k i s x
  rfl

end General

/-- Real lines in all degrees, with the actual constant loop structure. -/
abbrev realPrespectrum : LoopPrespectrum where
  space _ := TopCat.of ℝ
  point _ := 0
  structureMap _ := ContinuousMap.const _ (Path.refl 0)
  map_point _ := rfl

/-- The identity sequence on the nontrivial real-line prespectrum. -/
abbrev stages (_ : ℕ) := realPrespectrum

abbrev transition (i : ℕ) : stages i ⟶ stages (i + 1) := 𝟙 realPrespectrum

def projectionTrack (i : ℕ) :
    Homotopy (𝟙 realPrespectrum) (transition i ≫ 𝟙 realPrespectrum) where
  level _ := ⟨fun z ↦ z.2, continuous_snd⟩
  at_zero _ _ := rfl
  at_one _ _ := rfl
  at_point _ _ := rfl
  comm _ _ _ _ := rfl

/-- A concrete continuous prespectrum map out of the entire quotient. -/
def projection : Telescope.prespectrum stages transition ⟶ realPrespectrum :=
  Telescope.desc stages transition (fun _ ↦ 𝟙 realPrespectrum) projectionTrack

example (i : ℕ) : Telescope.inclusion stages transition i ≫ projection = 𝟙 realPrespectrum :=
  Telescope.inclusion_desc stages transition (fun _ ↦ 𝟙 realPrespectrum) projectionTrack i

example (k i : ℕ) (s : unitInterval) (x : ℝ) :
    projection.map k (Telescope.cylinder stages transition k i (s, x)) = x := rfl

example : (Telescope.inclusion stages transition 0).map 0 (1 : ℝ) ≠
    Telescope.point stages transition 0 := by
  intro h
  have hp := congrArg (projection.map 0) h
  change (1 : ℝ) = 0 at hp
  exact one_ne_zero hp

/-- Doubling, as an actual based continuous prespectrum morphism. -/
def doubling : realPrespectrum ⟶ realPrespectrum where
  map _ := ⟨fun x ↦ x + x, by fun_prop⟩
  map_point _ := by exact add_zero 0
  comm _ _ := by ext t; exact add_zero 0

def doubledTelescope : Telescope.prespectrum stages transition ⟶
    Telescope.prespectrum stages transition :=
  Telescope.map stages transition stages transition (fun _ ↦ doubling)
    (by intro i; simp [transition])

example (k i : ℕ) (s : unitInterval) (x : ℝ) :
    doubledTelescope.map k (Telescope.cylinder stages transition k i (s, x)) =
      Telescope.cylinder stages transition k i (s, x + x) := rfl

example : doubledTelescope ≫ projection = projection ≫ doubling := by
  apply Telescope.hom_ext
  intro k i s x
  rfl

example : Telescope.inclusion stages transition 0 ≫ doubledTelescope =
    doubling ≫ Telescope.inclusion stages transition 0 :=
  Telescope.inclusion_map stages transition stages transition (fun _ ↦ doubling)
    (by intro i; simp [transition]) 0

example (i : ℕ) : Telescope.inclusion stages transition (i + 1) ≫ doubledTelescope =
    doubling ≫ Telescope.inclusion stages transition (i + 1) :=
  Telescope.inclusion_map stages transition stages transition (fun _ ↦ doubling)
    (by intro j; simp [transition]) (i + 1)

/-- A nonconstant based homotopy, not an assumed family of desired telescope laws. -/
def doublingTrack : Homotopy (zeroHom realPrespectrum realPrespectrum) doubling where
  level _ := ⟨fun z ↦ (z.1 : ℝ) * (z.2 + z.2), by fun_prop⟩
  at_zero _ x := by change (0 : ℝ) * (x + x) = 0; exact zero_mul _
  at_one _ x := by change (1 : ℝ) * (x + x) = x + x; exact one_mul _
  at_point _ s := by change (s : ℝ) * (0 + 0) = 0; simp
  comm _ s _ _ := by change (s : ℝ) * (0 + 0) = 0; simp

def telescopeDoublingTrack :=
  Telescope.mapHomotopy stages transition stages transition
    (fun _ ↦ zeroHom realPrespectrum realPrespectrum) (fun _ ↦ doubling)
    (by intro i; simp [transition]) (by intro i; simp [transition])
    (fun _ ↦ doublingTrack) (by intro i k s x; rfl)

example (r s : unitInterval) (x : ℝ) :
    telescopeDoublingTrack.level 0 (r, Telescope.cylinder stages transition 0 0 (s, x)) =
      Telescope.cylinder stages transition 0 0 (s, (r : ℝ) * (x + x)) := rfl

example (k i : ℕ) (r s : unitInterval) (x : ℝ) :
    telescopeDoublingTrack.level k
        (r, Telescope.cylinder stages transition k (i + 1) (s, x)) =
      Telescope.cylinder stages transition k (i + 1) (s, (r : ℝ) * (x + x)) := rfl

section Homotopy

variable (E E' : ℕ → LoopPrespectrum.{u})
    (f : ∀ i, E i ⟶ E (i + 1)) (f' : ∀ i, E' i ⟶ E' (i + 1))
    (a b : ∀ i, E i ⟶ E' i)
    (ha : ∀ i, a i ≫ f' i = f i ≫ a (i + 1))
    (hb : ∀ i, b i ≫ f' i = f i ≫ b (i + 1))
    (H : ∀ i, Homotopy (a i) (b i))
    (hH : ∀ i k s x, (f' i).map k ((H i).level k (s, x)) =
      (H (i + 1)).level k (s, (f i).map k x))

example (k i : ℕ) (r s t : unitInterval) (x : (E i).space k) :
    (Telescope.mapHomotopy E f E' f' a b ha hb H hH).level (k + 1)
        (r, Telescope.cylinder E f (k + 1) i (s, (E i).structureMap k x t)) =
      Telescope.cylinder E' f' (k + 1) i
        (s, (E' i).structureMap k ((H i).level k (r, x)) t) := by
  rw [Telescope.mapHomotopy_cylinder, (H i).comm]

example (k : ℕ) (r s : unitInterval) (x : (E 0).space k) :
    (Telescope.mapHomotopy E f E' f' a b ha hb H hH).level k
        (r, Telescope.cylinder E f k 0 (s, x)) =
      Telescope.cylinder E' f' k 0 (s, (H 0).level k (r, x)) := rfl

end Homotopy

end ColibTest.PrespectrumTelescope
