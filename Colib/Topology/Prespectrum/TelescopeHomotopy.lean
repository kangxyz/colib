/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Telescope

/-!
# Homotopies of maps of reduced telescopes

A family of coherent based prespectrum homotopies, strictly compatible with the
connecting maps at every time, induces a coherent based homotopy on the actual
reduced telescope. Continuity is obtained by descending into the compact-open
space of interval maps and then evaluating. In particular, no assertion about
products of arbitrary quotient maps is needed.

The compatibility hypothesis concerns the stage homotopies, not the conclusion.
This module proves homotopy invariance for these compatible homotopies; it does
not assert that arbitrary levelwise equivalences of diagrams admit compatible
homotopy inverses, or identify telescope homotopy groups with a colimit.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/TelescopeHomotopy.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The homotopy parameter
is curried before quotient descent; the cylinder and structure-loop parameters
remain independent. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
open unitInterval
universe u

namespace Topology.LoopPrespectrum.Telescope

variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
  (a b : ∀ i, E i ⟶ E' i)
  (ha : ∀ i, a i ≫ f' i = f i ≫ a (i + 1))
  (hb : ∀ i, b i ≫ f' i = f i ≫ b (i + 1))
  (H : ∀ i, Homotopy (a i) (b i))
  (hH : ∀ i k s x, (f' i).map k ((H i).level k (s, x)) =
    (H (i + 1)).level k (s, (f i).map k x))

/-- The cylinderwise homotopy, curried in the homotopy parameter. -/
def homotopyPiece (k i : ℕ) : C(I × (E i).space k, C(I, Space E' f' k)) :=
  ContinuousMap.curry
    ⟨fun z ↦ cylinder E' f' k i (z.1.1, (H i).level k (z.2, z.1.2)), by fun_prop⟩

/-- Descend the whole interval map before evaluating its time parameter. -/
def homotopyFamily (k : ℕ) : C(Space E f k, C(I, Space E' f' k)) where
  toFun := Quot.lift (fun z ↦ homotopyPiece E E' f' a b H k z.1 z.2) (by
    intro x y h
    cases h with
    | step i x =>
      ext s
      change cylinder E' f' k i (1, (H i).level k (s, x)) =
        cylinder E' f' k (i + 1) (0, (H (i + 1)).level k (s, (f i).map k x))
      rw [cylinder_one, hH]
    | base i t =>
      ext s
      change cylinder E' f' k i (t, (H i).level k (s, (E i).point k)) =
        cylinder E' f' k 0 (0, (H 0).level k (s, (E 0).point k))
      rw [(H i).at_point, (H 0).at_point, cylinder_point, cylinder_point])
  continuous_toFun := continuous_quot_lift _
    (continuous_sigma (fun i ↦ (homotopyPiece E E' f' a b H k i).continuous))

/-- Strictly compatible stage homotopies induce a homotopy of telescope maps. -/
@[colib_tag "COL-0339"]
def mapHomotopy : Homotopy (map E f E' f' a ha) (map E f E' f' b hb) where
  level k := ⟨fun z ↦ homotopyFamily E f E' f' a b H hH k z.2 z.1,
    (homotopyFamily E f E' f' a b H hH k).uncurry.continuous.comp continuous_swap⟩
  at_zero k q := by
    induction q using Quot.inductionOn with
    | h z =>
      change cylinder E' f' k z.1 (z.2.1, (H z.1).level k (0, z.2.2)) = _
      rw [(H z.1).at_zero]
      rfl
  at_one k q := by
    induction q using Quot.inductionOn with
    | h z =>
      change cylinder E' f' k z.1 (z.2.1, (H z.1).level k (1, z.2.2)) = _
      rw [(H z.1).at_one]
      rfl
  at_point k s := by
    change cylinder E' f' k 0 (0, (H 0).level k (s, (E 0).point k)) = _
    rw [(H 0).at_point]
    exact cylinder_point E' f' k 0 0
  comm k s q t := by
    induction q using Quot.inductionOn with
    | h z =>
      change cylinder E' f' (k + 1) z.1
          (z.2.1, (H z.1).level (k + 1) (s, (E z.1).structureMap k z.2.2 t)) =
        cylinder E' f' (k + 1) z.1
          (z.2.1, (E' z.1).structureMap k ((H z.1).level k (s, z.2.2)) t)
      rw [(H z.1).comm]

@[simp] theorem mapHomotopy_cylinder (k i : ℕ) (s t : I) (x : (E i).space k) :
    (mapHomotopy E f E' f' a b ha hb H hH).level k (s, cylinder E f k i (t, x)) =
      cylinder E' f' k i (t, (H i).level k (s, x)) := rfl

/-- Every time slice is the telescope map of the corresponding stage time slices. -/
theorem mapHomotopy_at (s : I) :
    (mapHomotopy E f E' f' a b ha hb H hH).at s =
      map E f E' f' (fun i ↦ (H i).at s) (by
        intro i
        apply Hom.ext
        funext k
        ext x
        exact hH i k s x) := by
  apply hom_ext
  intro k i t x
  rfl

end Topology.LoopPrespectrum.Telescope
