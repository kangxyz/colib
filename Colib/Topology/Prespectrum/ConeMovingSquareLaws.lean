/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.Topology.Prespectrum.ConeHomotopy
public import Colib.Topology.Prespectrum.HomotopySquare
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.Topology.Prespectrum.ZeroHomComposition

/-!
# Cone Moving Square Laws

Exact restriction and descent for homotopies of the original reduced cone.
The Laurent inclusion may move. Both independent cylinder and comparison parameters survive.
The square is necessary as well as sufficient; this module does not construct a geometric square.

The equivalence fixes both cone maps and the prescribed inclusion track.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The actual entire null track obtained by evaluating a map on the original cone cylinder. -/
def mappingConeMapNullTrack (k : mappingCone f ⟶ G) :
    Homotopy (f ≫ (mappingConeInclusion f ≫ k)) (zeroHom E G) :=
  ((mappingConeHomotopy f).postcomp k).cast (Category.assoc _ _ _) (zeroHom_comp _)

variable {k₀ k₁ : mappingCone f ⟶ G}
  (L : Homotopy (mappingConeInclusion f ≫ k₀) (mappingConeInclusion f ≫ k₁))

/-- The exact missing two-parameter cone-cylinder filling, with prescribed inclusion motion. -/
abbrev MappingConeMapNullSquare :=
  (mappingConeMapNullTrack f k₀).Square (mappingConeMapNullTrack f k₁)
    (Homotopy.precomp f L) (Homotopy.refl (zeroHom E G))

variable (S : MappingConeMapNullSquare f L)

/-- Jointly continuous descent of the supplied full moving null square. -/
def mappingConeMovingSquareFamily (n : ℕ) :
    C((mappingCone f).space n, C(unitInterval, G.space n)) :=
  ReducedMappingCone.desc (E.point n) (F.point n) (f.map n)
    (ContinuousMap.curry ⟨fun z : F.space n × unitInterval ↦ L.level n (z.2, z.1), by fun_prop⟩)
    (ContinuousMap.curry ⟨fun z : (unitInterval × E.space n) × unitInterval ↦
      S.level n (z.2, z.1), by fun_prop⟩)
    (by intro x; ext r; exact S.left n r x)
    (by intro x; ext r; exact (S.right n r x).trans (L.at_point n r).symm)
    (by intro s; ext r; exact (S.at_point n r s).trans (L.at_point n r).symm)

/-- A full moving square gives a whole homotopy between the exact original cone maps. -/
def mappingConeHomotopyOfNullSquare : Homotopy k₀ k₁ where
  level n := ⟨fun z ↦ mappingConeMovingSquareFamily f L S n z.2 z.1,
    (mappingConeMovingSquareFamily f L S n).uncurry.continuous.comp continuous_swap⟩
  at_zero n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => exact L.at_zero n y
      | inr z => exact S.at_zero n z.1 z.2
  at_one n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => exact L.at_one n y
      | inr z => exact S.at_one n z.1 z.2
  at_point n r := L.at_point n r
  comm n r q t := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => exact L.comm n r y t
      | inr z => exact S.comm n r z.1 z.2 t

/-- The inclusion retains the prescribed track exactly, with no inserted constant segment. -/
@[simp] theorem mappingConeHomotopyOfNullSquare_inclusion
    (n : ℕ) (r : unitInterval) (y : F.space n) :
    (mappingConeHomotopyOfNullSquare f L S).level n
      (r, (mappingConeInclusion f).map n y) = L.level n (r, y) := rfl

/-- The entire original cone cylinder retains the supplied square with independent times. -/
@[simp] theorem mappingConeHomotopyOfNullSquare_cylinder
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (mappingConeHomotopyOfNullSquare f L S).level n
      (r, ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) =
        S.level n (r, (s, x)) := rfl

/-- Conversely, a whole cone homotopy with the prescribed inclusion gives exactly the null square.
Thus specifying the inclusion face alone cannot replace this obligation. -/
def mappingConeNullSquareOfHomotopy (H : Homotopy k₀ k₁)
    (hL : ∀ n r y, H.level n (r, (mappingConeInclusion f).map n y) = L.level n (r, y)) :
    MappingConeMapNullSquare f L where
  level n := ⟨fun z ↦ H.level n (z.1, (mappingConeHomotopy f).level n (z.2.1, z.2.2)),
    by fun_prop⟩
  at_zero n s x := H.at_zero n ((mappingConeHomotopy f).level n (s, x))
  at_one n s x := H.at_one n ((mappingConeHomotopy f).level n (s, x))
  left n r x := by
    change H.level n (r, (mappingConeHomotopy f).level n (0, x)) = _
    rw [(mappingConeHomotopy f).at_zero]
    exact hL n r (f.map n x)
  right n r x := by
    change H.level n (r, (mappingConeHomotopy f).level n (1, x)) = _
    rw [(mappingConeHomotopy f).at_one]
    exact H.at_point n r
  at_point n r s := by
    change H.level n (r, (mappingConeHomotopy f).level n (s, E.point n)) = _
    rw [(mappingConeHomotopy f).at_point]
    exact H.at_point n r
  comm n r s x t := by
    change H.level (n + 1) (r, (mappingConeHomotopy f).level (n + 1)
      (s, E.structureMap n x t)) = _
    rw [(mappingConeHomotopy f).comm, H.comm]
    rfl

/-- Exact, bidirectional obstruction criterion with all original cone maps and the fixed face. -/
theorem mappingConeHomotopy_with_inclusion_iff :
    (∃ H : Homotopy k₀ k₁,
      ∀ n r y, H.level n (r, (mappingConeInclusion f).map n y) = L.level n (r, y)) ↔
      Nonempty (MappingConeMapNullSquare f L) := by
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨mappingConeNullSquareOfHomotopy f L H hH⟩
  · rintro ⟨S⟩
    exact ⟨mappingConeHomotopyOfNullSquare f L S, fun _ _ _ ↦ rfl⟩

end Topology.LoopPrespectrum
