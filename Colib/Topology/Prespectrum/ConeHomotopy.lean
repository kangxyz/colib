/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.Prespectrum.MappingCone
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Homotopies of actual cone descents

A relative comparison of original nullhomotopies descends to a whole coherent homotopy between the
actual cone maps. The comparison is curried into the compact-open interval mapping space before
quotient descent. Postcomposition and the original identity descent retain every cylinder point.
-/
@[expose] public section
noncomputable section

open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum

variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) (g : F ⟶ G)
  {H K : Homotopy (f ≫ g) (zeroHom E G)} (J : H.RelHomotopy K)

/-- The supplied relative nullhomotopy comparison descends into the interval mapping space. -/
def mappingConeDescHomotopyFamily (n : ℕ) :
    C((mappingCone f).space n, C(unitInterval, G.space n)) :=
  ReducedMappingCone.desc (E.point n) (F.point n) (f.map n)
    (ContinuousMap.curry ⟨fun z : F.space n × unitInterval ↦ g.map n z.1, by fun_prop⟩)
    (ContinuousMap.curry ⟨fun z : (unitInterval × E.space n) × unitInterval ↦
      J.level n (z.2, z.1), by fun_prop⟩)
    (by intro x; ext r; exact (J.at r).at_zero n x)
    (by intro x; ext r; exact ((J.at r).at_one n x).trans (g.map_point n).symm)
    (by intro s; ext r; exact ((J.at r).at_point n s).trans (g.map_point n).symm)

/-- Relative comparisons of whole nullhomotopies preserve the existing cone descent maps. -/
def mappingConeDescHomotopy :
    Homotopy (mappingConeDesc f g H) (mappingConeDesc f g K) where
  level n := ⟨fun z ↦ mappingConeDescHomotopyFamily f g J n z.2 z.1,
    (mappingConeDescHomotopyFamily f g J n).uncurry.continuous.comp continuous_swap⟩
  at_zero n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => rfl
      | inr z => exact (J.level n).apply_zero z
  at_one n q := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => rfl
      | inr z => exact (J.level n).apply_one z
  at_point n _r := g.map_point n
  comm n r q t := by
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl y => exact congrArg (fun p ↦ p t) (g.comm n y)
      | inr z => exact J.comm n r z.1 z.2 t

/-- The target map stays literally fixed throughout the descended homotopy. -/
@[simp] theorem mappingConeDescHomotopy_inclusion (n : ℕ) (r : unitInterval) (y : F.space n) :
    (mappingConeDescHomotopy f g J).level n (r, (mappingConeInclusion f).map n y) = g.map n y := rfl

/-- The original cylinder retains both supplied comparison parameters. -/
@[simp] theorem mappingConeDescHomotopy_cylinder
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (mappingConeDescHomotopy f g J).level n
      (r, ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) =
        J.level n (r, (s, x)) := rfl

/-- Descending the original cone inclusion and cylinder recovers its identity map exactly. -/
@[simp] theorem mappingConeDesc_self :
    mappingConeDesc f (mappingConeInclusion f) (mappingConeHomotopy f) = 𝟙 (mappingCone f) := by
  apply mappingCone_hom_ext
  · simp
  · intro n s x
    rfl

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/ConeHomotopy.lean:1-83"
  "adaptation" "Actual whole-track descent and its original homotopy comparison"]
  mappingConeDescHomotopy

end Topology.LoopPrespectrum
