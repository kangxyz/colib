/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.Topology.Prespectrum.TelescopeHomotopyMapStable
open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.LoopPrespectrum.Telescope.HomotopyMapTest
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
  (a : ∀ i, E i ⟶ E' i)
  (H : ∀ i, Homotopy (a i ≫ f' i) (f i ≫ a (i + 1)))

example (i : ℕ) :
    inclusion E f i ≫ mapOfHomotopies E f E' f' a H = a i ≫ inclusion E' f' i :=
  inclusion_mapOfHomotopies E f E' f' a H i

example (k i : ℕ) (s : unitInterval)
    (hs : ¬(s : ℝ) ≤ 1 / 2) (x : (E i).space k) :
    (mapOfHomotopies E f E' f' a H).map k (cylinder E f k i (s, x)) =
      (inclusion E' f' (i + 1)).map k
        ((H i).level k
          (⟨2 * s - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 hs).le, s.2.2⟩⟩, x)) :=
  mapOfHomotopies_second_half E f E' f' a H k i s hs x

example (d : ℤ) :
    colimMap (homotopyStageStableDiagramMap E f E' f' a H d) ≫
        stableColimitComparison E' f' d =
      stableColimitComparison E f d ≫
        (stableHomotopyFunctor d).map (mapOfHomotopies E f E' f' a H) :=
  stableColimitComparison_mapOfHomotopies E f E' f' a H d

variable [∀ i k, T1Space ((E i).space k)] [∀ i k, T1Space ((E' i).space k)]
example (h : ∀ i, IsStableEquivalence (a i)) :
    IsStableEquivalence (mapOfHomotopies E f E' f' a H) :=
  mapOfHomotopies_isStableEquivalence E f E' f' a H h
end Topology.LoopPrespectrum.Telescope.HomotopyMapTest
