module

import Colib.Topology.Prespectrum.PushoutHomotopySquareCells

/-!
# Terminal cell clocks for original prespectrum pushouts

The final cell reverses only the second square parameter. The structure clock
is independent, and remains unchanged when passing between successive levels.
-/

open CategoryTheory Topology Topology.LoopPrespectrum
open Topology.LoopPrespectrum.HomotopyPushout
open scoped Topology unitInterval

universe u

variable {A B C A' B' C' : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (Hf : Homotopy (f ≫ b) (a ≫ f')) (Hg : Homotopy (g ≫ c) (a ≫ g'))

example (n : ℕ) (t : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map n
      (cylinder f g n (secondHalfTime (firstHalfTime t), x)) =
      cylinder f' g' n (t, a.map n x) :=
  mapOfHomotopies_middleQuarter f g f' g' a b c Hf Hg n t x

example (n : ℕ) (t z : unitInterval) (x : A.space n) :
    (mapOfHomotopies f g f' g' a b c Hf Hg).map (n + 1)
      (cylinder f g (n + 1) (secondHalfTime (secondHalfTime t), A.structureMap n x z)) =
      (prespectrum f' g').structureMap n
        ((inr f' g').map n (Hg.level n (unitInterval.symm t, x))) z := by
  rw [mapOfHomotopies_lastQuarter]
  exact (Hg.postcomp (inr f' g')).comm n (unitInterval.symm t) x z
