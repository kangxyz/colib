module

import Colib.AlgebraicGeometry.Sites.Smooth.Torus

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite

universe u

noncomputable section

example (S : Scheme.{u}) : torusPower S 0 = base S := rfl
example (S : Scheme.{u}) (q : ℕ) (i : Fin (q + 1)) :
    torusInsertOne S q i ≫ torusDeleteCoordinate S q i = 𝟙 _ :=
  torusInsertOne_deleteCoordinate S q i
example (S : Scheme.{u}) (q : ℕ) (i : Fin (q + 1)) :
    IsClosedImmersion (torusInsertOne S q i).left := inferInstance
example (S : Scheme.{u}) :
    (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv (torusOneOver S) = 1 :=
  torusOneOver_represents_one S
example (S : Scheme.{u}) : torusPower S 1 ≅ multiplicativeGroupObject S :=
  torusPowerOneIso S
