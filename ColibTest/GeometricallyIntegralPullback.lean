/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Chow.GeometricallyIntegralPullback

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

variable (C : ChowSituation.{u}) {P Q : Scheme.{u}}
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
  (sQ : Q ⟶ C.S) [LocallyOfFiniteType sQ]
  (f : P ⟶ Q) [LocallyOfFiniteType f] [Flat f]
  [GeometricallyIntegral f] [UniversallyOpen f]
  (hbase : f ≫ sQ = sP) (r : ℕ) (hrel : AlgebraicGeometry.RelativeDimension f r)

example (x : Q) :
    let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
    IsIntegral ((integralComponentAt x).comap f).subscheme := by
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
  exact isIntegral_comap_integralComponentAt f x

example (x : Q) :
    let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
    f (geometricallyIntegralPullbackPoint f x) = x := by
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
  exact geometricallyIntegralPullbackPoint_map f x

example (x : Q) :
    let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
    flatPullbackWeight C sP f
      (relativeDimension C.dimensionFunction sQ x + (r : ℤ))
      (geometricallyIntegralPullbackPoint f x) = 1 := by
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
  exact flatPullbackWeight_geometricallyIntegralPullbackPoint C sP sQ f hbase r hrel x

example (x : Q) (n : ℤ) :
    let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
    (flatPullback C sP sQ f hbase r hrel
      (relativeDimension C.dimensionFunction sQ x)
      (pointCycleAtOwnDimension C sQ x (-n))).val =
        single (geometricallyIntegralPullbackPoint f x) (-n) := by
  let : IsLocallyNoetherian Q := LocallyOfFiniteType.isLocallyNoetherian sQ
  exact flatPullback_pointCycleAtOwnDimension C sP sQ f hbase r hrel x (-n)

#check length_comapRestrict_generic_fiber
#check flatPullbackWeight_eq_one_of_reduced_generic_fiber
#check flatPullbackWeight_eq_zero_of_ne_geometricallyIntegralPullbackPoint
