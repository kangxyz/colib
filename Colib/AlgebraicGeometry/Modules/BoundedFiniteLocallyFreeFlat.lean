/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectWaldhausen
public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFreeWaldhausen
public import
  StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation

/-!
# The Literal Bounded Vector-Bundle Inclusion into Flat Perfect Complexes

Finite locally free sheaves are flat. Thus the original globally bounded vector-bundle
complex, with its actual chain maps, lies in the bounded-above flat perfect class. Both
inclusions use the inherited quotient cofibrations. No resolution property is required.

Adapted from the strict-to-flat inclusion used in
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/Functor.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

/-- The original bounded vector-bundle complex is bounded above, flat and native perfect. -/
theorem boundedAboveFlatPerfectComplex_of_boundedFiniteLocallyFree
    {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : boundedFiniteLocallyFreeComplex X K) :
    boundedAboveFlatPerfectComplex X.toRingedSpace K :=
  ⟨isPerfectComplex_of_boundedFiniteLocallyFree hK, hK.1.2,
    fun n => AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree (K.X n) (hK.2 n)⟩

/-- The literal full-chain inclusion keeps the original bounded vector-bundle objects. -/
def boundedFiniteLocallyFreeFlatInclusion (X : Scheme.{u}) :
    (boundedFiniteLocallyFreeComplex X).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ hK =>
    boundedAboveFlatPerfectComplex_of_boundedFiniteLocallyFree hK)

instance boundedFiniteLocallyFreeFlatInclusion_additive (X : Scheme.{u}) :
    (boundedFiniteLocallyFreeFlatInclusion X).Additive where
  map_add := by intros; rfl

/-- Both inherited conflations are the unchanged ambient short exact sequences. -/
def boundedFiniteLocallyFreeFlatExactInclusion (X : Scheme.{u}) :
    CategoryTheory.ExactCategory.ExactFunctor (boundedFiniteLocallyFreeExactStructure X)
      (boundedAboveFlatPerfectExactStructure X.toRingedSpace) where
  toFunctor := boundedFiniteLocallyFreeFlatInclusion X
  map_conflation _ hS := hS

/-- Inherited exact sequences give the exact strict-to-flat comparison. -/
theorem boundedFiniteLocallyFreeFlatInclusion_isExact (X : Scheme.{u}) :
    Waldhausen.IsExact (boundedFiniteLocallyFreeWaldhausen X).cof
      (boundedFiniteLocallyFreeWaldhausen X).weq
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq
      (boundedFiniteLocallyFreeFlatInclusion X) where
  zero h := (boundedFiniteLocallyFreeFlatInclusion X).map_isZero h
  cofibration f hf := (boundedFiniteLocallyFreeFlatExactInclusion X).map_inflation f hf
  weak _ hf := hf
  pushout hi h := (boundedFiniteLocallyFreeFlatExactInclusion X).map_isPushout hi h

/-- The two literal inclusions compose to the original vector-bundle-to-perfect inclusion. -/
@[simp]
theorem boundedFiniteLocallyFreeFlatInclusion_comp (X : Scheme.{u}) :
    boundedFiniteLocallyFreeFlatInclusion X ⋙ boundedAboveFlatPerfectInclusion X.toRingedSpace =
      boundedFiniteLocallyFreePerfectInclusion X := rfl

end Stacks.Perfect.BoundedLocallyFreeComplexes
