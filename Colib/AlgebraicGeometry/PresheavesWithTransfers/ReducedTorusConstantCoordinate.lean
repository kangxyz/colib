/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.Simplex.ParameterConstantCoordinateFormula
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusCoordinateInsertion
public import Colib.AlgebraicTopology.ConstantCoordinateSingle
/-! # The actual reduced-torus universal coordinate from a constant simplicial unit -/
@[expose] public noncomputable section
open CategoryTheory MonoidalCategory Opposite AlgebraicTopology
open AlgebraicGeometry.Scheme AlgebraicSimplex
universe u
namespace AlgebraicGeometry.PresheafWithTransfers
variable (k : Type u) [Field k]

/-- The original universal reduced weight-one section, made into a constant-source map. -/
def reducedTorusConstantParameterCoordinate :=
  simplicialConstantParameterCoordinate k (reducedTorusIntPresheaf k 1)
    (SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k)))
    (reducedTorusUniversalCoordinate k)

/-- The genuine degree-zero coordinate, via the native inverse augmentation. -/
def reducedTorusSingleParameterCoordinate :=
  constantCoordinateSingle _ _ (reducedTorusConstantParameterCoordinate k)

/-- The actual reindexed reduced-torus AW coordinate square is homotopic to its
augmentation/degree-zero formulation, retaining the unnormalized constant chain. -/
def reducedTorusConstantCoordinateAWHomotopy (q : ℕ) :=
  let G := SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
  let R := (SimplicialObject.whiskering
    ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
    ((SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)).obj
      (parameterReindex k G)
  constantCoordinateAWHomotopy (R.obj (reducedTorusIntSimplicial k q))
    (R.obj (reducedTorusIntSimplicial k 1)) _ (reducedTorusConstantParameterCoordinate k)

end AlgebraicGeometry.PresheafWithTransfers
