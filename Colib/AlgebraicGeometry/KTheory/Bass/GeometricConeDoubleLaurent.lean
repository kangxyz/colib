/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeSchemeNaturality
public import Colib.KTheory.Waldhausen.Iterated.StableHomotopy

/-!
# The actual permutation on double-Laurent representatives

The two original target inclusions give an actual prespectrum map from the
double-Laurent corner into the double cone. The geometric permutation acts
on these representatives by the original opposite Scheme factor swap.
No conclusion about the induced double-cokernel automorphism is imposed.

Adapted from the original construction in `Quillen/KTheory/Bass/GeometricConeDoubleLaurent.lean`.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare

universe u w

namespace KTheory.Bass.GeometricConeInterchange

/-- The two original cone inclusions retain the double-Laurent coefficient corner. -/
def doubleLaurentInclusion (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) :
    F.obj (laurent.op.obj (laurent.op.obj X)) ⟶ (coneFunctor.obj (coneFunctor.obj F)).obj X :=
  mappingConeInclusion (comparison (F.mapArrow.mapArrow.obj (square (laurent.op.obj X)))) ≫
    mappingConeInclusion (comparison ((coneFunctor.obj F).mapArrow.mapArrow.obj (square X)))

/-- On the whole original representative map, the permutation is exactly the original swap. -/
theorem doubleLaurentInclusion_permutation (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (X : Scheme.{u}ᵒᵖ) :
    doubleLaurentInclusion F X ≫ (permutation F X).hom =
      F.map (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
        (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op ≫ doubleLaurentInclusion F X := by
  apply Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact permutation_target_target F X n x

/-- Stable double-Laurent representatives retain the same actual factor-swap equation. -/
theorem doubleLaurentInclusion_permutation_stable
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) (X : Scheme.{u}ᵒᵖ) (d : ℤ) :
    (stableHomotopyFunctor d).map (doubleLaurentInclusion F X) ≫
        (stableHomotopyFunctor d).map (permutation F X).hom =
      (stableHomotopyFunctor d).map
          (F.map (baseProductSwapMap (laurentProjection (.of (ULift.{u} ℤ)))
            (laurentProjection (.of (ULift.{u} ℤ))) X.unop).op) ≫
        (stableHomotopyFunctor d).map (doubleLaurentInclusion F X) := by
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg (stableHomotopyFunctor d).map (doubleLaurentInclusion_permutation F X)

end KTheory.Bass.GeometricConeInterchange
