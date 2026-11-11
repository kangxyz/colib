/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.StrictSquarePushout
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare.Pushout
open HomotopyPushout
variable {S₀ S₁ S₂ : Arrow (Arrow LoopPrespectrum.{u})}
  (f : S₀ ⟶ S₁) (g : S₀ ⟶ S₂)

example : left f g ≫ bottom f g = top f g ≫ right f g :=
  comm f g

example : Arrow (Arrow LoopPrespectrum.{u}) :=
  square f g

example : prespectrum (spanMap f) (spanMap g) ≅ span (square f g) :=
  spanIso f g

example :
    (spanIso f g).hom ≫ comparison (square f g) =
      spanArrowMap (strictSquareComparisonFunctor.map f) (strictSquareComparisonFunctor.map g) :=
  spanIso_comparison f g

example :
    Arrow.mk (spanArrowMap (strictSquareComparisonFunctor.map f)
      (strictSquareComparisonFunctor.map g)) ≅ Arrow.mk (comparison (square f g)) :=
  comparisonArrowIso f g

example :
    prespectrum (mappingConeMap (strictSquareComparisonFunctor.map f))
      (mappingConeMap (strictSquareComparisonFunctor.map g)) ≅
        mappingCone (comparison (square f g)) :=
  totalIso f g

end Topology.LoopPrespectrum.StrictSquare.Pushout
end
