/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.StrictSquareConeInterchange
noncomputable section
open CategoryTheory Topology
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T)

example : Arrow (Arrow LoopPrespectrum.{u}) :=
  coneSquare a

example : mappingCone (spanMap a) ≅ span (coneSquare a) :=
  coneSpanIso a

example :
    (coneSpanIso a).hom ≫ comparison (coneSquare a) =
      ConeConeTranspose.vertical (comparison S) (comparison T) (spanMap a) a.right.right
        (comparison_naturality a) :=
  coneSpanIso_comparison a

example :
    mappingCone (mappingConeMap (strictSquareComparisonFunctor.map a)) ≅
      mappingCone (comparison (coneSquare a)) :=
  coneInterchangeIso a

example (n : ℕ) (y : T.right.right.space n) :
    (coneInterchangeIso a).hom.map n
      ((mappingConeInclusion (mappingConeMap (strictSquareComparisonFunctor.map a))).map n
        ((mappingConeInclusion (comparison T)).map n y)) =
      (mappingConeInclusion (comparison (coneSquare a))).map n
        ((mappingConeInclusion a.right.right).map n y) :=
  coneInterchangeIso_inclusion_inclusion a n y

example (n : ℕ) (r s : unitInterval)
    (x : (span S).space n) :
    (coneInterchangeIso a).hom.map n
      (ReducedMappingCone.cylinder ((mappingCone (comparison S)).point n)
        ((mappingCone (comparison T)).point n)
        ((mappingConeMap (strictSquareComparisonFunctor.map a)).map n)
        (r, ReducedMappingCone.cylinder ((span S).point n) (S.right.right.point n)
          ((comparison S).map n) (s, x))) =
      ReducedMappingCone.cylinder ((span (coneSquare a)).point n)
        ((mappingCone a.right.right).point n) ((comparison (coneSquare a)).map n)
        (s, (coneSpanIso a).hom.map n
          (ReducedMappingCone.cylinder ((span S).point n) ((span T).point n)
            ((spanMap a).map n) (r, x))) :=
  coneInterchangeIso_doubleCylinder a n r s x

end Topology.LoopPrespectrum.StrictSquare
end
