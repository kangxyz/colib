/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.StrictSquareCone
public import Colib.Topology.Prespectrum.ConeStableNaturality
public import Colib.Topology.Prespectrum.ParameterLoopingStableEquivalence

/-!
# Stable preservation by the original strict-square looped cone

The actual span map and final-corner map determine the original comparison-arrow square.
Genuine cone-to-fiber excision for its two rows lets the original signed cone sequence prove
stable preservation; the actual parameter-loop shift then completes the Bass operation.
The row-excision inputs remain explicit for arbitrary prespectra.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- The unchanged looped-cone square functor preserves stable sides under genuine row excision. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/StrictSquareStableEquivalence.lean:27"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem strictSquareLoopedConeFunctor_map_isStableEquivalence_of_excision
    {S T : Arrow (Arrow LoopPrespectrum.{u})} (a : S ⟶ T)
    (hS : IsStableEquivalence (mappingConeFiberComparison (StrictSquare.comparison S)))
    (hT : IsStableEquivalence (mappingConeFiberComparison (StrictSquare.comparison T)))
    (hspan : IsStableEquivalence (StrictSquare.spanMap a))
    (hfinal : IsStableEquivalence a.right.right) :
    IsStableEquivalence (strictSquareLoopedConeFunctor.map a) :=
  parameterLoopingMap_isStableEquivalence _
    (mappingConeMap_isStableEquivalence_of_excision
      (strictSquareComparisonFunctor.map a) hS hT hspan hfinal)

end Topology.LoopPrespectrum
