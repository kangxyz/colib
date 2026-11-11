/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeStableNaturality

/-!
# Detecting the original target map from genuine stable cone sequences

For a strict original arrow square with genuine row excision, stable equivalence on the
source and original cone maps implies stable equivalence on the unchanged target map.
The proof uses the original signed boundaries and the five lemma in every signed degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B)
  (hA : IsStableEquivalence (mappingConeFiberComparison A.hom))
  (hB : IsStableEquivalence (mappingConeFiberComparison B.hom))

include hA hB in
/-- Genuine original cone sequences detect stability of the exact original target map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeStableDetection.lean:30"
  "adaptation" "Original fixed-order finite-loop maps and whole equality transports."]
theorem right_isStableEquivalence_of_coneMap
    (hl : IsStableEquivalence sq.left) (hc : IsStableEquivalence (mappingConeMap sq)) :
    IsStableEquivalence sq.right := by
  have hshift (d : ℤ) : IsIso ((stableHomotopyFunctor (d + 1)).map sq.right) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (stableMappingConeConnecting A.hom hA (d + 1)).hom
      ((stableHomotopyFunctor (d + 1)).map A.hom).hom
      ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion A.hom)).hom
      (stableMappingConeConnecting A.hom hA d).hom
      (stableMappingConeConnecting B.hom hB (d + 1)).hom
      ((stableHomotopyFunctor (d + 1)).map B.hom).hom
      ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion B.hom)).hom
      (stableMappingConeConnecting B.hom hB d).hom
      ((stableHomotopyFunctor (d + 1 + 1)).map (mappingConeMap sq)).hom
      ((stableHomotopyFunctor (d + 1)).map sq.left).hom
      ((stableHomotopyFunctor (d + 1)).map sq.right).hom
      ((stableHomotopyFunctor (d + 1)).map (mappingConeMap sq)).hom
      ((stableHomotopyFunctor d).map sq.left).hom
      ?_ ?_ ?_ ?_
      (stableMappingConeConnecting_exact_source A.hom hA (d + 1))
      (stableMappingCone_exact_target A.hom hA (d + 1))
      (stableMappingConeConnecting_exact_cone A.hom hA d)
      (stableMappingConeConnecting_exact_source B.hom hB (d + 1))
      (stableMappingCone_exact_target B.hom hB (d + 1))
      (stableMappingConeConnecting_exact_cone B.hom hB d)
      ((ConcreteCategory.isIso_iff_bijective _).mp (hc (d + 1 + 1))).surjective
      ((ConcreteCategory.isIso_iff_bijective _).mp (hl (d + 1)))
      ((ConcreteCategory.isIso_iff_bijective _).mp (hc (d + 1)))
      ((ConcreteCategory.isIso_iff_bijective _).mp (hl d)).injective
    · ext x
      exact ConcreteCategory.congr_hom
        (stableMappingConeConnecting_naturality sq hA hB (d + 1)) x
    · ext x
      have he := congrArg ((stableHomotopyFunctor (d + 1)).map) sq.w
      rw [Functor.map_comp, Functor.map_comp] at he
      exact ConcreteCategory.congr_hom he x
    · ext x
      have he := congrArg ((stableHomotopyFunctor (d + 1)).map) (mappingConeInclusionSquare sq).w
      rw [Functor.map_comp, Functor.map_comp] at he
      exact ConcreteCategory.congr_hom he x
    · ext x
      exact ConcreteCategory.congr_hom (stableMappingConeConnecting_naturality sq hA hB d) x
  intro d
  have h := hshift (d - 1)
  rw [show d - 1 + 1 = d by omega] at h
  exact h

end Topology.LoopPrespectrum
