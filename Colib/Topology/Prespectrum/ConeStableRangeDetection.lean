/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ConeStableNaturality

/-!
# Degreewise detection by the original stable cone sequence

The original signed cone sequence detects an arrow in one degree from vanishing in the two
adjacent cone degrees. Its five-term naturality diagram also detects the source of an original
arrow square from the precise surjectivity, bijectivity and injectivity needed in that degree.
Neither assertion promotes a bounded comparison to an all-degree stable equivalence.

Source: `Quillen/Topology/Prespectrum/ConeStableRangeDetection.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
universe u
namespace Topology.LoopPrespectrum

/-- Vanishing in exactly two adjacent cone degrees makes the original arrow invertible here. -/
theorem stableMap_isIso_of_cone_subsingleton {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : IsStableEquivalence (mappingConeFiberComparison f)) (d : ℤ)
    (hzero : Subsingleton (stableHomotopyGroup (mappingCone f) d))
    (hsucc : Subsingleton (stableHomotopyGroup (mappingCone f) (d + 1))) :
    IsIso ((stableHomotopyFunctor d).map f) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply (injective_iff_map_eq_zero ((stableHomotopyFunctor d).map f).hom).mpr
    intro x hx
    obtain ⟨y, hy⟩ := (stableMappingConeConnecting_exact_source f hf d x).mp hx
    have hy0 : y = 0 := hsucc.elim _ _
    rw [hy0, map_zero] at hy
    exact hy.symm
  · intro y
    exact (stableMappingCone_exact_target f hf d y).mp (hzero.elim _ _)

/-- The original five-term cone diagram detects its source map in the indicated degree. -/
theorem left_stableMap_isIso_of_coneMap {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B)
    (hA : IsStableEquivalence (mappingConeFiberComparison A.hom))
    (hB : IsStableEquivalence (mappingConeFiberComparison B.hom)) (d : ℤ)
    (hrsucc : Function.Surjective ((stableHomotopyFunctor (d + 1)).map sq.right))
    (hcsucc : Function.Bijective ((stableHomotopyFunctor (d + 1)).map (mappingConeMap sq)))
    (hr : Function.Bijective ((stableHomotopyFunctor d).map sq.right))
    (hc : Function.Injective ((stableHomotopyFunctor d).map (mappingConeMap sq))) :
    IsIso ((stableHomotopyFunctor d).map sq.left) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
    ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion A.hom)).hom
    (stableMappingConeConnecting A.hom hA d).hom
    ((stableHomotopyFunctor d).map A.hom).hom
    ((stableHomotopyFunctor d).map (mappingConeInclusion A.hom)).hom
    ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion B.hom)).hom
    (stableMappingConeConnecting B.hom hB d).hom
    ((stableHomotopyFunctor d).map B.hom).hom
    ((stableHomotopyFunctor d).map (mappingConeInclusion B.hom)).hom
    ((stableHomotopyFunctor (d + 1)).map sq.right).hom
    ((stableHomotopyFunctor (d + 1)).map (mappingConeMap sq)).hom
    ((stableHomotopyFunctor d).map sq.left).hom
    ((stableHomotopyFunctor d).map sq.right).hom
    ((stableHomotopyFunctor d).map (mappingConeMap sq)).hom
    ?_ ?_ ?_ ?_
    (stableMappingConeConnecting_exact_cone A.hom hA d)
    (stableMappingConeConnecting_exact_source A.hom hA d)
    (stableMappingCone_exact_target A.hom hA d)
    (stableMappingConeConnecting_exact_cone B.hom hB d)
    (stableMappingConeConnecting_exact_source B.hom hB d)
    (stableMappingCone_exact_target B.hom hB d)
    hrsucc hcsucc hr hc
  · ext x
    have he := congrArg ((stableHomotopyFunctor (d + 1)).map) (mappingConeInclusionSquare sq).w
    rw [Functor.map_comp, Functor.map_comp] at he
    exact ConcreteCategory.congr_hom he x
  · ext x
    exact ConcreteCategory.congr_hom (stableMappingConeConnecting_naturality sq hA hB d) x
  · ext x
    have he := congrArg ((stableHomotopyFunctor d).map) sq.w
    rw [Functor.map_comp, Functor.map_comp] at he
    exact ConcreteCategory.congr_hom he x
  · ext x
    have he := congrArg ((stableHomotopyFunctor d).map) (mappingConeInclusionSquare sq).w
    rw [Functor.map_comp, Functor.map_comp] at he
    exact ConcreteCategory.congr_hom he x

end Topology.LoopPrespectrum
