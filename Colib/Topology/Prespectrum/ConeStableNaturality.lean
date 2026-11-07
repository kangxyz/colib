/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.ConeStableExactness

/-!
# Naturality and stable comparison for the original cone sequence

The original strict cone map preserves the signed boundary transported from actual fiber
excision. The original five-lemma diagram consequently proves its stable equivalence from the
two original side maps, whenever genuine cone-to-fiber excision is proved for both original rows.
-/

/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeStableNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, endpoint casts, complete homotopies and hypotheses are retained
under their native mathematical owners. -/
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

/-- Original strict cone squares preserve the original signed boundary after actual excision. -/
theorem stableMappingConeConnecting_naturality (d : ℤ) :
    (stableHomotopyFunctor (d + 1)).map (mappingConeMap sq) ≫
      stableMappingConeConnecting B.hom hB d =
        stableMappingConeConnecting A.hom hA d ≫ (stableHomotopyFunctor d).map sq.left := by
  let := hB d
  have hn := congrArg ((stableHomotopyFunctor d).map) (mappingConeFiberComparison_naturality sq)
  rw [Functor.map_comp, Functor.map_comp] at hn
  apply (cancel_mono ((stableHomotopyFunctor d).map (mappingConeFiberComparison B.hom))).1
  rw [Category.assoc, stableMappingConeConnecting_comparison]
  refine (stableFiberConnecting_naturality (mappingConeInclusionSquare sq) d).trans ?_
  calc
    stableFiberConnecting (mappingConeInclusion A.hom) d ≫
        (stableHomotopyFunctor d).map (homotopyFiberMap (mappingConeInclusionSquare sq)) =
      (stableMappingConeConnecting A.hom hA d ≫
        (stableHomotopyFunctor d).map (mappingConeFiberComparison A.hom)) ≫
          (stableHomotopyFunctor d).map (homotopyFiberMap (mappingConeInclusionSquare sq)) :=
      congrArg (fun a ↦ a ≫ (stableHomotopyFunctor d).map
        (homotopyFiberMap (mappingConeInclusionSquare sq)))
          (stableMappingConeConnecting_comparison A.hom hA d).symm
    _ = stableMappingConeConnecting A.hom hA d ≫
        ((stableHomotopyFunctor d).map (mappingConeFiberComparison A.hom) ≫
          (stableHomotopyFunctor d).map (homotopyFiberMap (mappingConeInclusionSquare sq))) :=
      Category.assoc _ _ _
    _ = stableMappingConeConnecting A.hom hA d ≫
        ((stableHomotopyFunctor d).map sq.left ≫
          (stableHomotopyFunctor d).map (mappingConeFiberComparison B.hom)) :=
      congrArg (fun a ↦ stableMappingConeConnecting A.hom hA d ≫ a) hn.symm
    _ = _ := (Category.assoc _ _ _).symm

include hA hB in
/-- Actual stable side equivalences induce stable equivalence of the unchanged strict cone map. -/
theorem mappingConeMap_isStableEquivalence_of_excision
    (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) :
    IsStableEquivalence (mappingConeMap sq) := by
  have hshift (d : ℤ) : IsIso ((stableHomotopyFunctor (d + 1)).map (mappingConeMap sq)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      ((stableHomotopyFunctor (d + 1)).map A.hom).hom
      ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion A.hom)).hom
      (stableMappingConeConnecting A.hom hA d).hom ((stableHomotopyFunctor d).map A.hom).hom
      ((stableHomotopyFunctor (d + 1)).map B.hom).hom
      ((stableHomotopyFunctor (d + 1)).map (mappingConeInclusion B.hom)).hom
      (stableMappingConeConnecting B.hom hB d).hom ((stableHomotopyFunctor d).map B.hom).hom
      ((stableHomotopyFunctor (d + 1)).map sq.left).hom
      ((stableHomotopyFunctor (d + 1)).map sq.right).hom
      ((stableHomotopyFunctor (d + 1)).map (mappingConeMap sq)).hom
      ((stableHomotopyFunctor d).map sq.left).hom ((stableHomotopyFunctor d).map sq.right).hom
      ?_ ?_ ?_ ?_
      (stableMappingCone_exact_target A.hom hA (d + 1))
      (stableMappingConeConnecting_exact_cone A.hom hA d)
      (stableMappingConeConnecting_exact_source A.hom hA d)
      (stableMappingCone_exact_target B.hom hB (d + 1))
      (stableMappingConeConnecting_exact_cone B.hom hB d)
      (stableMappingConeConnecting_exact_source B.hom hB d)
      ((ConcreteCategory.isIso_iff_bijective _).mp (hl (d + 1))).surjective
      ((ConcreteCategory.isIso_iff_bijective _).mp (hr (d + 1)))
      ((ConcreteCategory.isIso_iff_bijective _).mp (hl d))
      ((ConcreteCategory.isIso_iff_bijective _).mp (hr d)).injective
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
    · ext x
      have he := congrArg ((stableHomotopyFunctor d).map) sq.w
      rw [Functor.map_comp, Functor.map_comp] at he
      exact ConcreteCategory.congr_hom he x
  intro d
  have h := hshift (d - 1)
  rw [show d - 1 + 1 = d by omega] at h
  exact h

end Topology.LoopPrespectrum
