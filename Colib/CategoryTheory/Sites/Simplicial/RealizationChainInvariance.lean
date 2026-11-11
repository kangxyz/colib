/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ReducedSimplicialChainsWeak
public import Colib.Topology.Realization.SingularChainComparison.Skeletal
public import Colib.Topology.Realization.WeakHomotopyEquiv

/-!
# Realization invariance of pointed simplicial chains

A realization weak equivalence has an actual topological homotopy inverse,
so its original realized map induces a quasi-isomorphism on singular chains.
Naturality of the realization comparison transfers this to simplicial chains,
and the absolute-to-reduced comparison gives the pointed-chain implication.

The skeletal comparison proves that the actual adjunction unit induces an
integral quasi-isomorphism for every simplicial set, discharging the comparison
premise.
-/

@[expose] public section

open AlgebraicTopology CategoryTheory

universe w

namespace CategoryTheory.PointedSimplicialPresheaf

/-- The integral unit comparison alone supplies realization invariance for the
actual pointed reduced normalized chains. The comparison premise is explicit. -/
theorem pointedSimplicialSetChainsPreserveRealizationWeakEquivalences_of_realizationChainComparison
    (hunit : ∀ X : SSet.{w},
      QuasiIso (SSet.realizationChainComparison X (ModuleCat.of ℤ (ULift.{w} ℤ)))) :
    PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w} := by
  apply pointedSimplicialSetChainsPreserveRealizationWeakEquivalences_of_integralChainComplexMap
  intro X Y f hf
  let R := ModuleCat.of ℤ (ULift.{w} ℤ)
  let : QuasiIso (SSet.realizationChainComparison X R) := hunit X
  let : QuasiIso (SSet.realizationChainComparison Y R) := hunit Y
  let : QuasiIso (((singularChainComplexFunctor (ModuleCat.{w} ℤ)).obj R).map
      (SSet.toTop.map f)) := by
    simpa only [SSet.IsRealizationWeakEquivalence.homotopyEquiv_toFun, TopCat.ofHom_hom] using
      SSet.quasiIso_singular_of_homotopyEquiv
        (X := SSet.toTop.obj X) (Y := SSet.toTop.obj Y) hf.homotopyEquiv R
  exact SSet.quasiIso_chainComplexMap_of_realizationChainComparison f R

/-- Actual pointed reduced normalized chains preserve realization weak equivalences. -/
theorem pointedSimplicialSetChainsPreserveRealizationWeakEquivalences :
    PointedSimplicialSetChainsPreserveRealizationWeakEquivalences.{w} :=
  pointedSimplicialSetChainsPreserveRealizationWeakEquivalences_of_realizationChainComparison
    (fun X ↦ SSet.quasiIso_realizationChainComparison X _)

attribute [colib_tag "COL-1013"]
  pointedSimplicialSetChainsPreserveRealizationWeakEquivalences

end CategoryTheory.PointedSimplicialPresheaf
