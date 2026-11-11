/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeStableExactness

/-!
# Stable equivalence from vanishing of the original cone

For an actual prespectrum arrow with genuine cone-to-fiber excision, vanishing of all signed
stable groups of its original cone makes that unchanged arrow a stable equivalence. The proof
uses the original cone exact sequence in adjacent degrees; it assumes no uniform connectivity.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Genuine cone excision and signed cone vanishing detect stability of the original arrow. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ConeStableVanishing.lean:24"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
theorem isStableEquivalence_of_cone_stableGroup_subsingleton
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hf : IsStableEquivalence (mappingConeFiberComparison f))
    (hcone : ∀ d : ℤ, Subsingleton (stableHomotopyGroup (mappingCone f) d)) :
    IsStableEquivalence f := by
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply (injective_iff_map_eq_zero ((stableHomotopyFunctor d).map f).hom).mpr
    intro x hx
    obtain ⟨y, hy⟩ := (stableMappingConeConnecting_exact_source f hf d x).mp hx
    have hy0 : y = 0 := (hcone (d + 1)).elim _ _
    rw [hy0, map_zero] at hy
    exact hy.symm
  · intro y
    exact (stableMappingCone_exact_target f hf d y).mp ((hcone d).elim _ _)

end Topology.LoopPrespectrum
