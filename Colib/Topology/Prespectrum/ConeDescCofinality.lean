/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeDescZeroComparison


/-!
# Original cone descent from cofinality and the honest zero-degree comparison

An actual arrow with genuine cone-fiber excision, injective signed stable maps and
surjective nonzero-degree stable maps has a cone concentrated in degree zero. A specified
cone descent to another such concentrated object is stable once its actual degree-zero map
is bijective. The original cylinder and signed boundary are retained; zero-degree
surjectivity of the original arrow is not assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}} (r : E ⟶ F) (q : F ⟶ G)
    (N : Homotopy (r ≫ q) (zeroHom E G))

/-- Actual signed excision and cofinality identify the same specified cone descent. -/
@[colib_ref "quillen" "Quillen/Topology/Prespectrum/ConeDescCofinality.lean:28"
  "adaptation" "Original actual all-signed cone descent from cofinality and honest K-zero"]
theorem mappingConeDesc_isStableEquivalence_of_cofinality
    (he : IsStableEquivalence (mappingConeFiberComparison r))
    (hi : ∀ d : ℤ, Function.Injective ((stableHomotopyFunctor d).map r))
    (hs : ∀ d : ℤ, d ≠ 0 → Function.Surjective ((stableHomotopyFunctor d).map r))
    (hg : ∀ d : ℤ, d ≠ 0 → Subsingleton (stableHomotopyGroup G d))
    (hzero : Function.Bijective ((stableHomotopyFunctor 0).map (mappingConeDesc r q N))) :
    IsStableEquivalence (mappingConeDesc r q N) := by
  intro d
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  by_cases hd : d = 0
  · subst d
    exact hzero
  · have hcone : ∀ x : stableHomotopyGroup (mappingCone r) (d - 1 + 1), x = 0 := by
      intro x
      have hb : stableMappingConeConnecting r he (d - 1) x = 0 :=
        hi (d - 1)
          (((stableMappingConeConnecting_exact_source r he (d - 1) _).mpr ⟨x, rfl⟩).trans
            (map_zero ((stableHomotopyFunctor (d - 1)).map r).hom).symm)
      obtain ⟨y, hy⟩ := (stableMappingConeConnecting_exact_cone r he (d - 1) x).mp hb
      obtain ⟨z, rfl⟩ := hs (d - 1 + 1) (by omega) y
      exact hy.symm.trans ((stableMappingCone_exact_target r he (d - 1 + 1) _).mpr ⟨z, rfl⟩)
    have hc : Subsingleton (stableHomotopyGroup (mappingCone r) (d - 1 + 1)) :=
      ⟨fun x y ↦ (hcone x).trans (hcone y).symm⟩
    have hc' : Subsingleton (stableHomotopyGroup (mappingCone r) d) :=
      Eq.mp (congrArg (fun k : ℤ ↦ Subsingleton (stableHomotopyGroup (mappingCone r) k))
        (sub_add_cancel d 1)) hc
    constructor
    · intro x y _
      exact hc'.elim x y
    · intro y
      exact ⟨0, (hg d hd).elim _ _⟩

end Topology.LoopPrespectrum
