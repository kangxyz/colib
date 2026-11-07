/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.ConeStableExactness
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# The original degree-zero cone cokernel

Genuine cone-to-fiber excision and vanishing of the original source in degree minus one identify
the actual degree-zero cone group as the cokernel of the unchanged stable map. The comparison
retains the original cone inclusion on every representative.
-/

/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeStableCokernel.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, endpoint casts, complete homotopies and hypotheses are retained
under their native mathematical owners. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (hf : IsStableEquivalence (mappingConeFiberComparison f))
  [Subsingleton (stableHomotopyGroup E (-1))]

include hf in
/-- The actual cone inclusion is surjective in degree zero when the original source has no
negative degree-minus-one classes. -/
theorem stableMappingConeInclusion_zero_surjective :
    Function.Surjective ((stableHomotopyFunctor 0).map (mappingConeInclusion f)) := by
  intro y
  have h := stableMappingConeConnecting_exact_cone f hf (-1)
  exact (h y).mp (Subsingleton.elim _ _)

/-- The original target and cone maps form a degree-zero short complex. -/
def stableMappingConeZeroShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk ((stableHomotopyFunctor 0).map f)
    ((stableHomotopyFunctor 0).map (mappingConeInclusion f)) (by
      ext x
      exact (stableMappingCone_exact_target f hf 0 _).mpr ⟨x, rfl⟩)

/-- The original stable cone sequence supplies the actual cokernel universal property. -/
def stableMappingConeZeroIsCokernel :
    IsColimit (CokernelCofork.ofπ ((stableHomotopyFunctor 0).map (mappingConeInclusion f))
      (stableMappingConeZeroShortComplex f hf).zero) := by
  have : Epi ((stableMappingConeZeroShortComplex f hf).g) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (stableMappingConeInclusion_zero_surjective f hf)
  have he : (stableMappingConeZeroShortComplex f hf).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro y hy
    exact (stableMappingCone_exact_target f hf 0 y).mp hy
  exact he.gIsCokernel

/-- The canonical cokernel isomorphism uses the original cone inclusion as its forward map. -/
def stableMappingConeZeroCokernelIso :
    cokernel ((stableHomotopyFunctor 0).map f) ≅ stableHomotopyGroup (mappingCone f) 0 :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (stableMappingConeZeroIsCokernel f hf)

/-- Every original target representative maps through the unchanged cone inclusion. -/
@[reassoc]
theorem stableMappingConeZeroCokernelIso_π :
    cokernel.π ((stableHomotopyFunctor 0).map f) ≫
      (stableMappingConeZeroCokernelIso f hf).hom =
        (stableHomotopyFunctor 0).map (mappingConeInclusion f) :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom
    (stableMappingConeZeroIsCokernel f hf) WalkingParallelPair.one

end Topology.LoopPrespectrum

namespace Topology.LoopPrespectrum
variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (hf : IsStableEquivalence (mappingConeFiberComparison f)) (d : ℤ)
  [Subsingleton (stableHomotopyGroup E (d - 1))]

include hf in
/-- The original inclusion is surjective in signed degree d when its actual boundary group
in degree d minus one vanishes. -/
theorem stableMappingConeInclusion_degree_surjective :
    Function.Surjective ((stableHomotopyFunctor d).map (mappingConeInclusion f)) := by
  have h : Function.Surjective
      ((stableHomotopyFunctor (d - 1 + 1)).map (mappingConeInclusion f)) := by
    intro y
    exact (stableMappingConeConnecting_exact_cone f hf (d - 1) y).mp
      (Subsingleton.elim _ _)
  exact Eq.mp (congrArg
    (fun k : ℤ ↦ Function.Surjective ((stableHomotopyFunctor k).map (mappingConeInclusion f)))
      (sub_add_cancel d 1)) h

/-- The unchanged arrow and cone inclusion form the original signed-degree short complex. -/
def stableMappingConeDegreeShortComplex : ShortComplex AddCommGrpCat :=
  ShortComplex.mk ((stableHomotopyFunctor d).map f)
    ((stableHomotopyFunctor d).map (mappingConeInclusion f)) (by
      ext x
      exact (stableMappingCone_exact_target f hf d _).mpr ⟨x, rfl⟩)

/-- Actual signed cone exactness and the proved vanishing give the original cokernel property. -/
def stableMappingConeDegreeIsCokernel :
    IsColimit (CokernelCofork.ofπ ((stableHomotopyFunctor d).map (mappingConeInclusion f))
      (stableMappingConeDegreeShortComplex f hf d).zero) := by
  have : Epi ((stableMappingConeDegreeShortComplex f hf d).g) :=
    (AddCommGrpCat.epi_iff_surjective _).mpr
      (stableMappingConeInclusion_degree_surjective f hf d)
  have he : (stableMappingConeDegreeShortComplex f hf d).Exact := by
    rw [ShortComplex.ab_exact_iff]
    intro y hy
    exact (stableMappingCone_exact_target f hf d y).mp hy
  exact he.gIsCokernel

/-- The actual signed-degree cone group is the cokernel of the unchanged original stable map. -/
def stableMappingConeDegreeCokernelIso :
    cokernel ((stableHomotopyFunctor d).map f) ≅ stableHomotopyGroup (mappingCone f) d :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (stableMappingConeDegreeIsCokernel f hf d)

/-- Every original target representative is retained in arbitrary signed degree. -/
@[reassoc]
theorem stableMappingConeDegreeCokernelIso_π :
    cokernel.π ((stableHomotopyFunctor d).map f) ≫
      (stableMappingConeDegreeCokernelIso f hf d).hom =
        (stableHomotopyFunctor d).map (mappingConeInclusion f) :=
  (cokernelIsCokernel _).comp_coconePointUniqueUpToIso_hom
    (stableMappingConeDegreeIsCokernel f hf d) WalkingParallelPair.one

end Topology.LoopPrespectrum
