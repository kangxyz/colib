/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Prespectrum.ConeStableCokernel

/-!
# The original cone descent on degree zero

A genuine degree-zero cokernel sequence identifies the actual cone descent, with its supplied
nullhomotopy, as a bijection on stable degree zero. Neither the spectrum map nor its cylinder
is replaced by an abstract cokernel comparison.
-/

/-! Implementation provenance: `Quillen/Topology/Prespectrum/ConeDescZeroComparison.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, endpoint casts, complete homotopies and hypotheses are retained
under their native mathematical owners. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum
variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F) (g : F ⟶ G)
  (N : Homotopy (f ≫ g) (zeroHom E G))
  (hf : IsStableEquivalence (mappingConeFiberComparison f))
  [Subsingleton (stableHomotopyGroup E (-1))]

include hf in
/-- Exactness and surjectivity of the unchanged target map identify the actual cone descent. -/
theorem mappingConeDesc_stable_zero_bijective
    (he : Function.Exact ((stableHomotopyFunctor 0).map f)
      ((stableHomotopyFunctor 0).map g))
    (hg : Function.Surjective ((stableHomotopyFunctor 0).map g)) :
    Function.Bijective ((stableHomotopyFunctor 0).map (mappingConeDesc f g N)) := by
  have hcomp : (stableHomotopyFunctor 0).map (mappingConeInclusion f) ≫
      (stableHomotopyFunctor 0).map (mappingConeDesc f g N) =
        (stableHomotopyFunctor 0).map g := by
    rw [← Functor.map_comp, mappingConeInclusion_desc]
  have hi := stableMappingConeInclusion_zero_surjective f hf
  constructor
  · intro x y hxy
    have hz : (stableHomotopyFunctor 0).map (mappingConeDesc f g N) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hzx⟩ := hi (x - y)
    have hgz : (stableHomotopyFunctor 0).map g z = 0 :=
      (ConcreteCategory.congr_hom hcomp z).symm.trans
        ((congrArg ((stableHomotopyFunctor 0).map (mappingConeDesc f g N)) hzx).trans hz)
    obtain ⟨a, ha⟩ := (he z).mp hgz
    have hzi := (stableMappingCone_exact_target f hf 0 z).mpr ⟨a, ha⟩
    exact sub_eq_zero.mp (hzx.symm.trans hzi)
  · intro y
    obtain ⟨x, hx⟩ := hg y
    exact ⟨(stableHomotopyFunctor 0).map (mappingConeInclusion f) x,
      (ConcreteCategory.congr_hom hcomp x).trans hx⟩

end Topology.LoopPrespectrum
