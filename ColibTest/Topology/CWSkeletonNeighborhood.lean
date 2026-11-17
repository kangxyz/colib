module

public import Colib.Topology.CWComplex.SkeletonNeighborhood

open Set Topology Topology.CWComplex

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (n : ℕ)

example (U : Set (SkeletonLT C n)) (hU : IsOpen U) :
    IsOpen (stepNeighborhood C n U) ∧ IsQuotientMap (stepNeighborhoodMap C n U) :=
  ⟨isOpen_stepNeighborhood C n hU, isQuotientMap_stepNeighborhoodMap C n hU⟩

example (U : Set (SkeletonLT C n)) (x : SkeletonLT C n) :
    skeletonInclusion C n x ∈ stepNeighborhood C n U ↔ x ∈ U :=
  skeletonInclusion_mem_stepNeighborhood C n U x

example (U : Set (SkeletonLT C n)) :
    (skeletonStepMap C n) ⁻¹' stepNeighborhood C n U = stepNeighborhoodSource C n U :=
  preimage_stepNeighborhood C n U

#print axioms isQuotientMap_stepNeighborhoodMap
#print axioms skeletonInclusion_mem_stepNeighborhood
