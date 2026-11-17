module

public import Colib.Topology.CWComplex.NeighborhoodContraction

open Set Topology Topology.CWComplex
open scoped Topology unitInterval

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n)

example : IsOpen (neighborhoodSet C n i) :=
  isOpen_neighborhoodSet C n i

example (x : CellNeighborhood C n i) :
    cellNeighborhoodToComplex C n i x ∈ neighborhoodSet C n i :=
  seed_mem_neighborhoodSet C n i x

example (x : CellNeighborhood C n i) :
    ∃ H : (neighborhoodToComplex C n i).Homotopy
        (ContinuousMap.const (Neighborhood C n i) (cellNeighborhoodToComplex C n i x)),
      ∀ (k : ℕ) (t : I) (y : SkeletalNeighborhood C n i k),
        H (t, neighborhoodStageInclusion C n i k y) =
          (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) :=
  ⟨neighborhoodAmbientContraction C n i x, neighborhoodAmbientContraction_stage C n i x⟩

#print axioms neighborhoodAmbientContraction
#print axioms isOpen_neighborhoodSet
