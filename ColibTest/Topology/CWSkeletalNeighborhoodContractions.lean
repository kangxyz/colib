module

public import Colib.Topology.CWComplex.SkeletalNeighborhoodContractions

open Set Topology Topology.CWComplex
open scoped Topology unitInterval

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (n : ℕ) (i : RelCWComplex.cell C n)
  (x : CellNeighborhood C n i)

example (k : ℕ) : IsOpen (skeletalNeighborhood C n i k) :=
  isOpen_skeletalNeighborhood C n i k

example (k : ℕ) (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (1, y) =
      cellNeighborhoodToComplex C n i x :=
  skeletalNeighborhoodContraction_one C n i x k y

example {k l : ℕ} (h : k ≤ l) (t : I) (y : SkeletalNeighborhood C n i k) :
    (skeletalNeighborhoodContraction C n i x l).toHomotopy
      (t, skeletalNeighborhoodInclusion C n i h y) =
        (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) :=
  skeletalNeighborhoodContraction_restrict C n i x h t y

example {k l : ℕ} (y : SkeletalNeighborhood C n i k) (z : SkeletalNeighborhood C n i l)
    (h : skeletalNeighborhoodToComplex C n i k y = skeletalNeighborhoodToComplex C n i l z)
    (t : I) :
    (skeletalNeighborhoodContraction C n i x k).toHomotopy (t, y) =
      (skeletalNeighborhoodContraction C n i x l).toHomotopy (t, z) :=
  skeletalNeighborhoodContraction_eq_of_toComplex_eq C n i x y z h t

#print axioms skeletalNeighborhoodContraction
#print axioms skeletalNeighborhoodContraction_restrict
