module

public import Colib.Topology.CWComplex.SkeletonNeighborhoodDeformation

open Set Topology Topology.CWComplex
open scoped Topology unitInterval

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (n : ℕ)
  (U : Set (SkeletonLT C n)) (hU : IsOpen U)

example :
    ∃ H : (ContinuousMap.id (stepNeighborhood C n U)).Homotopy
        ((stepNeighborhoodInclusion C n U hU).comp (stepNeighborhoodRetraction C n U hU)),
      ∀ (t : I) (x : U),
        H (t, stepNeighborhoodInclusion C n U hU x) =
          stepNeighborhoodInclusion C n U hU x :=
  ⟨stepNeighborhoodDeformation C n U hU, stepNeighborhoodDeformation_fixed C n U hU⟩

example (x : U) :
    stepNeighborhoodRetraction C n U hU (stepNeighborhoodInclusion C n U hU x) = x :=
  stepNeighborhoodRetraction_old C n U hU x

example (t : I) (i : RelCWComplex.cell C n)
    (z : RadialCollar n (stepCollarDirections C n U i)) :
    stepNeighborhoodDeformation C n U hU (t, stepNeighborhoodCollarMap C n U hU i z) =
      stepNeighborhoodCollarMap C n U hU i
        (collarRadialMap n (stepCollarDirections C n U i) (t, z)) :=
  stepNeighborhoodDeformationFun_collar C n U hU t i z

#print axioms stepNeighborhoodDeformation
#print axioms stepNeighborhoodDeformation_fixed
