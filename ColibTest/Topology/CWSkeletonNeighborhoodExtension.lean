module

public import Colib.Topology.CWComplex.SkeletonNeighborhoodExtension

open Set Topology Topology.CWComplex
open scoped Topology

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (n : ℕ)
  (U : Set (SkeletonLT C n)) (hU : IsOpen U)
  {Y : Type v} [TopologicalSpace Y] (a : C(U, Y))
  (b : ∀ i : RelCWComplex.cell C n, C(RadialCollar n (stepCollarDirections C n U i), Y))
  (hab : ∀ i z, b i (stepCollarBoundaryPoint C n U i z) = a (stepOldBoundaryPoint C n U i z))

example (i : RelCWComplex.cell C n) (z : stepCollarDirections C n U i) :
    stepNeighborhoodMap C n U (Sum.inr ⟨i, stepCollarBoundaryPoint C n U i z⟩) =
      stepNeighborhoodMap C n U (Sum.inl (stepOldBoundaryPoint C n U i z)) :=
  stepNeighborhoodMap_boundary C n U i z

example : ∃ f : C(stepNeighborhood C n U, Y),
    (∀ x : U, f (stepNeighborhoodMap C n U (Sum.inl x)) = a x) ∧
    (∀ (i : RelCWComplex.cell C n) (z : RadialCollar n (stepCollarDirections C n U i)),
      f (stepNeighborhoodMap C n U (Sum.inr ⟨i, z⟩)) = b i z) :=
  ⟨stepNeighborhoodExtension C n U a b hU hab,
    stepNeighborhoodExtension_old C n U a b hU hab,
    stepNeighborhoodExtension_collar C n U a b hU hab⟩

#print axioms stepNeighborhoodExtension
#print axioms stepNeighborhoodData_fiberwise
