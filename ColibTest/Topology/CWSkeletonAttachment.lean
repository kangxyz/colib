module

public import Colib.Topology.CWComplex.SkeletonAttachment

open Set Topology Topology.CWComplex

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

example (n : ℕ) : IsQuotientMap (skeletonStepMap C n) :=
  isQuotientMap_skeletonStepMap C n

example (n : ℕ) (i : RelCWComplex.cell C n) (z : CharacteristicSphere n) :
    skeletonCharacteristicMap C n i (characteristicSphereInclusion n z) =
      skeletonInclusion C n (characteristicBoundaryMap C n i z) :=
  skeletonCharacteristicMap_boundary C n i z

example : IsEmpty (SkeletonLT C 0) :=
  skeletonLT_zero_isEmpty C

#print axioms isQuotientMap_skeletonStepMap
#print axioms characteristic_mem_previous_iff
