module

public import Colib.Topology.CWComplex.SkeletonExtension

open Set Topology Topology.CWComplex
open scoped Topology

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] (n : ℕ) {Y : Type v} [TopologicalSpace Y]
  (a : C(SkeletonLT C n, Y))
  (b : ∀ _ : RelCWComplex.cell C n, C(CharacteristicDisk n, Y))
  (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
    a (characteristicBoundaryMap C n i t))

example : ∃! f : C(SkeletonLT C (n + 1), Y),
    (∀ x, f (skeletonInclusion C n x) = a x) ∧
    (∀ i z, f (skeletonCharacteristicMap C n i z) = b i z) := by
  refine ⟨skeletonStepExtension C n a b hab,
    ⟨skeletonStepExtension_old C n a b hab, skeletonStepExtension_disk C n a b hab⟩,
    ?_⟩
  intro f hf
  exact skeletonStepExtension_unique C n a b hab f hf.1 hf.2

#print axioms skeletonStepExtension
#print axioms skeletonStepExtension_unique
