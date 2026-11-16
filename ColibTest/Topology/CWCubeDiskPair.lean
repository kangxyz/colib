module

public import Colib.Topology.CWComplex.CubeDiskPair

open Topology Topology.CWComplex
open scoped Topology

universe u v

example (n : ℕ) (t : CubicalSubdivision.Boundary n) :
    characteristicSphereInclusion n (cubeBoundarySphereHomeomorph n t) =
      cubeDiskHomeomorph n t.val :=
  cubeBoundarySphereHomeomorph_inclusion n t

example : IsEmpty (CharacteristicSphere 0) :=
  characteristicSphere_zero_isEmpty

example {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : CubicalSubdivision.BoundaryLifting p) (n : ℕ)
    (a : C(CharacteristicSphere n, E)) (b : C(CharacteristicDisk n, B))
    (hab : ∀ z, p (a z) = b (characteristicSphereInclusion n z)) :
    ∃ c : C(CharacteristicDisk n, E),
      (∀ z, c (characteristicSphereInclusion n z) = a z) ∧ p.comp c = b :=
  hp.characteristicDisk n a b hab

#print axioms cubeDiskHomeomorph_mem_sphere_iff
#print axioms CubicalSubdivision.BoundaryLifting.characteristicDisk
