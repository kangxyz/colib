module

public import Colib.Topology.CWComplex.SkeletonLifting

open Set Topology Topology.CWComplex
open scoped Topology

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] {E : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
  (hp : CubicalSubdivision.BoundaryLifting p) (f : C(C, B))

example (n : ℕ) (a : C(SkeletonLT C n, E)) (d : C(SkeletonLT C (n + 1), B))
    (ha : ∀ x, p (a x) = d (skeletonInclusion C n x)) :
    ∃ c : C(SkeletonLT C (n + 1), E),
      (∀ x, c (skeletonInclusion C n x) = a x) ∧ p.comp c = d :=
  exists_skeletonStepLift C p hp n a d ha

example {n m : ℕ} (h : n ≤ m) (x : SkeletonLT C n) :
    (skeletonLiftFamily C p hp f m).val (skeletonInclusionLE C h x) =
      (skeletonLiftFamily C p hp f n).val x :=
  skeletonLiftFamily_compatible C p hp f h x

example (n : ℕ) (x : SkeletonLT C n) :
    p ((skeletonLiftFamily C p hp f n).val x) = f (skeletonToComplex C n x) :=
  (skeletonLiftFamily C p hp f n).property x

#print axioms skeletonLiftFamily
#print axioms skeletonLiftFamily_compatible
