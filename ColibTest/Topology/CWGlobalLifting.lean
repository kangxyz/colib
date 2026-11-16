module

public import Colib.Topology.CWComplex.GlobalLifting

open Set Topology Topology.CWComplex
open scoped Topology

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C] {E : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
  (hp : CubicalSubdivision.BoundaryLifting p) (f : C(C, B))

example : ∃ g : C(C, E), p.comp g = f :=
  exists_globalLift C p hp f

example (n : ℕ) (x : SkeletonLT C n) :
    globalLift C p hp f (skeletonToComplex C n x) =
      (skeletonLiftFamily C p hp f n).val x :=
  globalLift_on_skeleton C p hp f n x

example (x : C) : p (globalLift C p hp f x) = f x :=
  ContinuousMap.congr_fun (globalLift_comp C p hp f) x

#print axioms exists_globalLift
#print axioms globalLift_on_skeleton
