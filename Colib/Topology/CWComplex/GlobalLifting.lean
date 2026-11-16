/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.SkeletonLifting

/-!
# Actual global lifting from a classical CW complex

A strict cubical boundary-lifting map lifts every continuous map from the
original Hausdorff classical-CW subtype. The function is assembled from the
constructed finite-stage lifts, whose compatibility proves independence of
which containing skeleton is used. Its continuity follows on each original
characteristic disk and then from the actual characteristic quotient.

This is global map lifting only. No cylinder lifting, prescribed-endpoint
homotopy, Whitehead conclusion, singular counit comparison, realization
domination or cover-existence theorem is assumed or asserted here.

Adapted from `Quillen/Topology/CWComplex/GlobalLifting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open Topology
noncomputable section
open Set
universe u v w
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
variable (p : C(E, B)) (hp : CubicalSubdivision.BoundaryLifting p) (f : C(C, B))

/-- Each point of the original CW subtype belongs to an actual finite skeleton. -/
theorem exists_containing_skeleton (x : C) :
    ∃ n : ℕ, x.val ∈ (CWComplex.skeletonLT C n : Set X) := by
  have hx : x.val ∈ ⋃ n : ℕ, (CWComplex.skeletonLT C n : Set X) := by
    simpa only [CWComplex.iUnion_skeletonLT_eq_complex] using x.property
  exact Set.mem_iUnion.mp hx

/-- A containing skeleton is chosen only to define the underlying global function. -/
def pointSkeleton (x : C) : ℕ := Classical.choose (exists_containing_skeleton C x)

/-- The unchanged original point in its chosen containing skeleton. -/
def pointInSkeleton (x : C) : SkeletonLT C (pointSkeleton C x) :=
  ⟨x.val, Classical.choose_spec (exists_containing_skeleton C x)⟩

/-- The assembled function uses the actual finite-stage maps. -/
def globalLiftFun (x : C) : E :=
  (skeletonLiftFamily C p hp f (pointSkeleton C x)).val (pointInSkeleton C x)

/-- The assembled function agrees with every finite stage, independently of
its chosen containing skeleton. Both comparison points lie in a common maximum stage. -/
theorem globalLiftFun_on_skeleton (n : ℕ) (x : SkeletonLT C n) :
    globalLiftFun C p hp f (skeletonToComplex C n x) =
      (skeletonLiftFamily C p hp f n).val x := by
  let y := skeletonToComplex C n x
  let m := pointSkeleton C y
  let z := pointInSkeleton C y
  have hleft := skeletonLiftFamily_compatible C p hp f (Nat.le_max_left m n) z
  have hright := skeletonLiftFamily_compatible C p hp f (Nat.le_max_right m n) x
  have he : skeletonInclusionLE C (Nat.le_max_left m n) z =
      skeletonInclusionLE C (Nat.le_max_right m n) x := Subtype.ext rfl
  exact hleft.symm.trans ((congrArg (skeletonLiftFamily C p hp f (max m n)).val he).trans hright)

/-- The original base-map equation is pointwise, not merely up to homotopy. -/
theorem globalLiftFun_over (x : C) : p (globalLiftFun C p hp f x) = f x :=
  (skeletonLiftFamily C p hp f (pointSkeleton C x)).property (pointInSkeleton C x)

/-- Every original characteristic disk sees its stored continuous finite-stage
map, so the actual characteristic quotient proves global continuity. -/
theorem continuous_globalLiftFun : Continuous (globalLiftFun C p hp f) := by
  apply (continuous_iff_characteristic C (globalLiftFun C p hp f)).mpr
  intro n i
  have he : (fun z : CharacteristicDisk n ↦
      globalLiftFun C p hp f (characteristicQuotient C ⟨n, i, z⟩)) =
      (skeletonLiftFamily C p hp f (n + 1)).val ∘ skeletonCharacteristicMap C n i := by
    funext z
    exact globalLiftFun_on_skeleton C p hp f (n + 1) (skeletonCharacteristicMap C n i z)
  rw [he]
  exact (skeletonLiftFamily C p hp f (n + 1)).val.continuous.comp
    (skeletonCharacteristicMap C n i).continuous

/-- An actual continuous global lift on the original CW subtype. -/
def globalLift : C(C, E) := ⟨globalLiftFun C p hp f, continuous_globalLiftFun C p hp f⟩

/-- The constructed continuous map strictly lifts the original base map. -/
theorem globalLift_comp : p.comp (globalLift C p hp f) = f := by
  ext x
  exact globalLiftFun_over C p hp f x

/-- Every constructed finite skeleton is retained pointwise by the global map. -/
theorem globalLift_on_skeleton (n : ℕ) (x : SkeletonLT C n) :
    globalLift C p hp f (skeletonToComplex C n x) =
      (skeletonLiftFamily C p hp f n).val x :=
  globalLiftFun_on_skeleton C p hp f n x

include hp in
/-- Global CW lifting follows from genuine boundary lifting without a supplied
realization model, domination, endpoint homotopy or covering-space hypothesis. -/
theorem exists_globalLift : ∃ g : C(C, E), p.comp g = f :=
  ⟨globalLift C p hp f, globalLift_comp C p hp f⟩

end Topology.CWComplex
