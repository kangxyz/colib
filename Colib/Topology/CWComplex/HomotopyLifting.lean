/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.GlobalLifting
public import Colib.Topology.HomotopyPullback.PathProjectionLifting

/-!
# Prescribed-endpoint lifting over an actual classical CW subtype

The generic endpoint-constrained compact-open path projection has genuine
boundary lifting by the full finite cylinder boundary argument. Apply actual
global CW lifting to that projection, then uncurry. Both original endpoints and
the entire prescribed base homotopy are retained; continuity is joint in time
and the original CW parameter. No CW structure on a product is assumed.

Adapted from `Quillen/Topology/CWComplex/HomotopyLifting.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

open Topology

noncomputable section
open Set
open scoped unitInterval
universe u v
namespace Topology.CWComplex
open HomotopyPullback
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]
variable {E B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable (p : C(E, B)) (hp : CubicalSubdivision.BoundaryLifting p)

/-- Lift the entire original base homotopy with both prescribed endpoint maps,
using global lifting for the actual endpoint-constrained path projection. -/
def homotopyLift (a₀ a₁ : C(C, E))
    (H : (p.comp a₀).Homotopy (p.comp a₁)) : a₀.Homotopy a₁ :=
  homotopyOfPathProjectionLift p a₀ a₁ H
    (globalLift C (pathProjection p) hp.pathProjection (homotopyTarget p a₀ a₁ H))
    (globalLift_comp C (pathProjection p) hp.pathProjection (homotopyTarget p a₀ a₁ H))

/-- Every point of the lifted homotopy projects to the prescribed original track. -/
theorem homotopyLift_project (a₀ a₁ : C(C, E))
    (H : (p.comp a₀).Homotopy (p.comp a₁)) (t : I) (x : C) :
    p (homotopyLift C p hp a₀ a₁ H (t, x)) = H (t, x) :=
  homotopyOfPathProjectionLift_project p a₀ a₁ H _ _ t x

/-- The zero endpoint is exactly the prescribed first map. -/
theorem homotopyLift_zero (a₀ a₁ : C(C, E))
    (H : (p.comp a₀).Homotopy (p.comp a₁)) (x : C) :
    homotopyLift C p hp a₀ a₁ H (0, x) = a₀ x :=
  (homotopyLift C p hp a₀ a₁ H).map_zero_left x

/-- The one endpoint is exactly the prescribed second map. -/
theorem homotopyLift_one (a₀ a₁ : C(C, E))
    (H : (p.comp a₀).Homotopy (p.comp a₁)) (x : C) :
    homotopyLift C p hp a₀ a₁ H (1, x) = a₁ x :=
  (homotopyLift C p hp a₀ a₁ H).map_one_left x

end Topology.CWComplex
