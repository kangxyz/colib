/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.Subtype
public import Colib.Topology.CWComplex.ULift

/-!
# Actual classical CW structure on the universe-lifted complex subtype

The intrinsic subtype structure and the literal universe lift combine to give
a CW structure on all of `ULift C`. The original characteristic maps are
preserved on their full closed disks after applying `down` and subtype inclusion.
The supplied point only determines irrelevant chart values outside those disks.

Adapted from `Quillen/Topology/CWComplex/UniverseTransport.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

open Topology
noncomputable section
open Set Metric
universe u v
namespace Topology.CWComplex
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (c : C)

/-- The actual original CW subtype, lifted to a larger universe, has a classical
CW structure on its entire underlying type. -/
@[instance_reducible]
def uliftSubtypeCWComplex : CWComplex (univ : Set (ULift.{v} C)) := by
  letI := subtypeCWComplex C c
  exact uliftUnivCWComplex

/-- Every original characteristic source is still the literal open unit ball. -/
theorem uliftSubtypeCWComplex_source (n : ℕ) (i : RelCWComplex.cell C n) :
    ((uliftSubtypeCWComplex.{u, v} C c).map n (ULift.up i)).source =
      ball (0 : Fin n → ℝ) 1 := rfl

/-- Original closed-disk values are unchanged by both geometric transports. -/
theorem uliftSubtypeCWComplex_map_val (n : ℕ) (i : RelCWComplex.cell C n)
    (z : Fin n → ℝ) (hz : z ∈ closedBall (0 : Fin n → ℝ) 1) :
    ((uliftSubtypeCWComplex.{u, v} C c).map n (ULift.up i) z).down.val =
      RelCWComplex.map n i z := subtypeCharacteristicMap_val C c n i z hz

/-- The inverse chart remains the original inverse chart after the literal projections. -/
theorem uliftSubtypeCWComplex_map_symm (n : ℕ) (i : RelCWComplex.cell C n)
    (y : ULift.{v} C) :
    ((uliftSubtypeCWComplex.{u, v} C c).map n (ULift.up i)).symm y =
      (RelCWComplex.map n i).symm y.down.val := rfl

end Topology.CWComplex
