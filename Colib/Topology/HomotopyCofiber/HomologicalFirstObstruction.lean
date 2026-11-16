/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyCofiber.UnreducedFirstObstruction
public import Colib.Topology.HomotopyCofiber.UnreducedConeHomology
public import Colib.Topology.LocalCoefficients.FirstObstruction
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.FiberObstructionStep

/-!
# The actual relative first obstruction detected by integral cone homology

The cone's lower homotopy groups vanish by the proved finite excision bridge.
Absolute first-obstruction detection then kills its next group; the literal
path-retaining cone comparison kills the corresponding original fiber group.
A constant-integral-chain quasi-isomorphism supplies the required cone homology
vanishing through the actual collar Mayer--Vietoris theorem.

The genuine frozen FirstObstruction theorem is applied directly; no
homology-to-homotopy certificate is introduced.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyCofiber/HomologicalFirstObstruction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual cone, stored paths, and
signed integral-coefficient comparison are retained. -/
@[expose] public section

open FundamentalGroupoid.LocalCoefficients

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
open scoped Topology
universe u

namespace Topology.ReducedMappingCone
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
variable (f : C(X, Y))

/-- Zero actual integral cone homology kills the first possible original
relative obstruction, including the fiber fundamental group at m=0. -/
theorem subsingleton_firstObstruction_of_cone_homology
    (x : X) (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1))
    (hH : IsZero (homology (constant (UnreducedSpace f) integralCoefficients.{u})
      (m + 2))) :
    Subsingleton (HomotopyGroup.Pi (m + 1) (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl)) := by
  let : PathConnectedSpace (UnreducedSpace f) :=
    TopCat.DoubleCylinder.pathConnectedSpace (TopCat.ofHom f)
      (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))
      (unreducedSquare f) x
  have hcone : Subsingleton (HomotopyGroup.Pi (m + 2)
      (UnreducedSpace f) (unreducedVertex f)) :=
    subsingleton_pi_of_homology_isZero m (unreducedVertex f)
      (fun z k _ hk ↦ unreducedCone_subsingleton_below_first f x m hf z k hk) hH
  exact subsingleton_firstObstruction_of_cone f x m hf hcone

/-- An actual constant-integral-chain quasi-isomorphism kills the next fiber
obstruction by its actual cone, not by an assumed relative Hurewicz map. -/
theorem subsingleton_firstObstruction_of_integral_quasiIso
    (x : X) (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1))
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficients.{u}))) :
    Subsingleton (HomotopyGroup.Pi (m + 1) (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl)) :=
  subsingleton_firstObstruction_of_cone_homology f x m hf
    (unreducedCone_positive_homology_isZero_of_quasiIso f integralCoefficients.{u}
      hH (m + 1))

/-- The first-obstruction argument raises the connectivity of the original
map, retaining its actual fibers and all of their basepoints. -/
theorem isHomotopyConnectedMap_succ_of_integral_quasiIso
    (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1))
    (hH : QuasiIso (pushforwardChainMap f (constant Y integralCoefficients.{u}))) :
    IsHomotopyConnectedMap f (m + 2) :=
  hf.succ_of_canonical (fun x ↦
    subsingleton_firstObstruction_of_integral_quasiIso f x m hf hH)

end Topology.ReducedMappingCone
