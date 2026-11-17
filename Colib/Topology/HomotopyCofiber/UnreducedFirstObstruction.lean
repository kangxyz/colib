/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyCofiber.ReducedMappingConeFiniteConnectivity
public import Colib.Topology.DoubleMappingCylinder.Connectivity
public import Colib.Topology.Homotopy.HomotopyGroup.Contractible
public import Colib.Topology.HomotopyFiber.WeakSourcePositive
public import Colib.Topology.HomotopyFiber.IteratedFiberPath
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.SimplyConnected

/-!
# The first possible relative homotopy group and the actual unreduced cone gap

For a map from a simply connected space, the proved finite homotopy-excision theorem gives
an extra degree of connectivity for its original cone gap. The actual common-base fiber map
therefore preserves the first possible nonzero relative homotopy group, including relative
degree two. Its inner path is the full original cone cylinder and its outer path is unchanged.

The supplied cylinder path also identifies the iterated fiber with the cone loop space.
The resulting vanishing criterion is purely homotopical: no homology comparison or Hurewicz
theorem is assumed or asserted.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyCofiber/UnreducedFirstObstruction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Both original stored paths and
actual fiber endpoints are retained. -/
@[expose] public section
noncomputable section

open scoped Topology unitInterval
universe u
namespace Topology.ReducedMappingCone

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))

/-- The original cone gap projects strictly to the original map. -/
@[simp] theorem projection_unreducedFiberComparison :
    (HomotopyFiber.projection (unreducedInclusion f) (unreducedVertex f)).comp
      (unreducedFiberComparison f) = f := rfl

/-- Apply the literal cone gap to the source coordinate and retain the original fiber path. -/
def unreducedFirstObstructionMap (y : Y) : C(HomotopyFiber f y,
    HomotopyFiber (HomotopyFiber.projection (unreducedInclusion f) (unreducedVertex f)) y) :=
  HomotopyFiber.mapOver f
    (HomotopyFiber.projection (unreducedInclusion f) (unreducedVertex f))
    (unreducedFiberComparison f) rfl y

/-- The new inner fiber point is the original cone gap at the unchanged source point. -/
@[simp] theorem unreducedFirstObstructionMap_source (y : Y) (z : HomotopyFiber f y) :
    (unreducedFirstObstructionMap f y z).1.1 = unreducedFiberComparison f z.1.1 := rfl

/-- The entire original outer path is unchanged. -/
@[simp] theorem unreducedFirstObstructionMap_outerPath (y : Y) (z : HomotopyFiber f y) :
    (unreducedFirstObstructionMap f y z).1.2 = z.1.2 := rfl

/-- The inner path retains the original cylinder coordinate at every time. -/
theorem unreducedFirstObstructionMap_innerPath (y : Y) (z : HomotopyFiber f y)
    (t : unitInterval) :
    (unreducedFirstObstructionMap f y z).1.1.1.2 t =
      unreducedCylinder f (z.1.1, ULift.up t) := rfl

/-- The outer basepoint is literal, but its inner path is the original cylinder, not constant. -/
@[simp] theorem unreducedFirstObstructionMap_basepoint (x : X) (y : Y) (h : f x = y) :
    unreducedFirstObstructionMap f y (HomotopyFiber.basepoint f y x h) =
      HomotopyFiber.basepoint
        (HomotopyFiber.projection (unreducedInclusion f) (unreducedVertex f)) y
        (unreducedFiberComparison f x) h :=
  HomotopyFiber.mapOver_basepoint f
    (HomotopyFiber.projection (unreducedInclusion f) (unreducedVertex f))
    (unreducedFiberComparison f) rfl x y h

/-- Simple connectedness of the source supplies q=2 in the actual finite excision range. -/
theorem unreducedFiberComparison_connected_of_simplyConnected [SimplyConnectedSpace X]
    (x : X) (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1)) :
    IsHomotopyConnectedMap (unreducedFiberComparison f) (m + 2) :=
  unreducedFiberComparison_isHomotopyConnectedMap f (m + 1) 2 (m + 2) (by omega) hf
    (isHomotopyConnectedMap_const_two_of_simplyConnected x)

/-- The exact original fiber comparison is bijective in the first possible obstruction degree.
At m=0 this is a theorem about the actual fundamental group of the homotopy fiber. -/
theorem unreducedFirstObstructionMap_pi_bijective [SimplyConnectedSpace X]
    (x : X) (y : Y) (h : f x = y) (m : ℕ)
    (hf : IsHomotopyConnectedMap f (m + 1)) :
    Function.Bijective (HomotopyGroup.piMap m (unreducedFirstObstructionMap f y)
      (unreducedFirstObstructionMap_basepoint f x y h)) := by
  have hg := unreducedFiberComparison_connected_of_simplyConnected f x m hf
  exact HomotopyFiber.piMap_mapOver_bijective f
    (HomotopyFiber.projection (unreducedInclusion f) (unreducedVertex f))
    (unreducedFiberComparison f) rfl x y h m
    (hg.homotopyGroupMap_bijective x (m + 1) (by omega))
    (hg.homotopyGroupMap_surjective x (m + 2) (by omega))

/-- The first actual relative homotopy set agrees with the cone homotopy set in the next degree.
The forward comparison begins with the original path-retaining cone gap. -/
def firstObstructionEquivCone [SimplyConnectedSpace X]
    (x : X) (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1)) :
    HomotopyGroup.Pi (m + 1) (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl) ≃
        HomotopyGroup.Pi (m + 2) (UnreducedSpace f) (unreducedVertex f) :=
  (Equiv.ofBijective
    (HomotopyGroup.piMap m (unreducedFirstObstructionMap f (f x))
      (unreducedFirstObstructionMap_basepoint f x (f x) rfl))
    (unreducedFirstObstructionMap_pi_bijective f x (f x) rfl m hf)).trans
      (HomotopyFiber.iteratedFiberPiEquivOfPath (unreducedInclusion f) (unreducedVertex f)
        (f x) (HomotopyFiber.toPath (unreducedInclusion f) (unreducedVertex f)
          (unreducedFiberComparison f x))
        (HomotopyFiber.basepoint
          (HomotopyFiber.projection (unreducedInclusion f) (unreducedVertex f)) (f x)
          (unreducedFiberComparison f x) rfl) (m + 1))

/-- The actual cone has no earlier homotopy obstruction. Degree one uses genuine
simple-connected gluing; the higher degrees use the original finite excision comparison. -/
theorem unreducedCone_subsingleton_below_first
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (x : X) (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1))
    (z : UnreducedSpace f) (k : ℕ) (hk : k < m + 2) :
    Subsingleton (HomotopyGroup.Pi k (UnreducedSpace f) z) := by
  let : PathConnectedSpace (UnreducedSpace f) :=
    TopCat.DoubleCylinder.pathConnectedSpace (TopCat.ofHom f)
      (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))
      (unreducedSquare f) x
  by_cases hk₂ : k < 2
  · exact TopCat.DoubleCylinder.homotopyGroup_subsingleton (TopCat.ofHom f)
      (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))
      (unreducedSquare f) x 0
      (fun a j hj ↦ subsingleton_homotopyGroup_lt_two_of_simplyConnected a j hj)
      (fun b j hj ↦ subsingleton_homotopyGroup_lt_two_of_simplyConnected b j hj)
      (fun a j _ ↦ subsingleton_pi_of_contractible j PUnit.{u + 1} a) z k hk₂
  · obtain ⟨l, rfl⟩ : ∃ l, k = l + 2 := ⟨k - 2, by omega⟩
    let := hf.fiber_subsingleton (f x) (HomotopyFiber.basepoint f (f x) x rfl)
      (l + 1) (by omega)
    let : Subsingleton (HomotopyGroup.Pi (l + 2) (UnreducedSpace f) (unreducedVertex f)) :=
      (firstObstructionEquivCone f x l (hf.mono (by omega))).symm.injective.subsingleton
    exact (pathTransport (PathConnectedSpace.joined (unreducedVertex f) z).somePath
      (l + 2)).symm.injective.subsingleton

/-- A vanishing cone homotopy group kills the first relative obstruction via the actual map.
This is the homotopy-excision bridge; vanishing cone homology is not an input to this theorem. -/
theorem subsingleton_firstObstruction_of_cone [SimplyConnectedSpace X]
    (x : X) (m : ℕ) (hf : IsHomotopyConnectedMap f (m + 1))
    (hcone : Subsingleton (HomotopyGroup.Pi (m + 2) (UnreducedSpace f) (unreducedVertex f))) :
    Subsingleton (HomotopyGroup.Pi (m + 1) (HomotopyFiber f (f x))
      (HomotopyFiber.basepoint f (f x) x rfl)) := by
  let := hcone
  exact (firstObstructionEquivCone f x m hf).injective.subsingleton

end Topology.ReducedMappingCone
