/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.DoubleMappingCylinder.Connectivity
public import Colib.Topology.HomotopyCofiber.ReducedMappingConeCollapse
public import Colib.Topology.Homotopy.HomotopyGroup.Contractible

/-!
# Finite vanishing of the original reduced mapping cone

The point-corner double cylinder preserves finite vanishing above the explicit cutoff two.
Genuine HEP at the two specified original points transfers this through the actual reduction
homotopy equivalence. Every point of the original quotient cone is retained.
-/
/-! Implementation provenance:
`Quillen/Topology/HomotopyCofiber/ReducedMappingConeVanishing.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
universe u
namespace Topology.ReducedMappingCone
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Original point HEP and finite source/target vanishing imply the same bound on the actual cone.
-/
theorem homotopyGroup_subsingleton (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀)
    (hX : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)))
    (hY : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀)))
    (n : ℕ)
    (hπX : ∀ x k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k X x))
    (hπY : ∀ y k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k Y y))
    (z : Space x₀ y₀ f) (k : ℕ) (hk : k < n + 2) :
    Subsingleton (HomotopyGroup.Pi k (Space x₀ y₀ f) z) := by
  let e := (reductionHomotopyEquiv x₀ y₀ f hf hX hY).symm
  let := DoubleCylinder.homotopyGroup_subsingleton (TopCat.ofHom f)
    (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))
    (unreducedSquare f) x₀ n hπX hπY
    (fun p j _ ↦ subsingleton_pi_of_contractible j PUnit.{u + 1} p) (e z) k hk
  exact (homotopyGroupMap_bijective_of_homotopyEquiv e rfl k).injective.subsingleton

end Topology.ReducedMappingCone

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyCofiber/ReducedMappingConeVanishing.lean:27"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.ReducedMappingCone.homotopyGroup_subsingleton
