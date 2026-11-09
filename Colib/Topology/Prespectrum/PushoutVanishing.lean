/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.DoubleMappingCylinder.Connectivity
public import Colib.Topology.Prespectrum.PushoutReduction

/-!
# Finite vanishing of the original reduced prespectrum pushout

At a fixed original level, the three chosen-point HEP hypotheses transfer genuine double-cylinder
vanishing through the original reduction. The finite cutoff is explicit and all quotient points
are included, so this can be iterated without replacing the original spectrum spaces.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/PushoutVanishing.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- Every original reduced-pushout point inherits the common finite bound of the three corners.
-/
theorem homotopyGroup_subsingleton (m n : ℕ)
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point m))))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point m))))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point m))))
    (hπA : ∀ a k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (A.space m) a))
    (hπB : ∀ b k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (B.space m) b))
    (hπC : ∀ c k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (C.space m) c))
    (z : Space f g m) (k : ℕ) (hk : k < n + 2) :
    Subsingleton (HomotopyGroup.Pi k (Space f g m) z) := by
  let e := (reductionHomotopyEquiv f g m hA hB hC).symm
  let := DoubleCylinder.homotopyGroup_subsingleton (TopCat.ofHom (f.map m))
    (TopCat.ofHom (g.map m)) (unreducedSquare f g m) (A.point m) n hπA hπB hπC (e z) k hk
  exact (homotopyGroupMap_bijective_of_homotopyEquiv e rfl k).injective.subsingleton

end Topology.LoopPrespectrum.HomotopyPushout

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/PushoutVanishing.lean:27"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.HomotopyPushout.homotopyGroup_subsingleton
