/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.ConeLinearExcision
public import Colib.Topology.Prespectrum.PushoutVanishing

/-!
# Original right-inclusion excision from linear corner growth

The actual reduced pushout inherits the all-point vanishing range of its three original
corners and genuine HEP at its literal point. The unchanged right inclusion therefore has
stable original cone-to-fiber excision, with no independent intermediate-pushout premise.
-/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C) (c : ℕ)

/-- Linear corner growth discharges actual right-inclusion excision for the original pushout. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutLinearExcision.lean:26"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem inr_coneFiber_isStableEquivalence_of_linearGrowth
    (hA : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point (n + c + 2)))))
    (hB : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point (n + c + 2)))))
    (hC : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point (n + c + 2)))))
    (hπA : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (A.space (n + c + 2)) x))
    (hπB : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (B.space (n + c + 2)) x))
    (hπC : ∀ n x k, k < n + 2 →
      Subsingleton (HomotopyGroup.Pi k (C.space (n + c + 2)) x)) :
    IsStableEquivalence (mappingConeFiberComparison (inr f g)) :=
  mappingConeFiberComparison_isStableEquivalence_of_linearGrowth (inr f g) c hC
    (fun n ↦ point_homotopyExtensionProperty f g _ (hA n) (hB n) (hC n)) hπC
    (fun n x k hk ↦ homotopyGroup_subsingleton f g _ n (hA n) (hB n) (hC n)
      (hπA n) (hπB n) (hπC n) x k hk)

end Topology.LoopPrespectrum.HomotopyPushout
