/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.PushoutVanishing
public import Colib.Topology.HomotopyCofiber.ReducedMappingConeVanishing
public import Colib.Topology.Prespectrum.StrictSquarePointHEP

/-!
# The exact finite loss in the original Bass operation

Finite vanishing of the four original corners passes through the original reduced span and
cone with no loss above cutoff two. The original parameter-loop space then loses precisely
one degree, at every actual loop component. Only the original four point HEP hypotheses
enter this fixed-level assertion; neither separation nor an Omega condition is required.
-/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/StrictSquareVanishing.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum.StrictSquare
variable (S : Arrow (Arrow LoopPrespectrum.{u})) (m n : ℕ)

/-- The genuine strict-square Bass operation loses one degree of finite vanishing. -/
theorem loopedCone_homotopyGroup_subsingleton
    (hA : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.left.point m))))
    (hB : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.left.right.point m))))
    (hC : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.left.point m))))
    (hD : TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (S.right.right.point m))))
    (hπA : ∀ a k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (S.left.left.space m) a))
    (hπB : ∀ b k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (S.left.right.space m) b))
    (hπC : ∀ c k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (S.right.left.space m) c))
    (hπD : ∀ d k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k (S.right.right.space m) d))
    (γ : (strictSquareLoopedConeFunctor.obj S).space m) (k : ℕ) (hk : k < n + 1) :
    Subsingleton (HomotopyGroup.Pi k ((strictSquareLoopedConeFunctor.obj S).space m) γ) := by
  have hs (z : (span S).space m) (j : ℕ) (hj : j < n + 2) :
      Subsingleton (HomotopyGroup.Pi j ((span S).space m) z) :=
    HomotopyPushout.homotopyGroup_subsingleton S.left.hom S.hom.left m n hA hB hC
      hπA hπB hπC z j hj
  have hc := ReducedMappingCone.homotopyGroup_subsingleton
    ((span S).point m) (S.right.right.point m) ((comparison S).map m)
    ((comparison S).map_point m) (span_point_homotopyExtensionProperty S m hA hB hC) hD
    n hs hπD ((mappingCone (comparison S)).point m) (k + 1) (by omega)
  exact subsingleton_pi_loop_of_succ ((mappingCone (comparison S)).point m) k hc γ

end Topology.LoopPrespectrum.StrictSquare

attribute [colib_ref "quillen" "Quillen/Topology/Prespectrum/StrictSquareVanishing.lean:28"
  "adaptation" "The actual maps and finite bounds, with native objects and namespaces"]
  Topology.LoopPrespectrum.StrictSquare.loopedCone_homotopyGroup_subsingleton
