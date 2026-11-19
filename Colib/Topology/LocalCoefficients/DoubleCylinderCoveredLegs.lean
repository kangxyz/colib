/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.PiOneLegs
public import Colib.Topology.LocalCoefficients.DoubleCylinderTwistedHomology
public import Colib.Topology.LocalCoefficients.HomologicalWhiteheadCovering

/-!
# Covered weak equivalences for the original double-cylinder legs

The literal endpoint maps of the same pushout are recognized from the original
plus maps with a common kernel. One supplied simply connected cover of the
pushout serves both maps. No equivalence of either leg is assumed.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Topology
open FundamentalGroupoid.LocalCoefficients
open scoped Topology unitInterval
universe u

namespace TopCat.DoubleCylinder

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}

/-- The two literal plus-construction cylinder legs are weak homotopy equivalences
by using the actual fundamental-group maps and local systems on their target. -/
theorem plus_legs_isWeakHomotopyEquivalence_of_cover
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (lo hi : unitInterval) (band : Band lo hi)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : Topology.IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : Topology.IsPlusConstruction.{u, u, u} g.hom δ N)
    {E : Type u} [TopologicalSpace E] [SimplyConnectedSpace E]
    (q : C(E, D)) (hq : IsCoveringMap q) (hs : Function.Surjective q) :
    IsWeakHomotopyEquivalence (gapLeftEndpoint e) ∧
      IsWeakHomotopyEquivalence (gapRightEndpoint e) := by
  let := hf.targetPathConnected
  let := hg.targetPathConnected
  let := pathConnectedSpace f g sq a
  have hπ := plus_legs_piOne_bijective f g sq a b c γ δ N hf hg
  obtain ⟨p, hp⟩ := hs (gapLeftEndpoint e (f a))
  obtain ⟨r, hr⟩ := hs (gapRightEndpoint e (g a))
  refine ⟨?_, ?_⟩
  · exact Topology.LocalCoefficients.isWeakHomotopyEquivalence_of_twisted_quasiIso_of_cover
      (gapLeftEndpoint e) q hq (f a) p hp.symm hπ.1
      (doubleCylinder_leftEnd_universeLift_quasiIso f g sq lo hi band hg.localCoefficients)
  · exact Topology.LocalCoefficients.isWeakHomotopyEquivalence_of_twisted_quasiIso_of_cover
      (gapRightEndpoint e) q hq (g a) r hr.symm hπ.2
      (doubleCylinder_rightEnd_universeLift_quasiIso f g sq lo hi band hf.localCoefficients)

end TopCat.DoubleCylinder
