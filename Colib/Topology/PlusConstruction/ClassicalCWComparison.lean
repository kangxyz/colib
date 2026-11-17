/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.CWComplex.ThinNeighborhoods
public import Colib.Topology.Covering.PathClassSimplyConnected
public import Colib.Topology.DoubleMappingCylinder.ComparisonDescent
public import Colib.Topology.DoubleMappingCylinder.CWWhitehead
public import Colib.Topology.DoubleMappingCylinder.ThinNeighborhoods
public import Colib.Topology.LocalCoefficients.DoubleCylinderCoveredLegs

/-!
# Comparison for plus constructions on classical CW complexes

The literal double mapping cylinder has a simply connected path-class cover.
The two plus maps determine homotopy equivalences from the original ends into
the cylinder, giving a comparison under the original source up to homotopy.

Adapted from the CW comparison in
`Quillen/Topology/PlusConstruction/ClassicalCWUniqueness.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Topology
open scoped unitInterval

universe u

namespace TopCat.DoubleCylinder

variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]

include A B C in
/-- Both actual endpoint maps are weak equivalences. The only cover needed is
the path-class cover of the actual double mapping cylinder. -/
theorem plus_legs_isWeakHomotopyEquivalence_of_cw
    {D : TopCat.{u}} (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (TopCat.intervalEndpoints (TopCat.of A)) (endMap f g) l e)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : Topology.IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : Topology.IsPlusConstruction.{u, u, u} g.hom δ N) :
    IsWeakHomotopyEquivalence (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e) ∧
      IsWeakHomotopyEquivalence (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e) := by
  letI := CWComplex.locallyPathConnectedSpace A
  letI := CWComplex.locallyPathConnectedSpace B
  letI := CWComplex.locallyPathConnectedSpace C
  letI := hf.targetPathConnected
  letI := hg.targetPathConnected
  letI := pathConnectedSpace f g sq a
  letI := locallyPathConnectedSpace f g sq
  let neighborhoods := pathThinNeighborhoods f g sq
    (CWComplex.pathThinNeighborhoods B) (CWComplex.pathThinNeighborhoods C)
  let d₀ : D := gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e b
  letI := (neighborhoods.prebundle d₀).totalSpaceTopology
  letI := neighborhoods.total_simplyConnectedSpace d₀
  let lo : unitInterval := ⟨1 / 3, by norm_num⟩
  let hi : unitInterval := ⟨2 / 3, by norm_num⟩
  let mid : Band lo hi := ⟨⟨1 / 2, by norm_num⟩, by
    constructor
    · change (1 : ℝ) / 3 < 1 / 2
      norm_num
    · change (1 : ℝ) / 2 < 2 / 3
      norm_num⟩
  exact plus_legs_isWeakHomotopyEquivalence_of_cover f g sq lo hi mid a b c γ δ N hf hg
    (neighborhoods.totalProjection d₀) (neighborhoods.isCoveringMap_projection d₀)
    (PathThinNeighborhoods.projection_surjective d₀)

end TopCat.DoubleCylinder

namespace Topology.IsPlusConstruction

open TopCat.DoubleCylinder

variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]

include A B C in
/-- Two same-universe plus constructions on actual classical CW subtypes admit
a homotopy equivalence commuting with the original maps up to homotopy. -/
theorem exists_classicalCWComparison
    (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
    (a : A) (b : B) (c : C) (γ : Path (f a) b) (δ : Path (g a) c)
    (N : Subgroup (HomotopyGroup.Pi 1 A a))
    (hf : IsPlusConstruction.{u, u, u} f.hom γ N)
    (hg : IsPlusConstruction.{u, u, u} g.hom δ N) :
    ∃ h : ContinuousMap.HomotopyEquiv B C, (h.toFun.comp f.hom).Homotopic g.hom := by
  let D : TopCat.{u} := pushout (TopCat.intervalEndpoints (TopCat.of A)) (endMap f g)
  let l : TopCat.of A ⊗ TopCat.I ⟶ D := pushout.inl _ _
  let e : TopCat.of (B ⊕ C) ⟶ D := pushout.inr _ _
  have sq : IsPushout (TopCat.intervalEndpoints (TopCat.of A)) (endMap f g) l e :=
    IsPushout.of_hasPushout _ _
  obtain ⟨hL, hR⟩ := plus_legs_isWeakHomotopyEquivalence_of_cw A B C f g sq a b c γ δ N hf hg
  let L := cwLeftEndpointHomotopyEquiv A B C f g sq hL
  let R := cwHomotopyEquivOfWeakMap A B C f g sq C
    (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e) hR
  exact ⟨L.trans R.symm, ⟨comparisonUnderSourceOfLegEquivs f g sq L R rfl rfl⟩⟩

end Topology.IsPlusConstruction
