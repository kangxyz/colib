/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.CubicalLifting
public import Colib.Topology.HELP.WeakFinite
public import Colib.Topology.HELP.CompactHomotopyEquivalence

/-!
# Whitehead recognition from actual realization domination

A space is dominated by a realization when there are continuous maps to and
from that realization whose composite is homotopic to the identity on the
original space. A weak equivalence from a realization to such a space has an
actual homotopy inverse, with its original forward map unchanged.

The domination data contain no inverse to the weak equivalence. Lifting over
the empty realized inclusion first constructs a mapping-path section over the
dominating realization. The displayed domination homotopy and the genuine
mapping-path covering homotopy property extend it to a section over the actual
target. Realized cylinder-endpoint lifting gives the other inverse homotopy.

This reduces a future loop-space application to constructing actual domination
maps and their homotopy. It does not assert domination for arbitrary loop
spaces or invert a merely weak CW approximation.
-/

open SSet Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/Realization/Domination.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps and proofs are retained. -/

@[expose] public section
noncomputable section

open CategoryTheory
open scoped Simplicial Topology unitInterval

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet.Realization

/-- Actual realization domination of the target supplies a strict section of
the mapping-path endpoint of any weak equivalence. The source is arbitrary. -/
theorem exists_mappingPath_section_of_domination
    {E Y : Type u} [TopologicalSpace E] [TopologicalSpace Y]
    (f : C(E, Y)) (hf : IsWeakHomotopyEquivalence f) (T : SSet.{u})
    (a : C(Y, |T|)) (b : C(|T|, Y))
    (H : (b.comp a).Homotopy (ContinuousMap.id Y)) :
    ∃ s : C(Y, MappingPath f), (MappingPath.endpoint f).comp s = ContinuousMap.id Y := by
  let i := (⊥ : T.Subcomplex).ι
  let z : |((⊥ : T.Subcomplex) : SSet.{u})| ⟶ TopCat.of (MappingPath f) :=
    TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let p := TopCat.ofHom (MappingPath.endpoint f)
  let : HasLiftingProperty (SSet.toTop.map i) p :=
    hf.mappingPath_endpoint_boundaryLifting.hasLiftingProperty_realization_mono i
  have sq : CommSq z (SSet.toTop.map i) p (TopCat.ofHom b) :=
    ⟨by ext x; exact isEmptyElim x⟩
  let l := sq.lift
  have hl : l ≫ p = TopCat.ofHom b := sq.fac_right
  obtain ⟨L, _, hL⟩ := MappingPath.endpoint_homotopy_lifting f (l.hom.comp a)
    H.toContinuousMap (by
      intro y
      exact (H.apply_zero y).trans (ConcreteCategory.congr_hom hl (a y)).symm)
  refine ⟨⟨fun y ↦ L (1, y), by fun_prop⟩, ?_⟩
  ext y
  exact (hL 1 y).trans (H.apply_one y)

/-- A chosen actual section obtained from the proved lifting construction. -/
def mappingPathSectionOfDomination
    {E Y : Type u} [TopologicalSpace E] [TopologicalSpace Y]
    (f : C(E, Y)) (hf : IsWeakHomotopyEquivalence f) (T : SSet.{u})
    (a : C(Y, |T|)) (b : C(|T|, Y))
    (H : (b.comp a).Homotopy (ContinuousMap.id Y)) : C(Y, MappingPath f) :=
  (exists_mappingPath_section_of_domination f hf T a b H).choose

@[simp]
theorem mappingPathSectionOfDomination_endpoint
    {E Y : Type u} [TopologicalSpace E] [TopologicalSpace Y]
    (f : C(E, Y)) (hf : IsWeakHomotopyEquivalence f) (T : SSet.{u})
    (a : C(Y, |T|)) (b : C(|T|, Y))
    (H : (b.comp a).Homotopy (ContinuousMap.id Y)) :
    (MappingPath.endpoint f).comp (mappingPathSectionOfDomination f hf T a b H) =
      ContinuousMap.id Y :=
  (exists_mappingPath_section_of_domination f hf T a b H).choose_spec

/-- A weak equivalence from an actual realization to a realization-dominated
space is an actual homotopy equivalence with exactly the given forward map. -/
def homotopyEquivOfWeakHomotopyEquivalenceOfDomination
    {X : SSet.{u}} {Y : Type u} [TopologicalSpace Y]
    (f : C(|X|, Y)) (hf : IsWeakHomotopyEquivalence f) (T : SSet.{u})
    (a : C(Y, |T|)) (b : C(|T|, Y))
    (H : (b.comp a).Homotopy (ContinuousMap.id Y)) :
    ContinuousMap.HomotopyEquiv |X| Y := by
  let s := mappingPathSectionOfDomination f hf T a b H
  have hs : (MappingPath.endpoint f).comp s = ContinuousMap.id Y :=
    mappingPathSectionOfDomination_endpoint f hf T a b H
  let g : C(Y, |X|) := (MappingPath.source f).comp s
  let K : (f.comp g).Homotopy (ContinuousMap.id Y) := {
    toFun z := (s z.2).1.2 z.1
    continuous_toFun := by fun_prop
    map_zero_left y := (s y).2
    map_one_left y := ContinuousMap.congr_fun hs y }
  let p := TopCat.ofHom (MappingPath.endpoint f)
  let a₀ : |X| ⟶ TopCat.of (MappingPath f) := TopCat.ofHom (s.comp f)
  let a₁ : |X| ⟶ TopCat.of (MappingPath f) := TopCat.ofHom (MappingPath.inclusion f)
  have h₀ : a₀ ≫ p = TopCat.ofHom f := by
    ext x
    exact ContinuousMap.congr_fun hs (f x)
  have h₁ : a₁ ≫ p = TopCat.ofHom f := rfl
  let L := TopCat.homotopyOfRealizedEndpointLifting p X
    (hf.mappingPath_endpoint_boundaryLifting.hasLiftingProperty_realization_mono
      (simplicialCylinderEndpoints X))
    a₀ a₁ (TopCat.ofHom f) h₀ h₁
  exact {
    toFun := f
    invFun := g
    left_inv := ⟨((ContinuousMap.Homotopy.refl (MappingPath.source f)).comp L).cast rfl rfl⟩
    right_inv := ⟨K⟩ }

@[simp]
theorem homotopyEquivOfWeakHomotopyEquivalenceOfDomination_toFun
    {X : SSet.{u}} {Y : Type u} [TopologicalSpace Y]
    (f : C(|X|, Y)) (hf : IsWeakHomotopyEquivalence f) (T : SSet.{u})
    (a : C(Y, |T|)) (b : C(|T|, Y))
    (H : (b.comp a).Homotopy (ContinuousMap.id Y)) :
    (homotopyEquivOfWeakHomotopyEquivalenceOfDomination f hf T a b H).toFun = f := rfl

end SSet.Realization
