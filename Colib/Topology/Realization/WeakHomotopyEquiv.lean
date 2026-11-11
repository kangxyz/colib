/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.HELP.CompactHomotopyEquivalence
public import Colib.Topology.HELP.RealizedSimplexBoundary
public import Colib.Topology.Realization.MapWeakEquivalence

/-!
# Weak realization equivalences have actual homotopy inverses

Finite cube lifting is transported to the actual realized simplex boundaries.
The actual mapping-path endpoint then supplies an inverse by lifting the empty
simplicial inclusion. Its lift against the two simplicial cylinder endpoints
supplies the second inverse homotopy. The forward continuous map is literal.

The inverse construction adapts `Topology.homotopyEquivOfCompactHELP` in
`Colib.Topology.HELP.CompactHomotopyEquivalence`; its compact HELP premise is
replaced by the exact generator lifting used in the proof.
-/

@[expose] public noncomputable section

open TopCat Topology SSet CategoryTheory Limits
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

/-- Lifting of the actual mapping-path endpoint against realized simplex boundaries
gives a homotopy inverse between realizations, with the original forward map. -/
def homotopyEquivOfRealizedBoundaryLifting {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : ∀ n : ℕ, HasLiftingProperty
      (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})))
      (TopCat.ofHom (MappingPath.endpoint f))) :
    ContinuousMap.HomotopyEquiv |X| |Y| := by
  let i := (⊥ : Y.Subcomplex).ι
  let a : |((⊥ : Y.Subcomplex) : SSet.{u})| ⟶ TopCat.of (MappingPath f) :=
    TopCat.ofHom ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let p := TopCat.ofHom (MappingPath.endpoint f)
  letI : HasLiftingProperty (SSet.toTop.map i) p :=
    SSet.hasLiftingProperty_realization_mono p hf i
  have sq : CommSq a (SSet.toTop.map i) p (𝟙 |Y|) := ⟨by ext x; exact isEmptyElim x⟩
  let s := sq.lift
  have hs : s ≫ p = 𝟙 |Y| := sq.fac_right
  let g : C(|Y|, |X|) := (MappingPath.source f).comp s.hom
  let K : (f.comp g).Homotopy (ContinuousMap.id |Y|) := {
    toFun z := (s z.2).1.2 z.1
    continuous_toFun := by fun_prop
    map_zero_left x := (s x).2
    map_one_left x := ConcreteCategory.congr_hom hs x }
  let a₀ : |X| ⟶ TopCat.of (MappingPath f) := TopCat.ofHom f ≫ s
  let a₁ : |X| ⟶ TopCat.of (MappingPath f) := TopCat.ofHom (MappingPath.inclusion f)
  have h₀ : a₀ ≫ p = TopCat.ofHom f := by rw [Category.assoc, hs, Category.comp_id]
  have h₁ : a₁ ≫ p = TopCat.ofHom f := rfl
  let H := homotopyOfRealizedEndpointLifting p X
    (SSet.hasLiftingProperty_realization_mono p hf (simplicialCylinderEndpoints X))
    a₀ a₁ (TopCat.ofHom f) h₀ h₁
  exact {
    toFun := f
    invFun := g
    left_inv := ⟨((ContinuousMap.Homotopy.refl (MappingPath.source f)).comp H).cast rfl rfl⟩
    right_inv := ⟨K⟩ }

@[simp]
theorem homotopyEquivOfRealizedBoundaryLifting_toFun {X Y : SSet.{u}} (f : C(|X|, |Y|))
    (hf : ∀ n : ℕ, HasLiftingProperty
      (SSet.toTop.map (∂Δ[n].ι : _ ⟶ (Δ[n] : SSet.{u})))
      (TopCat.ofHom (MappingPath.endpoint f))) :
    (homotopyEquivOfRealizedBoundaryLifting f hf).toFun = f := rfl

end Topology

namespace SSet.IsRealizationWeakEquivalence

/-- An actual realization weak equivalence is a homotopy equivalence with
exactly the original realized forward map. -/
def homotopyEquiv {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : IsRealizationWeakEquivalence f) : ContinuousMap.HomotopyEquiv |X| |Y| :=
  Topology.homotopyEquivOfRealizedBoundaryLifting (SSet.toTop.map f).hom
    (MappingPath.endpoint_hasLiftingProperty_realizationBoundary_of_isWeakHomotopyEquivalence hf)

@[simp]
theorem homotopyEquiv_toFun {X Y : SSet.{u}} {f : X ⟶ Y}
    (hf : IsRealizationWeakEquivalence f) :
    hf.homotopyEquiv.toFun = (SSet.toTop.map f).hom := rfl

end SSet.IsRealizationWeakEquivalence

namespace SSet.IsRealizationWeakEquivalence

attribute [colib_tag "COL-1012"]
  homotopyEquiv
  homotopyEquiv_toFun
attribute [colib_ref "HatcherAT" "Section 4.1, Theorem 4.5, p. 346" "background"
  "The classical CW counterpart of the realization-map comparison"]
  homotopyEquiv

end SSet.IsRealizationWeakEquivalence
