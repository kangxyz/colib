/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.TransferParameterShiftMap
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularUnit

/-!
# The signed transfer parameter map vanishes at one

The actual singular comparison carries the unit restriction to the
original restriction of the reduced torus presheaf. The same zero
composite persists under the native signed shifts.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open SheafWithTransfers

variable (k : Type u) [Field k]

local notation "B" => torusSectionsFunctor k
local notation "r" => torusSectionsComplexUnitRestriction k
local notation "c" => ComplexShape.up ℤ

private theorem shiftMap_unit {K L Z : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ}
    (s : ℤ) (f : K ⟶ ((B).mapHomologicalComplex c).obj L)
    (x : L⟦s⟧ ⟶ Z) (hf : f ≫ (r).app L = 0) :
    ((shiftFunctor _ s).map f ≫ (((B).mapHomologicalComplex c).commShiftIso s).inv.app L ≫
      ((B).mapHomologicalComplex c).map x) ≫ (r).app Z = 0 := by
  let T := (B).mapHomologicalComplex c
  let S := shiftFunctor (CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) s
  let a := (T.commShiftIso s).app L
  have h₁ : a.inv ≫ (r).app (L⟦s⟧) = S.map ((r).app L) := by
    apply HomologicalComplex.hom_ext
    intro n
    change 𝟙 _ ≫ ((torusSectionsUnitNatTrans k).app (L.X (n + s)) ≫ 𝟙 _) =
      (torusSectionsUnitNatTrans k).app (L.X (n + s)) ≫ 𝟙 _
    exact Category.id_comp _
  have h₂ : T.map x ≫ (r).app Z = (r).app (L⟦s⟧) ≫ x := (r).naturality x
  change (S.map f ≫ a.inv ≫ T.map x) ≫ (r).app Z = 0
  calc
    _ = S.map f ≫ a.inv ≫ (T.map x ≫ (r).app Z) := by simp only [Category.assoc]
    _ = S.map f ≫ a.inv ≫ (r).app (L⟦s⟧) ≫ x :=
      congrArg (fun z => S.map f ≫ a.inv ≫ z) h₂
    _ = S.map (f ≫ (r).app L) ≫ x := by
      rw [← Category.assoc a.inv, h₁, ← Category.assoc, ← S.map_comp]
    _ = _ := by rw [hf, S.map_zero, zero_comp]

/-- The original signed integral transfer map has zero restriction to
the actual unit section of the torus parameter. -/
theorem motivicTransferParameterProduct_comp_unit (q : ℕ) :
    motivicTransferParameterProduct k q ≫
      (r).app ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧) = 0 := by
  let P := reducedTorus k (q + 1)
  let A := singularSheafCochainFunctor k 0
  let : A.Additive := by
    change (singularSheafCochainFunctor k 0).Additive
    unfold singularSheafCochainFunctor singularCochainFunctor
    infer_instance
  let K := singularSheafCochainComplex k P 0
  let f := A.map (reducedTorusParameterProduct k q) ≫ singularSheafCochainTorusSectionsMap k P
  have hf : f ≫ (r).app K = 0 := by
    change (A.map (reducedTorusParameterProduct k q) ≫ _) ≫ (r).app K = 0
    rw [Category.assoc, singularSheafCochainTorusSectionsMap_comp_unit, ← A.map_comp,
      ← Category.assoc]
    have h : reducedTorusParameterProduct k q ≫ torusUnit P = 0 :=
      reducedTorusParameterProduct_parameterPullback_one k q
    rw [h, zero_comp, A.map_zero]
  rw [motivicTransferParameterProduct_eq_shiftTorusParameterMap]
  exact shiftMap_unit k (-(q : ℤ)) f _ hf

end AlgebraicGeometry.PresheafWithTransfers
