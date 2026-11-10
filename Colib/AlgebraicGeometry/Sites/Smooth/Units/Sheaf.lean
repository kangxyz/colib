/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Units.Presheaf
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.AlgebraicGeometry.Sites.Nisnevich.GlobalFunctions
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# The ordinary Nisnevich sheaf of actual global units

The global-functions presheaf is a sheaf by its native spectrum adjunction and
Nisnevich subcanonicity. Taking units, additive notation and the coefficient
universe lift preserve limits, hence the sheaf condition. The resulting sections
are literally the existing global units, not merely their sheafification.

Adapted from `Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Units/Basic.lean` at
motivic commit `a6805c4a87cdfd7717dd7a94039246a167f15380`. Definitions of the
ordinary units presheaf belong to the separate `Units.Presheaf` owner.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- Actual global units satisfy Nisnevich descent on the smooth site. -/
theorem unitsPresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (nisnevichTopology S) (unitsPresheaf S) := by
  let : PreservesLimitsOfSize.{u, u + 1} ringUnitsFunctor := by
    unfold ringUnitsFunctor
    change PreservesLimitsOfSize.{u, u + 1}
      (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
        commGroupAddCommGroupEquivalence.functor)
    infer_instance
  have h := Presheaf.isSheaf_comp_of_isSheaf Nisnevich.topology Scheme.Γ ringUnitsFunctor
    globalFunctions_isSheaf
  exact (forgetScheme S).op_comp_isSheaf_of_isSheaf _ _ _ h

/-- The ordinary Nisnevich sheaf with literal global-unit sections. -/
def unitsSheaf (S : Scheme.{u}) : Sheaf (nisnevichTopology S) AddCommGrpCat.{u} :=
  ⟨unitsPresheaf S, unitsPresheaf_isSheaf S⟩

/-- Sections of the sheaf are the actual units, written additively. -/
def unitsSheafSections (S : Scheme.{u}) (X : SmoothSite S) :
    (unitsSheaf S).obj.obj (op X) ≃+ Additive (Γ(X.left, ⊤))ˣ :=
  AddEquiv.refl _

/-- The coefficient universe lift preserves the genuine sheaf condition. -/
theorem largeUnitsPresheaf_isSheaf (S : Scheme.{u}) :
    Presheaf.IsSheaf (nisnevichTopology S) (largeUnitsPresheaf S) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ (unitsPresheaf_isSheaf S)

/-- Global units in the same large coefficient universe as the ordinary motivic complex. -/
def largeUnitsSheaf (S : Scheme.{u}) :
    Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1} :=
  ⟨largeUnitsPresheaf S, largeUnitsPresheaf_isSheaf S⟩

/-- Large sheaf sections retain the literal universe lift of global units. -/
def largeUnitsSheafSections (S : Scheme.{u}) (X : SmoothSite S) :
    (largeUnitsSheaf S).obj.obj (op X) ≃+ ULift.{u + 1} (Additive (Γ(X.left, ⊤))ˣ) :=
  AddEquiv.refl _

end AlgebraicGeometry.Scheme.SmoothSite
