/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Units.Sheaf
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ChangeOfTopology

/-! # Genuine global units on the smooth étale site -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The original smooth inclusion is continuous for the actual étale topologies. -/
instance forgetScheme_etaleContinuous (S : Scheme.{u}) :
    (forgetScheme S).IsContinuous (etaleTopology S) Scheme.etaleTopology :=
  Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy _ _ _ le_rfl

/-- Literal global units satisfy étale descent on the original smooth site. -/
theorem unitsPresheaf_isSheaf_etale (S : Scheme.{u}) :
    Presheaf.IsSheaf (etaleTopology S) (unitsPresheaf S) := by
  have : Scheme.etaleTopology.{u}.Subcanonical :=
    .of_le Scheme.etaleTopology_le_proetaleTopology
  have hΓ : Presheaf.IsSheaf Scheme.etaleTopology Scheme.Γ := by
    intro R
    exact Presieve.isSheaf_iso Scheme.etaleTopology
      (Scheme.globalFunctionsRepresentable R).symm
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  let : PreservesLimitsOfSize.{u, u + 1} ringUnitsFunctor := by
    unfold ringUnitsFunctor
    change PreservesLimitsOfSize.{u, u + 1}
      (forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units ⋙
        commGroupAddCommGroupEquivalence.functor)
    infer_instance
  have h := Presheaf.isSheaf_comp_of_isSheaf Scheme.etaleTopology Scheme.Γ ringUnitsFunctor hΓ
  exact (forgetScheme S).op_comp_isSheaf_of_isSheaf _ _ _ h

/-- The universe lift preserves the actual étale sheaf condition. -/
theorem largeUnitsPresheaf_isSheaf_etale (S : Scheme.{u}) :
    Presheaf.IsSheaf (etaleTopology S) (largeUnitsPresheaf S) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ (unitsPresheaf_isSheaf_etale S)

/-- Actual global units as an étale sheaf, in the motivic coefficient universe. -/
def largeUnitsEtaleSheaf (S : Scheme.{u}) :
    Sheaf (etaleTopology S) AddCommGrpCat.{u + 1} :=
  ⟨largeUnitsPresheaf S, largeUnitsPresheaf_isSheaf_etale S⟩

/-- Nisnevich-to-étale sheafification recovers literal units, canonically. -/
def nisnevichToEtaleLargeUnitsIso (S : Scheme.{u})
    [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}] :
    (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).obj (largeUnitsSheaf S) ≅
      largeUnitsEtaleSheaf S :=
  asIso ((sheafificationAdjunction (etaleTopology S) AddCommGrpCat.{u + 1}).counit.app
    (largeUnitsEtaleSheaf S))

end AlgebraicGeometry.Scheme.SmoothSite
