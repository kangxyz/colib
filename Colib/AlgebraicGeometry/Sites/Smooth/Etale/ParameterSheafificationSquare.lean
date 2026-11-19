/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ParameterChangeOfTopology
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedChangeOfTopology

/-! # Units for the native double-sheafification comparison -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u})
variable [HasSheafify (nisnevichTopology S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}]

/-- The native double-sheafification isomorphism preserves the composite units. -/
theorem toSheafify_nisnevichToEtaleSheafificationIso
    (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    toSheafify (nisnevichTopology S) P ≫
      toSheafify (etaleTopology S) (sheafify (nisnevichTopology S) P) ≫
        ((nisnevichToEtaleSheafificationIso S).hom.app P).hom =
    toSheafify (etaleTopology S) P := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((sheafificationAdjunction (nisnevichTopology S) AddCommGrpCat.{u + 1}).comp
      (nisnevichToEtaleSheafAdjunction S AddCommGrpCat.{u + 1}))
    (sheafificationAdjunction (etaleTopology S) AddCommGrpCat.{u + 1}) P
  simp only [Adjunction.comp_unit_app, sheafificationAdjunction_unit_app,
    Category.assoc] at h
  change toSheafify (nisnevichTopology S) P ≫
    ((nisnevichToEtaleSheafAdjunction S AddCommGrpCat.{u + 1}).unit.app
      ((presheafToSheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}).obj P)).hom ≫
        ((nisnevichToEtaleSheafificationIso S).hom.app P).hom = _ at h
  rw [nisnevichToEtaleSheafAdjunction_unit_app_hom] at h
  exact h

end AlgebraicGeometry.Scheme.SmoothSite
