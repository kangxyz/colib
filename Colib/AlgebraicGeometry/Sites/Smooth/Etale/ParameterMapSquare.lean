/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ParameterReindexSquare

/-! # Change of topology on actual sheafified parameter maps -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u})
variable [HasSheafify (nisnevichTopology S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}]

/-- The canonical comparison carries the sheafification of any actual parameter
map to its étale sheafification, through the native double-sheafification isos. -/
theorem parameterNisnevichToEtaleComparison_map
    (T : SmoothSite S) {P Q : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (f : P ⟶ (Contraction.parameterProduct T).op ⋙ Q) :
    let J := nisnevichTopology S
    let K := etaleTopology S
    let R := Contraction.parameterProduct T
    let N := presheafToSheaf J AddCommGrpCat.{u + 1}
    let A := presheafToSheaf K AddCommGrpCat.{u + 1}
    let E := nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}
    let Re := R.sheafPushforwardContinuous AddCommGrpCat.{u + 1} K K
    E.map (N.map f ≫ (R.sheafifyReindexComparison J J AddCommGrpCat.{u + 1}).app Q) ≫
      (parameterNisnevichToEtaleComparison S AddCommGrpCat.{u + 1} T).app (N.obj Q) ≫
        Re.map ((nisnevichToEtaleSheafificationIso S).hom.app Q) =
    (nisnevichToEtaleSheafificationIso S).hom.app P ≫ A.map f ≫
      (R.sheafifyReindexComparison K K AddCommGrpCat.{u + 1}).app Q := by
  intro J K R N A E Re
  rw [E.map_comp, Category.assoc,
    parameterNisnevichToEtaleComparison_sheafification]
  rw [← Category.assoc]
  change ((presheafToSheaf J AddCommGrpCat.{u + 1} ⋙ E).map f ≫
    (nisnevichToEtaleSheafificationIso S).hom.app _) ≫ _ = _
  rw [(nisnevichToEtaleSheafificationIso S).hom.naturality]
  exact Category.assoc _ _ _

end AlgebraicGeometry.Scheme.SmoothSite
