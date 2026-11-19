/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ParameterSheafificationSquare

/-! # Reindexing and the native double-sheafification isomorphism -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u})
variable [HasSheafify (nisnevichTopology S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}]

/-- The genuine reindexing comparison is compatible with the native
Nisnevich-to-étale sheafification isomorphism. No reindexing map is inverted. -/
theorem parameterNisnevichToEtaleComparison_sheafification
    (T : SmoothSite S) (P : (SmoothSite S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    let J := nisnevichTopology S
    let K := etaleTopology S
    let R := Contraction.parameterProduct T
    let Rp := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u + 1}).obj R.op
    let N := presheafToSheaf J AddCommGrpCat.{u + 1}
    let E := nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}
    let Re := R.sheafPushforwardContinuous AddCommGrpCat.{u + 1} K K
    E.map ((R.sheafifyReindexComparison J J AddCommGrpCat.{u + 1}).app P) ≫
      (parameterNisnevichToEtaleComparison S AddCommGrpCat.{u + 1} T).app (N.obj P) ≫
        Re.map ((nisnevichToEtaleSheafificationIso S).hom.app P) =
    (nisnevichToEtaleSheafificationIso S).hom.app (Rp.obj P) ≫
      (R.sheafifyReindexComparison K K AddCommGrpCat.{u + 1}).app P := by
  intro J K R Rp N E Re
  let Q := Re.obj ((presheafToSheaf K AddCommGrpCat.{u + 1}).obj P)
  apply ObjectProperty.hom_ext
  apply sheafify_hom_ext K _ _ Q.property
  apply sheafify_hom_ext J _ _
    ((etaleToNisnevichSheaf S AddCommGrpCat.{u + 1}).obj Q).property
  change toSheafify J (Rp.obj P) ≫
    (toSheafify K (sheafify J (Rp.obj P)) ≫
      (sheafifyMap K ((R.sheafifyReindexComparison J J AddCommGrpCat.{u + 1}).app P).hom ≫
        ((R.sheafifyReindexComparison K K AddCommGrpCat.{u + 1}).app
          (sheafify J P)).hom ≫
          Rp.map ((nisnevichToEtaleSheafificationIso S).hom.app P).hom)) =
    toSheafify J (Rp.obj P) ≫
      (toSheafify K (sheafify J (Rp.obj P)) ≫
        (((nisnevichToEtaleSheafificationIso S).hom.app (Rp.obj P)).hom ≫
          ((R.sheafifyReindexComparison K K AddCommGrpCat.{u + 1}).app P).hom))
  rw [← toSheafify_naturality_assoc]
  rw [← Category.assoc, R.toSheafify_sheafifyReindexComparison]
  change Rp.map (toSheafify J P) ≫
    toSheafify K (Rp.obj (sheafify J P)) ≫
      ((R.sheafifyReindexComparison K K AddCommGrpCat.{u + 1}).app
        (sheafify J P)).hom ≫
        Rp.map ((nisnevichToEtaleSheafificationIso S).hom.app P).hom = _
  rw [R.toSheafify_sheafifyReindexComparison_assoc]
  rw [← Rp.map_comp, ← Rp.map_comp]
  rw [toSheafify_nisnevichToEtaleSheafificationIso]
  have hu := congrArg (fun f => f ≫
    ((R.sheafifyReindexComparison K K AddCommGrpCat.{u + 1}).app P).hom)
      (toSheafify_nisnevichToEtaleSheafificationIso S (Rp.obj P))
  exact (R.toSheafify_sheafifyReindexComparison K K AddCommGrpCat.{u + 1} P).symm.trans
    (by simpa only [Category.assoc] using hu.symm)

end AlgebraicGeometry.Scheme.SmoothSite
