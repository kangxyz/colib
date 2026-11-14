/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedChangeOfTopology
public import Colib.AlgebraicGeometry.Sites.Smooth.Units.EtaleSheaf

/-! # The original topology-change free source preserves sections -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE

private lemma homEquiv_leftAdjointUniq_inv_comp_map
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : D ⥤ E} {R₂ : E ⥤ D} {L₃ : C ⥤ E}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₂ ⋙ R₁)
    (P : C) (G : D) (f : L₁.obj P ⟶ G) :
    c.homEquiv P (L₂.obj G)
      ((Adjunction.leftAdjointUniq (a.comp b) c).inv.app P ≫ L₂.map f) =
    a.homEquiv P (R₂.obj (L₂.obj G)) (f ≫ b.unit.app G) := by
  rw [c.homEquiv_naturality_right, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app, Adjunction.comp_unit_app,
    a.homEquiv_unit]
  simp only [Functor.comp_map, Category.assoc, ← R₁.map_comp]
  erw [← b.unit.naturality f]
  rfl

universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable (S : Scheme.{u})
variable [HasSheafify (nisnevichTopology S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The original free-Yoneda topology comparison sends sections through the actual unit. -/
lemma nisnevichToEtaleFreeYonedaIso_sections (X : SmoothSite S)
    (G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (f : (freeYoneda.{u + 1} (nisnevichTopology S)).obj X ⟶ G) :
    sectionsEquiv.{u + 1} X ((nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).obj G)
      ((nisnevichToEtaleFreeYonedaIso S).inv.app X ≫
        (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).map f) =
    ((nisnevichToEtaleSheafAdjunction S AddCommGrpCat.{u + 1}).unit.app G).hom.app (op X)
      (sectionsEquiv.{u + 1} X G f) := by
  erw [← sectionsEquiv_naturality.{u + 1} X f
    ((nisnevichToEtaleSheafAdjunction S AddCommGrpCat.{u + 1}).unit.app G)]
  dsimp only [sectionsEquiv, Equiv.trans_apply, nisnevichToEtaleFreeYonedaIso,
    nisnevichToEtaleSheafificationIso, Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  congr 2
  exact homEquiv_leftAdjointUniq_inv_comp_map
    (sheafificationAdjunction (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (nisnevichToEtaleSheafAdjunction S AddCommGrpCat.{u + 1})
    (sheafificationAdjunction (etaleTopology S) AddCommGrpCat.{u + 1}) _ G f

omit [HasSheafify (nisnevichTopology S) AddCommGrpCat.{u + 1}] in
/-- The actual units counit cancels the topology-change unit. -/
lemma nisnevichToEtaleLargeUnitsIso_unit :
    (nisnevichToEtaleSheafAdjunction S AddCommGrpCat.{u + 1}).unit.app
        (largeUnitsSheaf S) ≫
      (etaleToNisnevichSheaf S AddCommGrpCat.{u + 1}).map
        (nisnevichToEtaleLargeUnitsIso S).hom = 𝟙 (largeUnitsSheaf S) := by
  apply (sheafToPresheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}).map_injective
  change ((nisnevichToEtaleSheafAdjunction S AddCommGrpCat.{u + 1}).unit.app
    (largeUnitsSheaf S)).hom ≫ (nisnevichToEtaleLargeUnitsIso S).hom.hom = 𝟙 _
  simp [nisnevichToEtaleLargeUnitsIso, sheafificationAdjunction_counit_app_val,
    largeUnitsEtaleSheaf, largeUnitsSheaf]

/-- The original free-source topology map and units counit preserve the literal unit section. -/
lemma nisnevichToEtaleFreeYonedaIso_units (X : SmoothSite S)
    (f : (freeYoneda.{u + 1} (nisnevichTopology S)).obj X ⟶ largeUnitsSheaf S) :
    sectionsEquiv.{u + 1} X (largeUnitsEtaleSheaf S)
      ((nisnevichToEtaleFreeYonedaIso S).inv.app X ≫
        (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).map f ≫
        (nisnevichToEtaleLargeUnitsIso S).hom) =
      sectionsEquiv.{u + 1} X (largeUnitsSheaf S) f := by
  rw [← Category.assoc, sectionsEquiv_naturality, nisnevichToEtaleFreeYonedaIso_sections]
  exact congrArg (fun t => t.hom.app (op X)
    (sectionsEquiv.{u + 1} X (largeUnitsSheaf S) f)) (nisnevichToEtaleLargeUnitsIso_unit S)

end AlgebraicGeometry.Scheme.SmoothSite
