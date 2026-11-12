/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.ParameterNaturality
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.CylinderNaturality
import Mathlib.CategoryTheory.Localization.Predicate

/-!
# The unit and constant summands of total derived torus sections

The two original parameter morphisms give the section and retraction.
The base product is identified using its actual first projection.
The derived evaluation map is pinned by the original K-injective
comparison unit on each cochain complex.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe w u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "G" => SmoothSite.multiplicativeGroupObject S
local notation "B" => SmoothSite.base S

/-- The graph of the actual base-product projection gives the original
base-product coefficients of a transfer presheaf. -/
def baseSectionsPresheafIso (P : PresheafWithTransfers.{u + 1} k) :
    P ≅ baseSections P := by
  let e : Cor.parameterProduct B ≅ 𝟭 (Cor k) :=
    NatIso.ofComponents (fun X => (Cor.graphFunctor k).mapIso (productBaseIso X.toSmoothSite))
      (fun {X Y} f => Cor.parameterProduct_projection_naturality
        X.toSmoothSite Y.toSmoothSite B f)
  exact ObjectProperty.isoMk _ (P.obj.leftUnitor.symm ≪≫
    Functor.isoWhiskerRight (NatIso.op e) P.obj)

/-- The first-projection comparison is natural in the actual coefficient. -/
def baseSectionsPresheafNatIso : 𝟭 (PresheafWithTransfers.{u + 1} k) ≅
    withParameterFunctor B :=
  NatIso.ofComponents (baseSectionsPresheafIso k) (fun {P Q} f => by
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext V
    exact (f.hom.naturality
      ((Cor.graphFunctor k).map (productBaseIso V.unop.toSmoothSite).hom).op).symm)

/-- Sheafification of the actual base-product coefficient isomorphism is
the original base comparison on the sheafification. -/
theorem baseSectionsSheafification_hom (P : PresheafWithTransfers.{u + 1} k) :
    (nisnevichSheafify k).map (baseSectionsPresheafIso k P).hom ≫
      parameterSectionsSheafificationComparison k B P =
        ObjectProperty.homMk (baseSectionsPresheafIso k ((nisnevichSheafify k).obj P).obj).hom := by
  apply nisnevichSheafify_hom_ext k
  let A := nisnevichSheafify k
  let b := (baseSectionsPresheafIso k P).hom
  let η := toNisnevichSheafify k P
  let v := parameterSectionsSheafificationComparison k B P
  let η' := toNisnevichSheafify k (baseSections P)
  let c := (baseSectionsPresheafIso k (A.obj P).obj).hom
  change η ≫ ((A.map b).hom ≫ v.hom) = η ≫ c
  calc
    _ = (η ≫ (A.map b).hom) ≫ v.hom := (Category.assoc _ _ _).symm
    _ = (b ≫ η') ≫ v.hom := congrArg (· ≫ v.hom) (toNisnevichSheafify_naturality k b).symm
    _ = b ≫ withParameterMap η B := (Category.assoc _ _ _).trans
      (congrArg (b ≫ ·) (parameterSectionsSheafificationComparison_unit k B P))
    _ = _ := ((baseSectionsPresheafNatIso k).hom.naturality η).symm

/-- On a sheaf the original base-product projection gives the same
coefficient isomorphism. -/
def baseSectionsSheafIso : 𝟭 (SheafWithTransfers.{u + 1} k) ≅ parameterSectionsFunctor k B :=
  NatIso.ofComponents (fun F => ObjectProperty.isoMk _ (baseSectionsPresheafIso k F.obj))
    (fun {F H} f => by
      apply ObjectProperty.hom_ext
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext V
      exact (f.hom.hom.naturality
        ((Cor.graphFunctor k).map (productBaseIso V.unop.toSmoothSite).hom).op).symm)

/-- Original restriction to the unit section in ordinary base coordinates. -/
def torusSectionsUnitNatTrans : torusSectionsFunctor k ⟶ 𝟭 (SheafWithTransfers.{u + 1} k) :=
  (parameterSectionsFunctorTorusIso k).inv ≫
    parameterSectionsPullbackNatTrans k (SmoothSite.torusOne S) ≫ (baseSectionsSheafIso k).inv

/-- The original constant sections along the torus projection. -/
def torusSectionsConstantNatTrans :
    𝟭 (SheafWithTransfers.{u + 1} k) ⟶ torusSectionsFunctor k :=
  (baseSectionsSheafIso k).hom ≫ parameterSectionsPullbackNatTrans k (toBase G) ≫
    (parameterSectionsFunctorTorusIso k).hom

/-- Unit restriction retracts the original constant sections. -/
theorem torusSectionsConstant_comp_unit :
    torusSectionsConstantNatTrans k ≫ torusSectionsUnitNatTrans k = 𝟙 _ := by
  apply NatTrans.ext
  funext F
  apply ObjectProperty.hom_ext
  change (baseSectionsPresheafIso k F.obj).hom ≫ torusConstant F.obj ≫
      torusUnit F.obj ≫ (baseSectionsPresheafIso k F.obj).inv = 𝟙 F.obj
  rw [torusConstant_unit_assoc, Iso.hom_inv_id]

/-- Original unit restriction on the actual cochain complex. -/
def torusSectionsComplexUnitRestriction :
    (torusSectionsFunctor k).mapHomologicalComplex (.up ℤ) ⟶
      𝟭 (CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) :=
  (torusSectionsUnitNatTrans k).mapHomologicalComplex (.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom

variable [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

private def torusSectionsComplexUnitToDerived :
    torusSectionsComplexToDerived k ⟶
      DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (SheafWithTransfers.{u + 1} k)) :=
  Functor.whiskerRight (torusSectionsComplexUnitRestriction k) DerivedCategory.Q ≫
    DerivedCategory.Q.rightUnitor.inv

/-- Total derived evaluation at the original unit. -/
@[no_expose]
def torusSectionsDerivedUnitRestriction :
    torusSectionsDerivedFunctor k ⟶ 𝟭 (DerivedCategory (SheafWithTransfers.{u + 1} k)) :=
  (torusSectionsDerivedFunctor k).rightDerivedDesc (torusSectionsDerivedUnit k)
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ (torusSectionsComplexUnitToDerived k)

/-- The derived unit restriction agrees with the literal original restriction
on the cochain complex. -/
@[reassoc]
theorem torusSectionsDerivedUnitRestriction_app_Q_obj
    (K : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) :
    (torusSectionsDerivedUnit k).app K ≫
        (torusSectionsDerivedUnitRestriction k).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((torusSectionsComplexUnitRestriction k).app K) := by
  have h := (torusSectionsDerivedFunctor k).rightDerived_fac_app (torusSectionsDerivedUnit k)
    (HomologicalComplex.quasiIso _ (.up ℤ)) _ (torusSectionsComplexUnitToDerived k) K
  let r := DerivedCategory.Q.map ((torusSectionsComplexUnitRestriction k).app K)
  change (torusSectionsDerivedUnit k).app K ≫
      (torusSectionsDerivedUnitRestriction k).app (DerivedCategory.Q.obj K) =
    r ≫ 𝟙 (DerivedCategory.Q.obj K) at h
  exact h.trans (Category.comp_id r)

/-- Original constant sections on the cochain complex, followed by the
genuine total-derived unit, descend through the actual localization. -/
@[no_expose]
def torusSectionsDerivedConstant :
    𝟭 (DerivedCategory (SheafWithTransfers.{u + 1} k)) ⟶ torusSectionsDerivedFunctor k := by
  let Q : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ ⥤
    DerivedCategory (SheafWithTransfers.{u + 1} k) := DerivedCategory.Q
  let W := HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ)
  let c := (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv ≫
    (torusSectionsConstantNatTrans k).mapHomologicalComplex (.up ℤ)
  exact Localization.liftNatTrans Q W (Q ⋙ 𝟭 _) (Q ⋙ torusSectionsDerivedFunctor k) _ _
    (Q.rightUnitor.hom ≫ Functor.whiskerRight c Q ≫ torusSectionsDerivedUnit k)

@[reassoc]
theorem torusSectionsDerivedConstant_app_Q_obj
    (K : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) :
    (torusSectionsDerivedConstant k).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
        (((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv ≫
          (torusSectionsConstantNatTrans k).mapHomologicalComplex (.up ℤ)).app K) ≫
      (torusSectionsDerivedUnit k).app K := by
  unfold torusSectionsDerivedConstant
  rw [Localization.liftNatTrans_app]
  simp only [Localization.Lifting.compLeft_iso, Iso.refl_hom, Iso.refl_inv, NatTrans.comp_app,
    Functor.rightUnitor_hom_app, Functor.whiskerRight_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  exact Category.id_comp _

/-- The original constant and unit maps still split after deriving. -/
theorem torusSectionsDerivedConstant_comp_unit :
    torusSectionsDerivedConstant k ≫ torusSectionsDerivedUnitRestriction k = 𝟙 _ := by
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) (.up ℤ))
  intro K
  rw [NatTrans.comp_app, torusSectionsDerivedConstant_app_Q_obj_assoc,
    torusSectionsDerivedUnitRestriction_app_Q_obj, ← Functor.map_comp]
  have h : (((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv ≫
      (torusSectionsConstantNatTrans k).mapHomologicalComplex (.up ℤ)).app K) ≫
      (torusSectionsComplexUnitRestriction k).app K = 𝟙 K := by
    ext i : 1
    have h₀ := NatTrans.congr_app (torusSectionsConstant_comp_unit k) (K.X i)
    exact h₀
  rw [h, CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry.SheafWithTransfers
