/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Acyclic
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedFunctor
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty

/-!
# Reduced derived torus sections of a single transfer sheaf

For a homotopy invariant coefficient, the total derived comparison unit
is invertible on its single complex. The kernel of unit evaluation is
the single complex of the original Laurent contraction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

set_option hygiene false in
set_option quotPrecheck false in
local notation "NST" => SheafWithTransfers.{u + 1} k
local notation "B" => torusSectionsFunctor k
local notation "b" => baseSectionsPresheafIso k

variable {F G : NST} (hF : F.obj.IsA1Invariant) (hG : G.obj.IsA1Invariant)

/-- The contraction map uses the original morphism of Laurent quotient presheaves. -/
def contractionMap (f : F ⟶ G) : contraction F hF ⟶ contraction G hG :=
  ObjectProperty.homMk (PresheafWithTransfers.contractionMap f.hom)

private def contractionQuotient (F : NST) (hF : F.obj.IsA1Invariant) :
    (B).obj F ⟶ contraction F hF :=
  ObjectProperty.homMk (toContraction F.obj)

private def contractionInclusion (F : NST) (hF : F.obj.IsA1Invariant) :
    contraction F hF ⟶ (B).obj F :=
  ObjectProperty.homMk ((contractionIsoKernel F.obj hF).hom ≫ kernel.ι (torusUnit F.obj))

@[reassoc]
private theorem contractionQuotient_naturality (f : F ⟶ G) :
    (B).map f ≫ contractionQuotient k G hG =
      contractionQuotient k F hF ≫ contractionMap k hF hG f := by
  apply ObjectProperty.hom_ext
  exact (toContraction_map f.hom).symm

private theorem torusSectionsUnitNatTrans_hom (F : NST) :
    ((torusSectionsUnitNatTrans k).app F).hom = torusUnit F.obj ≫ ((b) F.obj).inv := by
  change 𝟙 _ ≫ torusUnit F.obj ≫ ((b) F.obj).inv = _
  rw [Category.id_comp]

private theorem torusSectionsConstantNatTrans_hom (F : NST) :
    ((torusSectionsConstantNatTrans k).app F).hom = ((b) F.obj).hom ≫ torusConstant F.obj := by
  change ((b) F.obj).hom ≫ torusConstant F.obj ≫ 𝟙 _ = _
  rw [Category.comp_id]

@[reassoc]
private theorem contractionInclusion_unit :
    contractionInclusion k F hF ≫ (torusSectionsUnitNatTrans k).app F = 0 := by
  apply ObjectProperty.hom_ext
  change ((contractionIsoKernel F.obj hF).hom ≫ kernel.ι (torusUnit F.obj)) ≫
    ((torusSectionsUnitNatTrans k).app F).hom = 0
  simp only [torusSectionsUnitNatTrans_hom, Category.assoc, kernel.condition_assoc,
    zero_comp, comp_zero]

private theorem contractionInclusion_quotient :
    contractionInclusion k F hF ≫ contractionQuotient k F hF = 𝟙 _ := by
  apply ObjectProperty.hom_ext
  change ((contractionIsoKernel F.obj hF).hom ≫ kernel.ι (torusUnit F.obj)) ≫
    toContraction F.obj = 𝟙 _
  exact (Category.assoc _ _ _).trans (contractionIsoKernel F.obj hF).hom_inv_id

private theorem contractionQuotient_inclusion :
    contractionQuotient k F hF ≫ contractionInclusion k F hF =
      𝟙 _ - (torusSectionsUnitNatTrans k).app F ≫ (torusSectionsConstantNatTrans k).app F := by
  apply ObjectProperty.hom_ext
  change toContraction F.obj ≫ (contractionIsoKernel F.obj hF).hom ≫
      kernel.ι (torusUnit F.obj) =
    𝟙 _ - ((torusSectionsUnitNatTrans k).app F).hom ≫
      ((torusSectionsConstantNatTrans k).app F).hom
  rw [contractionIsoKernel_hom_projection, torusSectionsUnitNatTrans_hom,
    torusSectionsConstantNatTrans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

variable [PerfectField k] [HasDerivedCategory.{w} NST]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "S" => DerivedCategory.singleFunctor NST 0
local notation "SingleComplex" => CochainComplex.singleFunctor NST 0
set_option quotPrecheck false in
local notation "Q" => DerivedCategory.Q (C := NST)
local notation "R" => torusSectionsDerivedFunctor k
local notation "D" => reducedTorusSectionsDerivedFunctor k
local notation "s" => HomologicalComplex.singleMapHomologicalComplex (B) (ComplexShape.up ℤ) (0 : ℤ)

private theorem isIso_torusSectionsDerivedUnit_single (F : NST) (hF : F.obj.IsA1Invariant) :
    IsIso ((torusSectionsDerivedUnit k).app ((SingleComplex).obj F)) := by
  apply isIso_torusSectionsDerivedUnit_app_of_rightAcyclic k
    ((SingleComplex).obj F) ⟨0, inferInstance⟩
  intro i
  apply torusSectionsFunctor_rightAcyclic_of_perfect k
  by_cases hi : i = 0
  · subst i
    exact hF.of_iso ((SheafWithTransfers.forget k).mapIso
      (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ) F).symm)
  · exact isA1Invariant_of_isZero ((SheafWithTransfers.forget k).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) (0 : ℤ) F i hi))

/-- The actual derived torus comparison unit on a single homotopy invariant coefficient. -/
@[no_expose]
def torusSectionsSingleComparison (F : NST) (hF : F.obj.IsA1Invariant) :
    (S).obj ((B).obj F) ≅ (R).obj ((S).obj F) := by
  let : IsIso ((torusSectionsDerivedUnit k).app ((SingleComplex).obj F)) :=
    isIso_torusSectionsDerivedUnit_single k F hF
  exact (Q).mapIso ((s).app F).symm ≪≫
    asIso ((torusSectionsDerivedUnit k).app ((SingleComplex).obj F))

/-- The single-coefficient comparison uses the original coefficient maps. -/
@[reassoc]
theorem torusSectionsSingleComparison_naturality (f : F ⟶ G) :
    (S).map ((B).map f) ≫ (torusSectionsSingleComparison k G hG).hom =
      (torusSectionsSingleComparison k F hF).hom ≫ (R).map ((S).map f) := by
  let v := torusSectionsDerivedUnit k
  have hs : (SingleComplex).map ((B).map f) ≫ (s).inv.app G =
      (s).inv.app F ≫ ((B).mapHomologicalComplex (.up ℤ)).map ((SingleComplex).map f) :=
    (s).inv.naturality f
  have hv := v.naturality ((SingleComplex).map f)
  change (Q).map ((SingleComplex).map ((B).map f)) ≫
      (Q).map ((s).inv.app G) ≫ v.app ((SingleComplex).obj G) =
    ((Q).map ((s).inv.app F) ≫ v.app ((SingleComplex).obj F)) ≫
      (R).map ((Q).map ((SingleComplex).map f))
  rw [Category.assoc, ← (Q).map_comp_assoc, hs, (Q).map_comp, Category.assoc]
  exact congrArg ((Q).map ((s).inv.app F) ≫ ·) hv

/-- Unit evaluation agrees with the original torus unit on the single coefficient. -/
@[reassoc]
theorem torusSectionsSingleComparison_unit (F : NST) (hF : F.obj.IsA1Invariant) :
    (torusSectionsSingleComparison k F hF).hom ≫
      (torusSectionsDerivedUnitRestriction k).app ((S).obj F) =
      (S).map ((torusSectionsUnitNatTrans k).app F) := by
  let η := torusSectionsUnitNatTrans k
  let v := torusSectionsDerivedUnit k
  have h := HomologicalComplex.natTransMapHomologicalComplex_app_single_obj
    η (.up ℤ) (0 : ℤ) F
  have h' : (torusSectionsComplexUnitRestriction k).app ((SingleComplex).obj F) =
      (s).hom.app F ≫ (SingleComplex).map (η.app F) := by
    change (η.mapHomologicalComplex (.up ℤ)).app ((SingleComplex).obj F) ≫
        (Functor.mapHomologicalComplexIdIso NST (.up ℤ)).hom.app ((SingleComplex).obj F) = _
    rw [h, Category.assoc, Category.assoc,
      HomologicalComplex.singleMapHomologicalComplex_id_inv_app, Iso.inv_hom_id_app]
    change (s).hom.app F ≫ (SingleComplex).map (η.app F) ≫
      𝟙 ((SingleComplex).obj F) = _
    exact congrArg ((s).hom.app F ≫ ·) (Category.comp_id ((SingleComplex).map (η.app F)))
  change ((Q).map ((s).inv.app F) ≫ v.app ((SingleComplex).obj F)) ≫
      (torusSectionsDerivedUnitRestriction k).app ((Q).obj ((SingleComplex).obj F)) =
    (Q).map ((SingleComplex).map (η.app F))
  rw [Category.assoc, torusSectionsDerivedUnitRestriction_app_Q_obj, h',
    ← (Q).map_comp, Iso.inv_hom_id_app_assoc]

/-- Reduced total derived torus sections of an HI sheaf are its contraction in degree zero. -/
@[no_expose]
def reducedTorusSectionsDerivedContractionIso (F : NST) (hF : F.obj.IsA1Invariant) :
    (D).obj ((S).obj F) ≅ (S).obj (contraction F hF) := by
  let e := torusSectionsSingleComparison k F hF
  let u := (torusSectionsDerivedUnitRestriction k).app ((S).obj F)
  let i := contractionInclusion k F hF
  let q := contractionQuotient k F hF
  let r := (torusSectionsUnitNatTrans k).app F
  have he : e.hom ≫ u = (S).map r := torusSectionsSingleComparison_unit k F hF
  have he' : u = e.inv ≫ (S).map r := by rw [← he, Iso.inv_hom_id_assoc]
  have hi : (S).map i ≫ e.hom ≫ u = 0 := by
    rw [he, ← (S).map_comp, contractionInclusion_unit, (S).map_zero]
  change kernel u ≅ (S).obj (contraction F hF)
  refine ⟨kernel.ι u ≫ e.inv ≫ (S).map q, kernel.lift u ((S).map i ≫ e.hom) (?_), ?_, ?_⟩
  · simpa only [Category.assoc] using hi
  · apply (cancel_mono (kernel.ι u)).mp
    simp only [Category.assoc, kernel.lift_ι, Category.id_comp]
    rw [← (S).map_comp_assoc, contractionQuotient_inclusion, (S).map_sub, (S).map_id,
      (S).map_comp]
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc e.inv ((S).map r), ← he', kernel.condition_assoc, zero_comp, sub_zero]
  · have h' : i ≫ q = 𝟙 _ := contractionInclusion_quotient k hF
    simp only [Category.assoc, kernel.lift_ι_assoc, Iso.hom_inv_id_assoc, ← (S).map_comp]
    rw [h', (S).map_id]

/-- The contraction comparison is natural in the original coefficient morphism. -/
@[reassoc]
theorem reducedTorusSectionsDerivedContractionIso_naturality (f : F ⟶ G) :
    (D).map ((S).map f) ≫ (reducedTorusSectionsDerivedContractionIso k G hG).hom =
      (reducedTorusSectionsDerivedContractionIso k F hF).hom ≫
        (S).map (contractionMap k hF hG f) := by
  let eF := torusSectionsSingleComparison k F hF
  let eG := torusSectionsSingleComparison k G hG
  let uF := (torusSectionsDerivedUnitRestriction k).app ((S).obj F)
  let uG := (torusSectionsDerivedUnitRestriction k).app ((S).obj G)
  have h : (R).map ((S).map f) ≫ eG.inv =
      eF.inv ≫ (S).map ((B).map f) := by
    rw [← cancel_epi eF.hom, Iso.hom_inv_id_assoc, ← Category.assoc,
      ← torusSectionsSingleComparison_naturality k hF hG f, Category.assoc, eG.hom_inv_id,
      Category.comp_id]
  change (D).map ((S).map f) ≫ kernel.ι uG ≫ eG.inv ≫ (S).map (contractionQuotient k G hG) =
    (kernel.ι uF ≫ eF.inv ≫ (S).map (contractionQuotient k F hF)) ≫
      (S).map (contractionMap k hF hG f)
  have hι : (D).map ((S).map f) ≫ kernel.ι uG = kernel.ι uF ≫ (R).map ((S).map f) :=
    reducedTorusSectionsDerivedMap_ι k ((S).map f)
  rw [← Category.assoc ((D).map _), hι, Category.assoc,
    reassoc_of% h, Category.assoc, Category.assoc, ← (S).map_comp,
    contractionQuotient_naturality, (S).map_comp]

end AlgebraicGeometry.SheafWithTransfers
