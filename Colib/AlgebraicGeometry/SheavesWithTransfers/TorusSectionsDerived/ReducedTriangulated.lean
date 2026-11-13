/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.ReducedFunctor
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Triangulated structure of the reduced derived torus functor

Take the split kernel of the original unit in each transfer sheaf.
On a K-injective complex, the comparison with the derived kernel is
a retract of the original total-derived comparison. This gives the
triangulated structure for the same functor and the same inclusion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open Stacks.Injectives.KInjectiveResolution

universe u w

namespace AlgebraicGeometry.SheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]

local notation "c" => ComplexShape.up ℤ
local notation "B" => torusSectionsFunctor k
local notation "R" => torusSectionsDerivedFunctor k
local notation "N" => reducedTorusSectionsDerivedFunctor k

/-- The split kernel of unit restriction on the original transfer sheaves. -/
def reducedTorusSectionsFunctor :
    SheafWithTransfers.{u + 1} k ⥤ SheafWithTransfers.{u + 1} k where
  obj F := kernel ((torusSectionsUnitNatTrans k).app F)
  map {F G} f := kernel.lift _ (kernel.ι ((torusSectionsUnitNatTrans k).app F) ≫ (B).map f) (by
    rw [Category.assoc, (torusSectionsUnitNatTrans k).naturality f,
      ← Category.assoc, kernel.condition, zero_comp])
  map_id F := by
    apply (cancel_mono (kernel.ι ((torusSectionsUnitNatTrans k).app F))).1
    simp
  map_comp {F G H} f g := by
    apply (cancel_mono (kernel.ι ((torusSectionsUnitNatTrans k).app H))).1
    simp [Category.assoc, Functor.map_comp]

instance : (reducedTorusSectionsFunctor k).Additive where
  map_add {F G} f g := by
    apply (cancel_mono (kernel.ι ((torusSectionsUnitNatTrans k).app G))).1
    change kernel.lift _ (kernel.ι _ ≫ (B).map (f + g)) _ ≫ _ = _
    simp only [reducedTorusSectionsFunctor, Preadditive.add_comp, kernel.lift_ι, Functor.map_add,
      Preadditive.comp_add]

private def reducedInclusion : reducedTorusSectionsFunctor k ⟶ B where
  app F := kernel.ι ((torusSectionsUnitNatTrans k).app F)
  naturality _ _ _ := kernel.lift_ι _ _ _

private def reducedProjection : B ⟶ reducedTorusSectionsFunctor k where
  app F := splitKernelProjection ((torusSectionsConstantNatTrans k).app F)
    ((torusSectionsUnitNatTrans k).app F)
    (NatTrans.congr_app (torusSectionsConstant_comp_unit k) F)
  naturality F G f := by
    let u := torusSectionsUnitNatTrans k
    let s := torusSectionsConstantNatTrans k
    let j (K : SheafWithTransfers.{u + 1} k) : kernel (u.app K) ⟶ (B).obj K :=
      kernel.ι (u.app K)
    let r (K : SheafWithTransfers.{u + 1} k) : (B).obj K ⟶ kernel (u.app K) :=
      splitKernelProjection (s.app K) (u.app K) (NatTrans.congr_app
        (torusSectionsConstant_comp_unit k) K)
    let g : kernel (u.app F) ⟶ kernel (u.app G) := (reducedTorusSectionsFunctor k).map f
    have h (K : SheafWithTransfers.{u + 1} k) :
        r K ≫ j K = 𝟙 _ - u.app K ≫ s.app K := splitKernelProjection_ι _ _ _
    have hg : g ≫ j G = j F ≫ (B).map f := (reducedInclusion k).naturality f
    apply (cancel_mono (j G)).1
    change ((B).map f ≫ r G) ≫ j G = (r F ≫ g) ≫ j G
    calc
      _ = (B).map f ≫ (r G ≫ j G) := Category.assoc _ _ _
      _ = (B).map f ≫ (𝟙 _ - u.app G ≫ s.app G) := congrArg ((B).map f ≫ ·) (h G)
      _ = (𝟙 _ - u.app F ≫ s.app F) ≫ (B).map f := by
        rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp,
          ← Category.assoc ((B).map f), u.naturality f, Category.assoc, s.naturality f,
          Category.assoc]
      _ = (r F ≫ j F) ≫ (B).map f := congrArg (· ≫ (B).map f) (h F).symm
      _ = r F ≫ (j F ≫ (B).map f) := Category.assoc _ _ _
      _ = r F ≫ (g ≫ j G) := congrArg (r F ≫ ·) hg.symm
      _ = _ := (Category.assoc _ _ _).symm

omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] in
private theorem reducedInclusion_projection :
    reducedInclusion k ≫ reducedProjection k = 𝟙 (reducedTorusSectionsFunctor k) := by
  apply NatTrans.ext
  funext F
  let u := (torusSectionsUnitNatTrans k).app F
  let s := (torusSectionsConstantNatTrans k).app F
  let h : s ≫ u = 𝟙 F := NatTrans.congr_app (torusSectionsConstant_comp_unit k) F
  change kernel.ι u ≫ splitKernelProjection s u h = 𝟙 _
  apply (cancel_mono (kernel.ι u)).1
  rw [Category.assoc, splitKernelProjection_ι, Preadditive.comp_sub, Category.comp_id,
    ← Category.assoc, kernel.condition, zero_comp, sub_zero, Category.id_comp]

private abbrev reducedCochainInclusion :=
  (reducedInclusion k).mapHomologicalComplex c

private abbrev reducedCochainProjection :=
  (reducedProjection k).mapHomologicalComplex c

omit [HasDerivedCategory (SheafWithTransfers.{u + 1} k)] in
private theorem reducedCochainInclusion_projection (I : CochainComplex
    (SheafWithTransfers.{u + 1} k) ℤ) :
    (reducedCochainInclusion k).app I ≫ (reducedCochainProjection k).app I = 𝟙 _ := by
  apply HomologicalComplex.hom_f_injective
  funext n
  exact NatTrans.congr_app (reducedInclusion_projection k) (I.X n)

/-- The derived comparison for the original split kernel. -/
@[no_expose]
def reducedTorusSectionsDerivedUnit :
    (reducedTorusSectionsFunctor k).mapHomologicalComplex c ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ N :=
  Functor.whiskerRight (reducedCochainInclusion k) DerivedCategory.Q ≫
    torusSectionsDerivedUnit k ≫
      Functor.whiskerLeft DerivedCategory.Q (reducedTorusSectionsDerivedProjection k)

private def reducedDerivedUnit_retract (I : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ) :
    RetractArrow ((reducedTorusSectionsDerivedUnit k).app I)
      ((torusSectionsDerivedUnit k).app I) := by
  let A := SheafWithTransfers.{u + 1} k
  let Q := DerivedCategory.Q (C := A)
  let r := (torusSectionsUnitNatTrans k).mapHomologicalComplex c
  let s := (torusSectionsConstantNatTrans k).mapHomologicalComplex c
  let e := Functor.mapHomologicalComplexIdIso A c
  let P := (Q).map ((reducedCochainProjection k).app I)
  let J := (Q).map ((reducedCochainInclusion k).app I)
  let φ : (Q).obj (((B).mapHomologicalComplex c).obj I) ⟶ (R).obj (Q.obj I) :=
    (torusSectionsDerivedUnit k).app I
  let ρ := (reducedTorusSectionsDerivedProjection k).app ((Q).obj I)
  let ι := (reducedTorusSectionsDerivedInclusion k).app ((Q).obj I)
  have hJ : J ≫ P = 𝟙 _ := by
    rw [← (Q).map_comp, reducedCochainInclusion_projection, (Q).map_id]
  have hp : P ≫ J = 𝟙 _ - (Q).map ((r ≫ e.hom).app I) ≫
      (Q).map ((e.inv ≫ s).app I) := by
    rw [← (Q).map_comp, ← (Q).map_comp, ← (Q).map_id, ← (Q).map_sub]
    congr 1
    apply HomologicalComplex.hom_f_injective
    funext n
    let hn := NatTrans.congr_app (torusSectionsConstant_comp_unit k) (I.X n)
    change splitKernelProjection _ _ hn ≫ kernel.ι _ = 𝟙 ((B).obj (I.X n)) -
      ((torusSectionsUnitNatTrans k).app (I.X n) ≫ 𝟙 _) ≫
        (𝟙 _ ≫ (torusSectionsConstantNatTrans k).app (I.X n))
    rw [splitKernelProjection_ι, Category.comp_id, Category.id_comp]
  let a := Q.map ((r ≫ e.hom).app I)
  let b := Q.map ((e.inv ≫ s).app I)
  let x := (torusSectionsDerivedUnitRestriction k).app (Q.obj I)
  let y := (torusSectionsDerivedConstant k).app (Q.obj I)
  have ha : φ ≫ x = a := torusSectionsDerivedUnitRestriction_app_Q_obj k I
  have hb : y = b ≫ φ := torusSectionsDerivedConstant_app_Q_obj k I
  have hρ : ρ ≫ ι = 𝟙 _ - x ≫ y := reducedTorusSectionsDerivedProjection_inclusion k _
  have hφ : P ≫ J ≫ φ = φ ≫ ρ ≫ ι := by
    calc
      _ = (P ≫ J) ≫ φ := (Category.assoc _ _ _).symm
      _ = (𝟙 _ - a ≫ b) ≫ φ := congrArg (· ≫ φ) hp
      _ = φ - a ≫ b ≫ φ := by
        rw [Preadditive.sub_comp, Category.id_comp, Category.assoc]
      _ = φ - (φ ≫ x) ≫ y := by rw [ha, hb]
      _ = φ ≫ (𝟙 _ - x ≫ y) := by
        rw [Preadditive.comp_sub, Category.comp_id, Category.assoc]
      _ = φ ≫ ρ ≫ ι := congrArg (φ ≫ ·) hρ.symm
  refine
    { i := Arrow.homMk J ι ?_
      r := Arrow.homMk P ρ ?_
      retract := ?_ }
  · change J ≫ φ = (J ≫ φ ≫ ρ) ≫ ι
    symm
    calc
      _ = J ≫ (φ ≫ ρ ≫ ι) := by simp only [Category.assoc]
      _ = J ≫ P ≫ J ≫ φ := congrArg (J ≫ ·) hφ.symm
      _ = _ := by rw [← Category.assoc J P, hJ, Category.id_comp]
  · change P ≫ (J ≫ φ ≫ ρ) = φ ≫ ρ
    have hh : ι ≫ ρ = 𝟙 _ := reducedTorusSectionsDerivedInclusion_projection k _
    calc
      _ = (P ≫ J ≫ φ) ≫ ρ := by simp only [Category.assoc]
      _ = (φ ≫ ρ ≫ ι) ≫ ρ := congrArg (· ≫ ρ) hφ
      _ = φ ≫ ρ ≫ (ι ≫ ρ) := by simp only [Category.assoc]
      _ = _ := by rw [hh, Category.comp_id]
  · ext
    · exact hJ
    · exact reducedTorusSectionsDerivedInclusion_projection k _

instance : (N).IsRightDerivedFunctor (reducedTorusSectionsDerivedUnit k)
    (HomologicalComplex.quasiIso (SheafWithTransfers.{u + 1} k) c) := by
  let Q := DerivedCategory.Q (C := SheafWithTransfers.{u + 1} k)
  apply (isRightDerivedFunctor_iff_isIso_app_of_isKInjective (Q) _ _
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (reducedTorusSectionsFunctor k))).2
  intro I hI
  have h := isIso_app_of_isKInjective (Q) (R) (torusSectionsDerivedUnit k)
    (invertsQuasiIso_mapHomologicalComplex_comp_Q (B)) I hI
  exact (MorphismProperty.isomorphisms _).of_retract (reducedDerivedUnit_retract k I) h

instance : (N).CommShift ℤ :=
  Stacks.Injectives.commShiftOfComplexUnit (reducedTorusSectionsFunctor k) (N)
    (reducedTorusSectionsDerivedUnit k)

instance : (N).IsTriangulated :=
  Stacks.Injectives.isTriangulated_of_complexUnit (reducedTorusSectionsFunctor k) (N)
    (reducedTorusSectionsDerivedUnit k)

end AlgebraicGeometry.SheafWithTransfers
