/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Cofiber
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Collapse
public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Functor
import Colib.CategoryTheory.Limits.PointedSmashAdjunction
import Colib.CategoryTheory.Limits.PointedSmashBraiding
import Colib.CategoryTheory.Sites.Simplicial.ReducedCofiberExact
import Colib.CategoryTheory.Sites.Simplicial.SmashCylinder
import Colib.CategoryTheory.Sites.Simplicial.SmashMonomorphism
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# The actual Tate collapse after smashing with a pointed presheaf

Smash preserves the pointed pushout defining the original Tate sphere.
The resulting reduced-cochain sequence has the actual Laurent inclusion
and quotient as its two maps. Its middle term is contracted by the
original affine-line homotopy.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Sᵣ" => Spec R
local notation "Cᵣ" => SmoothSite Sᵣ
local notation "Jᵣ" => SmoothSite.nisnevichTopology Sᵣ
local notation "A" => liftedPointedAffineLine R
local notation "I" => affineLineInterval Sᵣ

attribute [local instance] Functor.functorCategoryMonoidalClosed

variable (X : PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R)))

private def smashLeftAdjunctionForCofiber :
    Under.smashLeftFunctor X ⊣ Under.pointedIhomFunctor X :=
  (Under.smashRightAdjunction X).ofNatIsoLeft (Under.smashRightIsoLeft X)

private theorem isZero_smash_point (P : PointedSimplicialPresheaf.{u + 1} Cᵣ) (hP : IsZero P) :
    IsZero (Under.smash X P) := by
  let F := Under.smashLeftFunctor X
  let : F.IsLeftAdjoint := (smashLeftAdjunctionForCofiber R X).isLeftAdjoint
  exact (hP.isInitial.isInitialObj F _).isZero

section ReducedCochains

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1}]

/-- Smashing with an arbitrary pointed presheaf retains the actual
short exact sequence of the Laurent open and the Tate quotient. -/
theorem exists_tateSmashReducedCochains_shortExact :
    let F := reducedCochains Cᵣ Jᵣ
    let U := uliftPointed.{u + 1, u} Cᵣ
    let i := F.map (Under.smashMap (𝟙 X) (U.map (pointedLaurentOpen R)))
    let q := F.map (Under.smashMap (𝟙 X) (U.map (toTateSphere R)))
    ∃ h : i ≫ q = 0, (ShortComplex.mk i q h).ShortExact := by
  let F := Under.smashLeftFunctor X
  let U := uliftPointed.{u + 1, u} Cᵣ
  let P := U.obj (point.{u} Cᵣ)
  let i := U.map (pointedLaurentOpen R)
  let : F.IsLeftAdjoint := (smashLeftAdjunctionForCofiber R X).isLeftAdjoint
  let : Mono i.right :=
    @mono_uliftPointed_map_right _ _ _ _ (pointedLaurentOpen R) (mono_pointedLaurentOpen_right R)
  let : Mono i := Under.mono_of_mono_right i
  let : Mono (F.map i) := mono_smashMap (𝟙 X) i
  let : Mono (Under.smashMap (𝟙 X) (U.map (pointedLaurentOpen R))).right :=
    Under.mono_right_of_mono (F.map i)
  have sq := F.map_isPushout (uliftPointed_map_isPushout.{u + 1, u} (tateSphere_isPushout R))
  have hP : IsZero (F.obj P) := isZero_smash_point R X P isZero_uliftPointed_point
  exact exists_reducedCochains_shortExact_of_isPushout_isZero Jᵣ sq hP

end ReducedCochains

/-- The affine-line contraction still contracts after smashing with any
pointed presheaf, for the original affine-line localization. -/
theorem isIso_toAffineLineHomotopyCategory_map_smashPointedAffineLineToPoint
    (X : PointedSimplicialPresheaf.{u + 1} (SmoothSite (Spec R))) :
    IsIso ((toAffineLineHomotopyCategory Sᵣ).map (toPoint Cᵣ (Under.smash X A))) := by
  let B := Under.smash A X
  let P := point.{u + 1} Cᵣ
  let Q := toAffineLineHomotopyCategory Sᵣ
  let F := Under.smashRightFunctor X
  let e := smashCylinderIso A X I
  let h : parameterizedCylinder B I ⟶ B := e.inv ≫ F.map (pointedAffineLineContraction R)
  let z := toPoint Cᵣ A ≫ fromPoint Cᵣ A
  have hzero : cylinderSection B (affineLineParameterEndpoint R 0) ≫ h = F.map z := by
    change cylinderSection B (affineLineParameterEndpoint R 0) ≫ e.inv ≫
      F.map (pointedAffineLineContraction R) = _
    have hh : F.map (cylinderSection A (affineLineParameterEndpoint R 0)) ≫ e.hom =
        cylinderSection B (affineLineParameterEndpoint R 0) :=
      smashMap_cylinderSection_smashCylinderIso_hom A X (affineLineParameterEndpoint R 0)
    rw [← hh, Category.assoc, e.hom_inv_id_assoc, ← F.map_comp,
      pointedAffineLineContraction_zero]
  have hone : cylinderSection B (affineLineParameterEndpoint R 1) ≫ h = 𝟙 B := by
    change cylinderSection B (affineLineParameterEndpoint R 1) ≫ e.inv ≫
      F.map (pointedAffineLineContraction R) = _
    have hh : F.map (cylinderSection A (affineLineParameterEndpoint R 1)) ≫ e.hom =
        cylinderSection B (affineLineParameterEndpoint R 1) :=
      smashMap_cylinderSection_smashCylinderIso_hom A X (affineLineParameterEndpoint R 1)
    rw [← hh, Category.assoc, e.hom_inv_id_assoc, ← F.map_comp,
      pointedAffineLineContraction_one, F.map_id]
    rfl
  have hz : F.map z = toPoint Cᵣ B ≫ fromPoint Cᵣ B := by
    let e' := Under.smashBraiding P X
    have hP : IsZero (F.obj P) :=
      (isZero_smash_point R X P (point_isZero Cᵣ)).of_iso e'
    have he : toPoint Cᵣ (F.obj P) ≫ fromPoint Cᵣ (F.obj P) = 𝟙 (F.obj P) :=
      hP.eq_of_src _ _
    calc
      _ = F.map (toPoint Cᵣ A) ≫ 𝟙 (F.obj P) ≫ F.map (fromPoint Cᵣ A) := by
        rw [Category.id_comp]
        exact F.map_comp _ _
      _ = F.map (toPoint Cᵣ A) ≫ (toPoint Cᵣ (F.obj P) ≫ fromPoint Cᵣ (F.obj P)) ≫
          F.map (fromPoint Cᵣ A) := by rw [he]
      _ = (F.map (toPoint Cᵣ A) ≫ toPoint Cᵣ (F.obj P)) ≫
          (fromPoint Cᵣ (F.obj P) ≫ F.map (fromPoint Cᵣ A)) := by
        simp only [Category.assoc]
      _ = _ := congrArg₂ (· ≫ ·) ((point_isZero Cᵣ).eq_of_tgt _ _)
        ((point_isZero Cᵣ).eq_of_src _ _)
  have hb : Q.map (toPoint Cᵣ B ≫ fromPoint Cᵣ B) = Q.map (𝟙 B) := by
    rw [← hz, ← hzero, ← hone]
    exact toIntervalHomotopyCategory_map_of_cylinder Cᵣ Jᵣ I h
      (affineLineParameterEndpoint R 0) (affineLineParameterEndpoint R 1)
  let p := toPoint Cᵣ B
  let s := fromPoint Cᵣ B
  let : IsIso (Q.map p) :=
    ⟨Q.map s, ((Q.map_comp _ _).symm.trans (hb.trans (Q.map_id _))),
      (Q.map_comp _ _).symm.trans ((Q.congr_map ((point_isZero Cᵣ).eq_of_src _ _)).trans
        (Q.map_id _))⟩
  have hc : (Under.smashBraiding X A).hom ≫ p = toPoint Cᵣ (Under.smash X A) :=
    (point_isZero Cᵣ).eq_of_tgt _ _
  rw [← hc, Q.map_comp]
  infer_instance

end AlgebraicGeometry.MotivicHomotopy
