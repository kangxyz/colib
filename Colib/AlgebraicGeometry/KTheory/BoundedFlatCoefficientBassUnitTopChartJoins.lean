/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTopCharts
import Mathlib.Tactic.FinCases

/-! The complete split unit references in the original signed Bass identity top joins.
Adapted from `OriginalUnitSquareSimplex.lean` and `CoefficientPolynomialSpanUnitNodes.lean`
at Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

theorem unit_composite (X : Scheme.{u}) :
    (unitGeometric X).hom ≫ (unitNormalization X).hom =
      (boundedAboveFlatPerfectNormalizedPullbackIdIso X).hom := by
  simp [unitGeometric, unitNormalization, boundedAboveFlatPerfectNormalizedPullbackIdIso,
    Category.assoc]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem left_second_composite :
    (leftSecondGeometric f).hom ≫ (leftSecondNormalization f).hom =
      (leftSecond f).hom := by
  apply NatTrans.ext
  funext A
  simp only [leftSecondGeometric, leftSecondNormalization, leftSecond,
    boundedAboveFlatPerfectNormalizedLeftUnitSecond, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    Iso.trans_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    leftUnitor_hom_app]
  rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app, unit_composite]
  exact congrArg (fun k ↦ AsSmall.up.map k) (Category.comp_id _).symm

theorem two_routes :
    (rightFirst f).hom ≫ (rightSecond f).hom =
      (leftFirst f).hom ≫ (leftSecond f).hom := by
  have hh := congrArg
    (fun η ↦ whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (boundedAboveFlatPerfectNormalizedUnitRoutes_equation f)
  simpa only [rightFirst, rightSecond, leftFirst, leftSecond, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_comp, whiskerRight_comp] using hh

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTopCharts

open BoundedFlatPerfectOriginalUnitSquareSimplex

local notation "unitMiddleNodes" => BoundedFlatCoefficientBassUnitTopMiddle.nodes
local notation "idFirst" => BoundedFlatPerfectIdentitySimplex.first
local notation "idRefs" => BoundedFlatPerfectIdentitySimplex.identityReferences
local notation "idSecond" => BoundedFlatPerfectIdentitySimplex.second
local notation "bassProjNodes" => BoundedFlatCoefficientBassProjectionPath.nodes
local notation "pairRef" => BoundedFlatCoefficientBassUnitTerminalNodes.middlePairReference

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The exact original projection reference is natural in the base identity normalization. -/
theorem product_reference (i : Fin 3) (j : Fin 5) :
    pairRef P a i j = pairRef P a 0 j ≪≫
      isoWhiskerRight (idRefs (space (op P, a)) i)
        (bassProjNodes P a j).1.hom.toFunctor := by
  unfold BoundedFlatCoefficientBassUnitTerminalNodes.middlePairReference
  rw [CommonReferenceProduct.composition_pair_iso_other
    (idRefs (space (op P, a)) i) (bassProjNodes P a j).2,
    CommonReferenceProduct.composition_pair_iso_other
      (idRefs (space (op P, a)) 0) (bassProjNodes P a j).2]
  change _ = (_ ≪≫ isoWhiskerRight (Iso.refl _) _) ≪≫ _
  rw [isoWhiskerRight_refl, Iso.trans_refl]

theorem plus_six : plusNodes P a 6 = unitMiddleNodes P a 7 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerRight
    (leftFirst (polynomialProjection P a) ≪≫ leftSecondGeometric (polynomialProjection P a))
    (sourceMap (laurentPlus P a)).hom.toFunctor).hom = (pairRef P a 1 2).hom
  rw [product_reference]
  simp only [plusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv, whiskerRight_comp, Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rfl

theorem minus_six : minusNodes P a 6 = unitMiddleNodes P a 9 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerRight
    (leftFirst (polynomialProjection P a) ≪≫ leftSecondGeometric (polynomialProjection P a))
    (sourceMap (laurentMinus P a)).hom.toFunctor).hom = (pairRef P a 1 4).hom
  rw [product_reference]
  simp only [minusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv, whiskerRight_comp, Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rfl

private theorem left_second_whisker {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B) :
    whiskerRight (leftSecond p).hom (sourceMap q).hom.toFunctor =
      whiskerRight ((idFirst A).hom ≫ (idSecond A).hom)
        (sourceMap p ≫ sourceMap q).hom.toFunctor := by
  rw [← left_second_composite]
  simp only [whiskerRight_comp]
  rfl

theorem plus_seven : plusNodes P a 7 = unitMiddleNodes P a 12 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (plusSourceIso P a ≪≫ isoWhiskerRight
    (rightFirst (polynomialProjection P a) ≪≫ rightSecond (polynomialProjection P a))
    (sourceMap (laurentPlus P a)).hom.toFunctor).hom = (pairRef P a 2 2).hom
  rw [product_reference]
  simp only [plusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv]
  rw [two_routes, whiskerRight_comp]
  simp only [Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rw [left_second_whisker]
  rfl

theorem minus_seven : minusNodes P a 7 = unitMiddleNodes P a 14 := by
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  change (minusSourceIso P a ≪≫ isoWhiskerRight
    (rightFirst (polynomialProjection P a) ≪≫ rightSecond (polynomialProjection P a))
    (sourceMap (laurentMinus P a)).hom.toFunctor).hom = (pairRef P a 2 4).hom
  rw [product_reference]
  simp only [minusSourceIso, Iso.trans_hom, Iso.symm_hom, isoWhiskerRight_hom,
    isoWhiskerRight_inv]
  rw [two_routes, whiskerRight_comp]
  simp only [Category.assoc]
  simp only [← whiskerRight_comp, Iso.inv_hom_id_assoc]
  rw [left_second_whisker]
  rfl

/-- All three positive shared vertices agree as dependent nodes, including reference transport. -/
theorem plus_shared (i : Fin 3) :
    plusNodes P a ⟨5 + i.val, by omega⟩ =
      unitMiddleNodes P a ⟨5 * i.val + 2, by omega⟩ := by
  fin_cases i
  · exact plus_five P a
  · exact plus_six P a
  · exact plus_seven P a

/-- All three negative shared vertices retain the actual inverse-chart reference. -/
theorem minus_shared (i : Fin 3) :
    minusNodes P a ⟨5 + i.val, by omega⟩ =
      unitMiddleNodes P a ⟨5 * i.val + 4, by omega⟩ := by
  fin_cases i
  · exact minus_five P a
  · exact minus_six P a
  · exact minus_seven P a

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTopCharts
