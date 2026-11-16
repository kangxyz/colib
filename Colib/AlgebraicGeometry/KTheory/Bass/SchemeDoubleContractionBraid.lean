/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeDoubleContractionSwap
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseBraid

/-!
# The braid relation on the original triple Bass quotient

Both adjacent swaps are the independently descended literal Laurent-variable swap.
Their braid relation is checked after the epimorphic composite of the three original
Laurent quotient maps, using the geometric braid relation on nested products.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
universe u w
namespace AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open KTheory.Bass.TwoChart

local notation "C" => contraction (NatTrans.op plus) (NatTrans.op minus)
local notation "CM" => contractionMap (NatTrans.op plus) (NatTrans.op minus)
local notation "L" => laurentFunctor.op
local notation "θ" => contractionπ (NatTrans.op plus) (NatTrans.op minus)
local notation "Q₂" => doubleContractionπ (NatTrans.op plus) (NatTrans.op minus)

/-- The natural automorphism retains the independently descended original component. -/
@[simp]
theorem doubleContractionSwapNatIso_hom_app
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (doubleContractionSwapNatIso F).hom.app X = doubleContractionSwap F X := rfl

/-- The literal Laurent-variable swaps obey the cubic braid relation. -/
theorem doubleLaurentOppositeSwap_braid (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (L).map (doubleLaurentOppositeSwap.hom.app X) ≫
        doubleLaurentOppositeSwap.hom.app ((L).obj X) ≫
          (L).map (doubleLaurentOppositeSwap.hom.app X) =
      doubleLaurentOppositeSwap.hom.app ((L).obj X) ≫
        (L).map (doubleLaurentOppositeSwap.hom.app X) ≫
          doubleLaurentOppositeSwap.hom.app ((L).obj X) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  let q := PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ))
  change ((baseProductFunctor q).map (baseProductSwapMap q q X.unop.obj) ≫
      baseProductSwapMap q q ((baseProductFunctor q).obj X.unop.obj)) ≫
        (baseProductFunctor q).map (baseProductSwapMap q q X.unop.obj) =
    (baseProductSwapMap q q ((baseProductFunctor q).obj X.unop.obj) ≫
      (baseProductFunctor q).map (baseProductSwapMap q q X.unop.obj)) ≫
        baseProductSwapMap q q ((baseProductFunctor q).obj X.unop.obj)
  simpa only [Category.assoc] using baseProductSwapMap_braid q q q X.unop.obj

/-- The three original Laurent projections, with their original order unchanged. -/
def tripleContractionπ (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    F.obj ((L).obj ((L).obj ((L).obj X))) ⟶ (C (C (C F))).obj X :=
  (θ F).app ((L).obj ((L).obj X)) ≫ Q₂ (C F) X

instance tripleContractionπ_epi (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) : Epi (tripleContractionπ F X) := by
  unfold tripleContractionπ
  infer_instance

/-- The outer adjacent quotient swap acts on original representatives by `L(σ)`. -/
@[reassoc]
theorem tripleContractionπ_outer_swap
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    tripleContractionπ F X ≫ doubleContractionSwap (C F) X =
      F.map ((L).map (doubleLaurentOppositeSwap.hom.app X)) ≫ tripleContractionπ F X := by
  unfold tripleContractionπ
  rw [Category.assoc, doubleContractionπ_swap]
  have h := (θ F).naturality (doubleLaurentOppositeSwap.hom.app X)
  simp only [Functor.comp_map, Functor.comp_obj] at h
  rw [← Category.assoc, ← h, Category.assoc]

/-- The inner adjacent quotient swap acts by the literal swap at the Laurent base. -/
@[reassoc]
theorem tripleContractionπ_inner_swap
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    tripleContractionπ F X ≫ (CM (doubleContractionSwapNatIso F).hom).app X =
      F.map (doubleLaurentOppositeSwap.hom.app ((L).obj X)) ≫ tripleContractionπ F X := by
  simp only [tripleContractionπ, doubleContractionπ, Category.assoc, contractionMap_π,
    doubleContractionSwapNatIso_hom_app]
  simpa only [doubleContractionπ, Category.assoc] using
    doubleContractionπ_swap_assoc F ((L).obj X) ((θ (C (C F))).app X)

/-- The two actual adjacent swaps on the triple original quotient satisfy the braid relation. -/
theorem doubleContractionSwap_braid
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (doubleContractionSwapNatIso (C F)).hom ≫ CM (doubleContractionSwapNatIso F).hom ≫
        (doubleContractionSwapNatIso (C F)).hom =
      CM (doubleContractionSwapNatIso F).hom ≫ (doubleContractionSwapNatIso (C F)).hom ≫
        CM (doubleContractionSwapNatIso F).hom := by
  apply NatTrans.ext
  funext X
  apply (cancel_epi (tripleContractionπ F X)).1
  simp only [NatTrans.comp_app, doubleContractionSwapNatIso_hom_app]
  simp only [tripleContractionπ_outer_swap_assoc, tripleContractionπ_inner_swap_assoc,
    tripleContractionπ_outer_swap, tripleContractionπ_inner_swap]
  simp only [← Category.assoc, ← F.map_comp]
  simp only [Category.assoc]
  rw [doubleLaurentOppositeSwap_braid]

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
