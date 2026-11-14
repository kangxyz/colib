/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeDoubleContractionBraid

/-!
# Fixed-factor transport of the original double-quotient swap

Iterating the actual independent-product comparison transports the two original
Bass quotients. Its representative contains both original Laurent interchanges.
The geometric three-factor braid proves that this transport intertwines the
independently descended Laurent-variable swaps. Consequently a sign equality
only at the fixed product base suffices; no global sign premise is required.
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
local notation "CF" => contractionFunctor (NatTrans.op plus) (NatTrans.op minus)
local notation "L" => laurentFunctor.op
local notation "θ" => contractionπ (NatTrans.op plus) (NatTrans.op minus)
local notation "Q₂" => doubleContractionπ (NatTrans.op plus) (NatTrans.op minus)

variable {S : Scheme.{u}} (q : S ⟶ Spec (CommRingCat.of (ULift.{u} ℤ))) [QuasiCompact q]

/-- The two literal interchanges moving a fixed factor past both Laurent factors. -/
def productDoubleLaurentOppositeMap (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (qcBaseProductFunctor q).op.obj ((L).obj ((L).obj X)) ⟶
      (L).obj ((L).obj ((qcBaseProductFunctor q).op.obj X)) :=
  (productLaurentOppositeIso q).hom.app ((L).obj X) ≫
    (L).map ((productLaurentOppositeIso q).hom.app X)

/-- Moving the fixed factor past both variables commutes with their actual swap. -/
@[reassoc]
theorem productDoubleLaurentOppositeMap_swap (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (qcBaseProductFunctor q).op.map (doubleLaurentOppositeSwap.hom.app X) ≫
        productDoubleLaurentOppositeMap q X =
      productDoubleLaurentOppositeMap q X ≫
        doubleLaurentOppositeSwap.hom.app ((qcBaseProductFunctor q).op.obj X) := by
  unfold productDoubleLaurentOppositeMap
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  let l := PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ))
  change ((baseProductFunctor l).map (baseProductSwapMap q l X.unop.obj) ≫
      baseProductSwapMap q l ((baseProductFunctor l).obj X.unop.obj)) ≫
        (baseProductFunctor q).map (baseProductSwapMap l l X.unop.obj) =
    (baseProductSwapMap l l ((baseProductFunctor q).obj X.unop.obj) ≫
      (baseProductFunctor l).map (baseProductSwapMap q l X.unop.obj)) ≫
        baseProductSwapMap q l ((baseProductFunctor l).obj X.unop.obj)
  simpa only [Category.assoc] using baseProductSwapMap_braid q l l X.unop.obj

/-- The iterated actual product transport, retaining the order of both quotients. -/
def productDoubleContractionTransportIso
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    C (C ((qcBaseProductFunctor q).op ⋙ F)) ≅
      (qcBaseProductFunctor q).op ⋙ C (C F) :=
  (CF).mapIso (productContractionTransportIso q F) ≪≫
    productContractionTransportIso q (C F)

/-- Both original quotient projections recover the two literal Laurent interchanges. -/
@[reassoc]
theorem productDoubleContractionTransportIso_π
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    Q₂ ((qcBaseProductFunctor q).op ⋙ F) X ≫
        (productDoubleContractionTransportIso q F).hom.app X =
      F.map (productDoubleLaurentOppositeMap q X) ≫
        Q₂ F ((qcBaseProductFunctor q).op.obj X) := by
  change ((θ ((qcBaseProductFunctor q).op ⋙ F)).app ((L).obj X) ≫
      (θ (C ((qcBaseProductFunctor q).op ⋙ F))).app X) ≫
        ((CM (productContractionTransportIso q F).hom).app X ≫
          (productContractionTransportIso q (C F)).hom.app X) = _
  simp only [Category.assoc, contractionMap_π_assoc,
    productContractionTransportIso_π_assoc, productContractionTransportIso_π]
  have h := (θ F).naturality ((productLaurentOppositeIso q).hom.app X)
  simp only [Functor.comp_map, Functor.comp_obj] at h
  have h' := congrArg (fun f => f ≫ (θ (C F)).app ((qcBaseProductFunctor q).op.obj X)) h.symm
  simp only [Category.assoc] at h'
  rw [h']
  simp only [productDoubleLaurentOppositeMap, Functor.map_comp, doubleContractionπ,
    Category.assoc]

/-- The actual double product transport intertwines the independently descended swaps. -/
@[reassoc]
theorem productDoubleContractionTransportIso_swap
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    doubleContractionSwap ((qcBaseProductFunctor q).op ⋙ F) X ≫
        (productDoubleContractionTransportIso q F).hom.app X =
      (productDoubleContractionTransportIso q F).hom.app X ≫
        doubleContractionSwap F ((qcBaseProductFunctor q).op.obj X) := by
  apply doubleContraction_hom_ext (NatTrans.op plus) (NatTrans.op minus)
    ((qcBaseProductFunctor q).op ⋙ F) X
  simp only [doubleContractionπ_swap_assoc, productDoubleContractionTransportIso_π_assoc,
    productDoubleContractionTransportIso_π, doubleContractionπ_swap, Functor.comp_map]
  simp only [← Category.assoc, ← F.map_comp]
  rw [productDoubleLaurentOppositeMap_swap]

/-- The componentwise compatibility is a square of the original natural isomorphisms. -/
theorem productDoubleContractionTransportIso_swap_nat
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (doubleContractionSwapNatIso ((qcBaseProductFunctor q).op ⋙ F)).hom ≫
        (productDoubleContractionTransportIso q F).hom =
      (productDoubleContractionTransportIso q F).hom ≫
        Functor.whiskerLeft (qcBaseProductFunctor q).op (doubleContractionSwapNatIso F).hom := by
  apply NatTrans.ext
  funext X
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app,
    doubleContractionSwapNatIso_hom_app] using productDoubleContractionTransportIso_swap q F X

/-- A sign equality at the fixed product base transports to the product-parameter row. -/
theorem doubleContractionSwap_neg_product_app
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ)
    (h : doubleContractionSwap F ((qcBaseProductFunctor q).op.obj X) =
      -𝟙 ((C (C F)).obj ((qcBaseProductFunctor q).op.obj X))) :
    doubleContractionSwap ((qcBaseProductFunctor q).op ⋙ F) X =
      -𝟙 ((C (C ((qcBaseProductFunctor q).op ⋙ F))).obj X) := by
  apply (cancel_mono ((productDoubleContractionTransportIso q F).hom.app X)).1
  rw [productDoubleContractionTransportIso_swap, h]
  simp only [Preadditive.comp_neg, Preadditive.neg_comp, Category.id_comp]
  change -((productDoubleContractionTransportIso q F).hom.app X ≫ 𝟙 _) = _
  exact congrArg Neg.neg (Category.comp_id ((productDoubleContractionTransportIso q F).hom.app X))

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
