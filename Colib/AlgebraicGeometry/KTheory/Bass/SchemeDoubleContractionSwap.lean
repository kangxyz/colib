/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeProductTransport
public import Colib.KTheory.Bass.TwoChartDoubleDescent

/-!
# The actual Laurent-variable swap on the double Bass quotient

The original geometric swap exchanges the four polynomial-chart relations, so
it descends through the two original cokernels. Its representative is the
actual double Laurent swap, not an automorphism defined by a spectrum comparison.
No assertion that this automorphism is the identity or its negative is made.

Source: `Quillen/KTheory/Bass/SchemeDoubleContractionSwap.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
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

local notation "Z" => CommRingCat.of (ULift ℤ)

/-- The literal opposite two-variable Laurent swap. -/
def doubleLaurentOppositeSwap : laurentFunctor.op ⋙ laurentFunctor.op ≅
    laurentFunctor.op ⋙ laurentFunctor.op :=
  productLaurentOppositeIso (PolynomialLaurent.laurentProjection Z)

/-- The inner plus relation goes to the corresponding outer relation under the actual swap. -/
@[reassoc]
theorem doubleLaurentOppositeSwap_inner_plus (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (NatTrans.op plus).app (laurentFunctor.op.obj X) ≫
        doubleLaurentOppositeSwap.hom.app X =
      (NatIso.op (qcBaseProductSwapIso (PolynomialLaurent.polynomialProjection Z)
        (PolynomialLaurent.laurentProjection Z))).hom.app X ≫
          laurentFunctor.op.map ((NatTrans.op plus).app X) := by
  apply Quiver.Hom.unop_inj
  exact (qcBaseProductSwapIso_plus_first
    (PolynomialLaurent.laurentProjection Z) X.unop).symm

/-- The outer plus relation goes to its original inner counterpart. -/
@[reassoc]
theorem doubleLaurentOppositeSwap_outer_plus (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    laurentFunctor.op.map ((NatTrans.op plus).app X) ≫
        doubleLaurentOppositeSwap.hom.app X =
      (productPolynomialOppositeIso (PolynomialLaurent.laurentProjection Z)).hom.app X ≫
        (NatTrans.op plus).app (laurentFunctor.op.obj X) :=
  productOppositeIso_plus (PolynomialLaurent.laurentProjection Z) X

/-- The inner minus relation goes to the corresponding outer relation under the actual swap. -/
@[reassoc]
theorem doubleLaurentOppositeSwap_inner_minus (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (NatTrans.op minus).app (laurentFunctor.op.obj X) ≫
        doubleLaurentOppositeSwap.hom.app X =
      (NatIso.op (qcBaseProductSwapIso (PolynomialLaurent.polynomialProjection Z)
        (PolynomialLaurent.laurentProjection Z))).hom.app X ≫
          laurentFunctor.op.map ((NatTrans.op minus).app X) := by
  apply Quiver.Hom.unop_inj
  exact (qcBaseProductSwapIso_minus_first
    (PolynomialLaurent.laurentProjection Z) X.unop).symm

/-- The outer minus relation goes to its original inner counterpart. -/
@[reassoc]
theorem doubleLaurentOppositeSwap_outer_minus (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    laurentFunctor.op.map ((NatTrans.op minus).app X) ≫
        doubleLaurentOppositeSwap.hom.app X =
      (productPolynomialOppositeIso (PolynomialLaurent.laurentProjection Z)).hom.app X ≫
        (NatTrans.op minus).app (laurentFunctor.op.obj X) :=
  productOppositeIso_minus (PolynomialLaurent.laurentProjection Z) X

/-- The actual swapped chart vanishes in the original double quotient. -/
theorem doubleLaurentOppositeSwap_inner_plus_quotient_zero
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    F.map ((NatTrans.op plus).app (laurentFunctor.op.obj X)) ≫
      (F.map (doubleLaurentOppositeSwap.hom.app X) ≫
        doubleContractionπ (NatTrans.op plus) (NatTrans.op minus) F X) = 0 := by
  rw [← Category.assoc, ← F.map_comp, doubleLaurentOppositeSwap_inner_plus,
    F.map_comp, Category.assoc, outerPlus_doubleContractionπ, comp_zero]

/-- The actual swapped chart vanishes in the original double quotient. -/
theorem doubleLaurentOppositeSwap_inner_minus_quotient_zero
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    F.map ((NatTrans.op minus).app (laurentFunctor.op.obj X)) ≫
      (F.map (doubleLaurentOppositeSwap.hom.app X) ≫
        doubleContractionπ (NatTrans.op plus) (NatTrans.op minus) F X) = 0 := by
  rw [← Category.assoc, ← F.map_comp, doubleLaurentOppositeSwap_inner_minus,
    F.map_comp, Category.assoc, outerMinus_doubleContractionπ, comp_zero]

/-- The actual swapped chart vanishes in the original double quotient. -/
theorem doubleLaurentOppositeSwap_outer_plus_quotient_zero
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    F.map (laurentFunctor.op.map ((NatTrans.op plus).app X)) ≫
      (F.map (doubleLaurentOppositeSwap.hom.app X) ≫
        doubleContractionπ (NatTrans.op plus) (NatTrans.op minus) F X) = 0 := by
  rw [← Category.assoc, ← F.map_comp, doubleLaurentOppositeSwap_outer_plus,
    F.map_comp, Category.assoc, innerPlus_doubleContractionπ, comp_zero]

/-- The actual swapped chart vanishes in the original double quotient. -/
theorem doubleLaurentOppositeSwap_outer_minus_quotient_zero
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    F.map (laurentFunctor.op.map ((NatTrans.op minus).app X)) ≫
      (F.map (doubleLaurentOppositeSwap.hom.app X) ≫
        doubleContractionπ (NatTrans.op plus) (NatTrans.op minus) F X) = 0 := by
  rw [← Category.assoc, ← F.map_comp, doubleLaurentOppositeSwap_outer_minus,
    F.map_comp, Category.assoc, innerMinus_doubleContractionπ, comp_zero]

/-- Descent of the actual double Laurent swap through the original double quotient. -/
def doubleContractionSwap (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contraction (NatTrans.op plus) (NatTrans.op minus)
      (contraction (NatTrans.op plus) (NatTrans.op minus) F)).obj X ⟶
    (contraction (NatTrans.op plus) (NatTrans.op minus)
      (contraction (NatTrans.op plus) (NatTrans.op minus) F)).obj X :=
  doubleContractionDesc (NatTrans.op plus) (NatTrans.op minus) F X
    (F.map (doubleLaurentOppositeSwap.hom.app X) ≫
      doubleContractionπ (NatTrans.op plus) (NatTrans.op minus) F X)
    (doubleLaurentOppositeSwap_inner_plus_quotient_zero F X)
    (doubleLaurentOppositeSwap_inner_minus_quotient_zero F X)
    (doubleLaurentOppositeSwap_outer_plus_quotient_zero F X)
    (doubleLaurentOppositeSwap_outer_minus_quotient_zero F X)

/-- Original double Laurent representatives are acted on by the actual variable swap. -/
@[reassoc]
theorem doubleContractionπ_swap (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    doubleContractionπ (NatTrans.op plus) (NatTrans.op minus) F X ≫
        doubleContractionSwap F X =
      F.map (doubleLaurentOppositeSwap.hom.app X) ≫
        doubleContractionπ (NatTrans.op plus) (NatTrans.op minus) F X :=
  doubleContractionπ_desc _ _ _ _ _ _ _ _ _

/-- Swapping the actual two Laurent factors twice is the original identity. -/
@[reassoc (attr := simp)]
theorem doubleLaurentOppositeSwap_comp (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    doubleLaurentOppositeSwap.hom.app X ≫ doubleLaurentOppositeSwap.hom.app X = 𝟙 _ := by
  change doubleLaurentOppositeSwap.hom.app X ≫ doubleLaurentOppositeSwap.inv.app X = 𝟙 _
  exact Iso.hom_inv_id_app doubleLaurentOppositeSwap X

/-- The descended actual swap is involutive, checked on the original epimorphic projection. -/
@[reassoc (attr := simp)]
theorem doubleContractionSwap_comp (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    doubleContractionSwap F X ≫ doubleContractionSwap F X = 𝟙 _ := by
  apply doubleContraction_hom_ext (NatTrans.op plus) (NatTrans.op minus) F X
  rw [← Category.assoc, doubleContractionπ_swap, Category.assoc,
    doubleContractionπ_swap, ← Category.assoc, ← F.map_comp,
    doubleLaurentOppositeSwap_comp, F.map_id]
  simp only [Functor.comp_obj, Category.id_comp, Category.comp_id]

/-- The independently descended swap is an automorphism of the original double quotient. -/
def doubleContractionSwapIso (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contraction (NatTrans.op plus) (NatTrans.op minus)
      (contraction (NatTrans.op plus) (NatTrans.op minus) F)).obj X ≅
    (contraction (NatTrans.op plus) (NatTrans.op minus)
      (contraction (NatTrans.op plus) (NatTrans.op minus) F)).obj X where
  hom := doubleContractionSwap F X
  inv := doubleContractionSwap F X
  hom_inv_id := doubleContractionSwap_comp F X
  inv_hom_id := doubleContractionSwap_comp F X

/-- The actual descended swap commutes with a natural map of the original group functors. -/
@[reassoc]
theorem doubleContractionSwap_groupMap
    {F G : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}} (α : F ⟶ G)
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contractionMap (NatTrans.op plus) (NatTrans.op minus)
        (contractionMap (NatTrans.op plus) (NatTrans.op minus) α)).app X ≫
        doubleContractionSwap G X =
      doubleContractionSwap F X ≫
        (contractionMap (NatTrans.op plus) (NatTrans.op minus)
          (contractionMap (NatTrans.op plus) (NatTrans.op minus) α)).app X := by
  have ha := α.naturality (doubleLaurentOppositeSwap.hom.app X)
  simp only [Functor.comp_obj] at ha
  apply doubleContraction_hom_ext (NatTrans.op plus) (NatTrans.op minus) F X
  rw [← Category.assoc, doubleContractionπ_groupMap, Category.assoc,
    doubleContractionπ_swap, ← Category.assoc,
    ← ha, Category.assoc,
    ← doubleContractionπ_groupMap, ← Category.assoc, ← doubleContractionπ_swap,
    Category.assoc]

/-- The independently descended swap is natural in the original base-scheme variable. -/
@[reassoc]
theorem doubleContractionSwap_naturality
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    {X Y : QuasiCompactSchemes.{u}ᵒᵖ} (f : X ⟶ Y) :
    (contraction (NatTrans.op plus) (NatTrans.op minus)
        (contraction (NatTrans.op plus) (NatTrans.op minus) F)).map f ≫
        doubleContractionSwap F Y =
      doubleContractionSwap F X ≫
        (contraction (NatTrans.op plus) (NatTrans.op minus)
          (contraction (NatTrans.op plus) (NatTrans.op minus) F)).map f := by
  apply doubleContraction_hom_ext (NatTrans.op plus) (NatTrans.op minus) F X
  rw [← Category.assoc, ← doubleContractionπ_naturality, Category.assoc,
    doubleContractionπ_swap, ← Category.assoc, ← F.map_comp]
  rw [show laurentFunctor.op.map (laurentFunctor.op.map f) ≫
      doubleLaurentOppositeSwap.hom.app Y =
    doubleLaurentOppositeSwap.hom.app X ≫
      laurentFunctor.op.map (laurentFunctor.op.map f) from
        doubleLaurentOppositeSwap.hom.naturality f]
  rw [F.map_comp, Category.assoc, doubleContractionπ_naturality,
    ← Category.assoc, ← doubleContractionπ_swap, Category.assoc]

/-- The actual involutive swap as a natural automorphism of the original double quotient. -/
def doubleContractionSwapNatIso (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    contraction (NatTrans.op plus) (NatTrans.op minus)
        (contraction (NatTrans.op plus) (NatTrans.op minus) F) ≅
      contraction (NatTrans.op plus) (NatTrans.op minus)
        (contraction (NatTrans.op plus) (NatTrans.op minus) F) :=
  NatIso.ofComponents (doubleContractionSwapIso F)
    (fun f => doubleContractionSwap_naturality F f)

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
