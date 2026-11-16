/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactOpenPairPolynomialLaurentInterchange
public import Colib.KTheory.Bass.DiagramTransportNaturality
public import Colib.KTheory.Bass.DiagramTransportGroupNaturality

/-! # Actual independent-product transport of the original supported Bass quotient

The literal open-pair product swap constructs both opposite chart squares required by the existing
Bass cokernel transport. The resulting isomorphism preserves the original Laurent quotient and is
natural in both the group-valued row and every actual fixed-factor map. No geometric interchange
or desired quotient comparison is supplied as a premise.

Source: `Quillen/KTheory/Bass/OpenPairProductTransport.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Products
universe u w
namespace AlgebraicGeometry.Scheme.Bass
open KTheory.Bass.TwoChart

variable {S S' : AlgebraicGeometry.Scheme.{u}}

/-- The original polynomial interchange in the variance used by negative K-theory. -/
def pairProductPolynomialOppositeIso (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q] :
    pairPolynomialFunctor.op ⋙ (pairBaseProductFunctor q).op ≅
      (pairBaseProductFunctor q).op ⋙ pairPolynomialFunctor.op :=
  NatIso.op (pairBaseProductSwapIso q (PolynomialLaurent.polynomialProjection
        (CommRingCat.of (ULift.{u} ℤ))))

/-- The original Laurent interchange in the same opposite variance. -/
def pairProductLaurentOppositeIso (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q] :
    pairLaurentFunctor.op ⋙ (pairBaseProductFunctor q).op ≅
      (pairBaseProductFunctor q).op ⋙ pairLaurentFunctor.op :=
  NatIso.op (pairBaseProductSwapIso q (PolynomialLaurent.laurentProjection
        (CommRingCat.of (ULift.{u} ℤ))))

/-- The forward opposite polynomial component unops to the original forward geometric swap. -/
@[simp]
theorem pairProductPolynomialOppositeIso_hom_unop
    (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    ((pairProductPolynomialOppositeIso q).hom.app X).unop =
      (pairBaseProductSwapIso q (PolynomialLaurent.polynomialProjection
        (CommRingCat.of (ULift.{u} ℤ)))).hom.app
        X.unop := rfl

/-- The forward opposite Laurent component keeps the same original factor order. -/
@[simp]
theorem pairProductLaurentOppositeIso_hom_unop (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    ((pairProductLaurentOppositeIso q).hom.app X).unop =
      (pairBaseProductSwapIso q (PolynomialLaurent.laurentProjection
        (CommRingCat.of (ULift.{u} ℤ)))).hom.app
        X.unop := rfl

/-- The original positive chart square is constructed from the actual second-factor swap. -/
@[reassoc]
theorem pairProductOppositeIso_plus (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    (pairBaseProductFunctor q).op.map ((NatTrans.op pairPlus).app X) ≫
        (pairProductLaurentOppositeIso q).hom.app X =
      (pairProductPolynomialOppositeIso q).hom.app X ≫
        (NatTrans.op pairPlus).app ((pairBaseProductFunctor q).op.obj X) := by
  apply Quiver.Hom.unop_inj
  exact (pairBaseProductSwapIso_plus_second q X.unop).symm

/-- The original inverse-coordinate chart uses the same actual second-factor comparison. -/
@[reassoc]
theorem pairProductOppositeIso_minus (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    (pairBaseProductFunctor q).op.map ((NatTrans.op pairMinus).app X) ≫
        (pairProductLaurentOppositeIso q).hom.app X =
      (pairProductPolynomialOppositeIso q).hom.app X ≫
        (NatTrans.op pairMinus).app ((pairBaseProductFunctor q).op.obj X) := by
  apply Quiver.Hom.unop_inj
  exact (pairBaseProductSwapIso_minus_second q X.unop).symm

/-- Actual product transport of the original open-pair two-chart cokernel. -/
def pairProductContractionTransportIso (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    contraction (NatTrans.op pairPlus) (NatTrans.op pairMinus)
      ((pairBaseProductFunctor q).op ⋙ F) ≅
      (pairBaseProductFunctor q).op ⋙
        contraction (NatTrans.op pairPlus) (NatTrans.op pairMinus) F :=
  contractionTransportIso (NatTrans.op pairPlus) (NatTrans.op pairMinus)
    (NatTrans.op pairPlus) (NatTrans.op pairMinus) (pairBaseProductFunctor q).op
    (pairProductPolynomialOppositeIso q) (pairProductLaurentOppositeIso q)
    (pairProductOppositeIso_plus q) (pairProductOppositeIso_minus q) F

/-- The actual quotient representative is retained with its original Laurent swap. -/
@[reassoc]
theorem pairProductContractionTransportIso_π (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus)
      ((pairBaseProductFunctor q).op ⋙ F)).app X ≫
        (pairProductContractionTransportIso q F).hom.app X =
      F.map ((pairProductLaurentOppositeIso q).hom.app X) ≫
        (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).app
          ((pairBaseProductFunctor q).op.obj X) :=
  contractionTransportIso_π (NatTrans.op pairPlus) (NatTrans.op pairMinus)
    (NatTrans.op pairPlus) (NatTrans.op pairMinus) (pairBaseProductFunctor q).op
    (pairProductPolynomialOppositeIso q) (pairProductLaurentOppositeIso q)
    (pairProductOppositeIso_plus q) (pairProductOppositeIso_minus q) F X

/-- Every natural map of original group-valued rows commutes with this actual transport. -/
@[reassoc]
theorem pairProductContractionTransportIso_groupMap
    (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    {F G : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}} (α : F ⟶ G)
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    (contractionMap (NatTrans.op pairPlus) (NatTrans.op pairMinus)
      (Functor.whiskerLeft (pairBaseProductFunctor q).op α)).app X ≫
        (pairProductContractionTransportIso q G).hom.app X =
      (pairProductContractionTransportIso q F).hom.app X ≫
        (contractionMap (NatTrans.op pairPlus) (NatTrans.op pairMinus) α).app
          ((pairBaseProductFunctor q).op.obj X) :=
  contractionTransportIso_groupMap (NatTrans.op pairPlus) (NatTrans.op pairMinus)
    (NatTrans.op pairPlus) (NatTrans.op pairMinus) (pairBaseProductFunctor q).op
    (pairProductPolynomialOppositeIso q) (pairProductLaurentOppositeIso q)
    (pairProductOppositeIso_plus q) (pairProductOppositeIso_minus q) α X

/-- The fixed-factor transformation has its actual contravariant Laurent square. -/
@[reassoc]
theorem pairProductLaurentOppositeIso_factorMap (q : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q' : S' ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q] [QuasiCompact q']
    (f : S ⟶ S') (hf : f ≫ q' = q) (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    (NatTrans.op (pairBaseProductTransformation q q' f hf)).app (pairLaurentFunctor.op.obj X) ≫
        (pairProductLaurentOppositeIso q).hom.app X =
      (pairProductLaurentOppositeIso q').hom.app X ≫
        pairLaurentFunctor.op.map
          ((NatTrans.op (pairBaseProductTransformation q q' f hf)).app X) := by
  apply Quiver.Hom.unop_inj
  exact (pairBaseProductSwapIso_transformation_first q q'
    (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ))) f hf X.unop).symm

/-- Every actual fixed-factor map preserves the original quotient transport. -/
@[reassoc]
theorem pairProductContractionTransportIso_factorMap (q : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q' : S' ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q] [QuasiCompact q']
    (f : S ⟶ S') (hf : f ≫ q' = q)
    (F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    (contractionMap (NatTrans.op pairPlus) (NatTrans.op pairMinus)
      (Functor.whiskerRight (NatTrans.op (pairBaseProductTransformation q q' f hf)) F)).app X ≫
        (pairProductContractionTransportIso q F).hom.app X =
      (pairProductContractionTransportIso q' F).hom.app X ≫
        (contraction (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).map
          ((NatTrans.op (pairBaseProductTransformation q q' f hf)).app X) :=
  contractionTransportIso_map (NatTrans.op pairPlus) (NatTrans.op pairMinus)
    (NatTrans.op pairPlus) (NatTrans.op pairMinus)
    (pairBaseProductFunctor q').op (pairBaseProductFunctor q).op
    (pairProductPolynomialOppositeIso q') (pairProductLaurentOppositeIso q')
    (pairProductPolynomialOppositeIso q) (pairProductLaurentOppositeIso q)
    (pairProductOppositeIso_plus q') (pairProductOppositeIso_minus q')
    (pairProductOppositeIso_plus q) (pairProductOppositeIso_minus q)
    (NatTrans.op (pairBaseProductTransformation q q' f hf))
    (pairProductLaurentOppositeIso_factorMap q q' f hf) F X

/-- The original coefficient projection commutes with the literal Laurent factor swap. -/
@[reassoc]
theorem pairProductLaurentOppositeIso_polynomialProjection
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    (NatTrans.op pairPolynomialProjection).app (pairLaurentFunctor.op.obj X) ≫
        (pairProductLaurentOppositeIso
          (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))).hom.app X =
      pairLaurentFunctor.op.map ((NatTrans.op pairPolynomialProjection).app X) := by
  apply Quiver.Hom.unop_inj
  exact pairBaseProductSwapIso_projection_first
    (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))
    (PolynomialLaurent.laurentProjection (CommRingCat.of (ULift.{u} ℤ))) X.unop

/-- Product transport retains the actual common-corner coefficient map after contraction. -/
@[reassoc]
theorem pairProductContractionTransportIso_polynomialProjection
    (F : QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactOpenPairs.{u}ᵒᵖ) :
    (contractionMap (NatTrans.op pairPlus) (NatTrans.op pairMinus)
      (Functor.whiskerRight (NatTrans.op pairPolynomialProjection) F)).app X ≫
        (pairProductContractionTransportIso
          (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ))) F).hom.app X =
      (contraction (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).map
        ((NatTrans.op pairPolynomialProjection).app X) := by
  apply (cancel_epi ((contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).app X)).mp
  rw [← Category.assoc, contractionMap_π, Category.assoc]
  have hp := pairProductContractionTransportIso_π
    (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ))) F X
  change (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus)
      (pairPolynomialFunctor.op ⋙ F)).app X ≫
        (pairProductContractionTransportIso
          (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ))) F).hom.app X =
      F.map ((pairProductLaurentOppositeIso
        (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))).hom.app X) ≫
          (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).app
            (pairPolynomialFunctor.op.obj X) at hp
  rw [hp]
  calc
    _ = (F.map ((NatTrans.op pairPolynomialProjection).app (pairLaurentFunctor.op.obj X)) ≫
        F.map ((pairProductLaurentOppositeIso
          (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))).hom.app X)) ≫
        (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).app
          (pairPolynomialFunctor.op.obj X) := (Category.assoc _ _ _).symm
    _ = F.map ((NatTrans.op pairPolynomialProjection).app (pairLaurentFunctor.op.obj X) ≫
        (pairProductLaurentOppositeIso
          (PolynomialLaurent.polynomialProjection (CommRingCat.of (ULift.{u} ℤ)))).hom.app X) ≫
        (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).app
          (pairPolynomialFunctor.op.obj X) :=
      congrArg (fun g => g ≫ (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).app
        (pairPolynomialFunctor.op.obj X)) (F.map_comp _ _).symm
    _ = F.map (pairLaurentFunctor.op.map ((NatTrans.op pairPolynomialProjection).app X)) ≫
        (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).app
          (pairPolynomialFunctor.op.obj X) :=
      congrArg (fun g => F.map g ≫
        (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).app
        (pairPolynomialFunctor.op.obj X)) (pairProductLaurentOppositeIso_polynomialProjection X)
    _ = _ := (contractionπ (NatTrans.op pairPlus) (NatTrans.op pairMinus) F).naturality
      ((NatTrans.op pairPolynomialProjection).app X)

end AlgebraicGeometry.Scheme.Bass
