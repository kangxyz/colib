/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactPolynomialLaurentInterchange
public import Colib.KTheory.Bass.DiagramTransportNaturality
public import Colib.KTheory.Bass.DiagramTransportGroupNaturality

/-! # Actual independent-product transport of the original Bass quotient

The literal scheme product swap constructs both opposite chart squares required by the existing
Bass cokernel transport. The resulting isomorphism preserves the original Laurent quotient and is
natural in both the group-valued row and every actual fixed-factor map. No geometric interchange
or desired quotient comparison is supplied as a premise.

Source: `Quillen/KTheory/Bass/SchemeProductTransport.lean`,
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

variable {S S' : AlgebraicGeometry.Scheme.{u}}

/-- The original polynomial interchange in the variance used by negative K-theory. -/
def productPolynomialOppositeIso (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q] :
    polynomialFunctor.op ⋙ (qcBaseProductFunctor q).op ≅
      (qcBaseProductFunctor q).op ⋙ polynomialFunctor.op :=
  NatIso.op (qcBaseProductSwapIso q (PolynomialLaurent.polynomialProjection Z))

/-- The original Laurent interchange in the same opposite variance. -/
def productLaurentOppositeIso (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q] :
    laurentFunctor.op ⋙ (qcBaseProductFunctor q).op ≅
      (qcBaseProductFunctor q).op ⋙ laurentFunctor.op :=
  NatIso.op (qcBaseProductSwapIso q (PolynomialLaurent.laurentProjection Z))

/-- The forward opposite polynomial component unops to the original forward geometric swap. -/
@[simp]
theorem productPolynomialOppositeIso_hom_unop
    (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    ((productPolynomialOppositeIso q).hom.app X).unop =
      (qcBaseProductSwapIso q (PolynomialLaurent.polynomialProjection Z)).hom.app
        X.unop := rfl

/-- The forward opposite Laurent component keeps the same original factor order. -/
@[simp]
theorem productLaurentOppositeIso_hom_unop (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    ((productLaurentOppositeIso q).hom.app X).unop =
      (qcBaseProductSwapIso q (PolynomialLaurent.laurentProjection Z)).hom.app
        X.unop := rfl

/-- The original positive chart square is constructed from the actual second-factor swap. -/
@[reassoc]
theorem productOppositeIso_plus (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (qcBaseProductFunctor q).op.map ((NatTrans.op plus).app X) ≫
        (productLaurentOppositeIso q).hom.app X =
      (productPolynomialOppositeIso q).hom.app X ≫
        (NatTrans.op plus).app ((qcBaseProductFunctor q).op.obj X) := by
  apply Quiver.Hom.unop_inj
  exact (qcBaseProductSwapIso_plus_second q X.unop).symm

/-- The original inverse-coordinate chart uses the same actual second-factor comparison. -/
@[reassoc]
theorem productOppositeIso_minus (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (qcBaseProductFunctor q).op.map ((NatTrans.op minus).app X) ≫
        (productLaurentOppositeIso q).hom.app X =
      (productPolynomialOppositeIso q).hom.app X ≫
        (NatTrans.op minus).app ((qcBaseProductFunctor q).op.obj X) := by
  apply Quiver.Hom.unop_inj
  exact (qcBaseProductSwapIso_minus_second q X.unop).symm

/-- Actual product transport of the original two-chart cokernel, with no supplied chart square. -/
def productContractionTransportIso (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    contraction (NatTrans.op plus) (NatTrans.op minus) ((qcBaseProductFunctor q).op ⋙ F) ≅
      (qcBaseProductFunctor q).op ⋙ contraction (NatTrans.op plus) (NatTrans.op minus) F :=
  contractionTransportIso (NatTrans.op plus) (NatTrans.op minus)
    (NatTrans.op plus) (NatTrans.op minus) (qcBaseProductFunctor q).op
    (productPolynomialOppositeIso q) (productLaurentOppositeIso q)
    (productOppositeIso_plus q) (productOppositeIso_minus q) F

/-- The actual quotient representative is retained with its original Laurent swap. -/
@[reassoc]
theorem productContractionTransportIso_π (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contractionπ (NatTrans.op plus) (NatTrans.op minus)
      ((qcBaseProductFunctor q).op ⋙ F)).app X ≫
        (productContractionTransportIso q F).hom.app X =
      F.map ((productLaurentOppositeIso q).hom.app X) ≫
        (contractionπ (NatTrans.op plus) (NatTrans.op minus) F).app
          ((qcBaseProductFunctor q).op.obj X) :=
  contractionTransportIso_π (NatTrans.op plus) (NatTrans.op minus)
    (NatTrans.op plus) (NatTrans.op minus) (qcBaseProductFunctor q).op
    (productPolynomialOppositeIso q) (productLaurentOppositeIso q)
    (productOppositeIso_plus q) (productOppositeIso_minus q) F X

/-- Every natural map of original group-valued rows commutes with this actual transport. -/
@[reassoc]
theorem productContractionTransportIso_groupMap
    (q : S ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q]
    {F G : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}} (α : F ⟶ G)
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contractionMap (NatTrans.op plus) (NatTrans.op minus)
      (Functor.whiskerLeft (qcBaseProductFunctor q).op α)).app X ≫
        (productContractionTransportIso q G).hom.app X =
      (productContractionTransportIso q F).hom.app X ≫
        (contractionMap (NatTrans.op plus) (NatTrans.op minus) α).app
          ((qcBaseProductFunctor q).op.obj X) :=
  contractionTransportIso_groupMap (NatTrans.op plus) (NatTrans.op minus)
    (NatTrans.op plus) (NatTrans.op minus) (qcBaseProductFunctor q).op
    (productPolynomialOppositeIso q) (productLaurentOppositeIso q)
    (productOppositeIso_plus q) (productOppositeIso_minus q) α X

/-- The fixed-factor transformation has its actual contravariant Laurent square. -/
@[reassoc]
theorem productLaurentOppositeIso_factorMap (q : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q' : S' ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q] [QuasiCompact q']
    (f : S ⟶ S') (hf : f ≫ q' = q) (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (NatTrans.op (qcBaseProductTransformation q q' f hf)).app (laurentFunctor.op.obj X) ≫
        (productLaurentOppositeIso q).hom.app X =
      (productLaurentOppositeIso q').hom.app X ≫
        laurentFunctor.op.map ((NatTrans.op (qcBaseProductTransformation q q' f hf)).app X) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  exact (baseProductSwapIso_transformation_first q q'
    (PolynomialLaurent.laurentProjection Z) f hf X.unop.obj).symm

/-- Every actual fixed-factor map preserves the original quotient transport. -/
@[reassoc]
theorem productContractionTransportIso_factorMap (q : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q' : S' ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact q] [QuasiCompact q']
    (f : S ⟶ S') (hf : f ≫ q' = q)
    (F : QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (X : QuasiCompactSchemes.{u}ᵒᵖ) :
    (contractionMap (NatTrans.op plus) (NatTrans.op minus)
      (Functor.whiskerRight (NatTrans.op (qcBaseProductTransformation q q' f hf)) F)).app X ≫
        (productContractionTransportIso q F).hom.app X =
      (productContractionTransportIso q' F).hom.app X ≫
        (contraction (NatTrans.op plus) (NatTrans.op minus) F).map
          ((NatTrans.op (qcBaseProductTransformation q q' f hf)).app X) :=
  contractionTransportIso_map (NatTrans.op plus) (NatTrans.op minus)
    (NatTrans.op plus) (NatTrans.op minus)
    (qcBaseProductFunctor q').op (qcBaseProductFunctor q).op
    (productPolynomialOppositeIso q') (productLaurentOppositeIso q')
    (productPolynomialOppositeIso q) (productLaurentOppositeIso q)
    (productOppositeIso_plus q') (productOppositeIso_minus q')
    (productOppositeIso_plus q) (productOppositeIso_minus q)
    (NatTrans.op (qcBaseProductTransformation q q' f hf))
    (productLaurentOppositeIso_factorMap q q' f hf) F X

end AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
