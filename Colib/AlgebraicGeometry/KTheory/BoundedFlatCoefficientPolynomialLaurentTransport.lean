/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactPolynomialLaurent

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import
  Colib.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurentProductNaturality
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSectionEvaluationNaturality
public import Colib.KTheory.Bass.DiagramTransport

/-!
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientPolynomialLaurentTransport.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original two-chart transport on the actual compact native coefficient row

The existing quasi-compact native row is compared by genuine natural
isomorphisms with the original polynomial and Laurent product functors. Both
original chart squares hold, including the inverse-coordinate map. Consequently
the actual two-chart contraction and its Laurent representatives transport for
any additive-group valued functor. Compactness of the original scheme is the
only geometric hypothesis.

This module supplies the original ambient coefficient maps and chart transport.
It does not claim supported-group comparisons, assembled scheme-restriction
naturality, seed invertibility, stabilization, telescope or TT identification.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
  AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u w
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- The actual native polynomial/product isomorphism in the quasi-compact opposite row. -/
def boundedAboveFlatCoefficientPolynomialIso :
    polynomialUnderFunctor R ⋙ boundedAboveFlatCoefficientQuasiCompactRow P ≅
      boundedAboveFlatCoefficientQuasiCompactRow P ⋙
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.op :=
  NatIso.ofComponents
    (fun a ↦ (AlgebraicGeometry.Scheme.quasiCompactScheme.isoMk (polynomialIso P
      a)).symm.op) (by
      intro a b g
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      change (polynomialIso P b).inv ≫
        coefficientMap P ((polynomialUnderFunctor R).map g) =
          (AlgebraicGeometry.Scheme.Products.baseProductFunctor
            (PolynomialLaurent.polynomialProjection
              (CommRingCat.of (ULift.{u} ℤ)))).map
              (coefficientMap P g) ≫ (polynomialIso P a).inv
      apply (cancel_mono (polynomialIso P a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [polynomialIso_naturality P g, Iso.inv_hom_id_assoc])

/-- The actual native Laurent/product isomorphism in the same quasi-compact opposite row. -/
def boundedAboveFlatCoefficientLaurentIso :
    laurentUnderFunctor R ⋙ boundedAboveFlatCoefficientQuasiCompactRow P ≅
      boundedAboveFlatCoefficientQuasiCompactRow P ⋙
        AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op :=
  NatIso.ofComponents
    (fun a ↦ (AlgebraicGeometry.Scheme.quasiCompactScheme.isoMk (laurentIso P a)).symm.op)
      (by
      intro a b g
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      change (laurentIso P b).inv ≫
        coefficientMap P ((laurentUnderFunctor R).map g) =
          (AlgebraicGeometry.Scheme.Products.baseProductFunctor
            (PolynomialLaurent.laurentProjection
              (CommRingCat.of (ULift.{u} ℤ)))).map
              (coefficientMap P g) ≫ (laurentIso P a).inv
      apply (cancel_mono (laurentIso P a).hom).1
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      rw [laurentIso_naturality P g, Iso.inv_hom_id_assoc])

/-- The forward opposite polynomial component is exactly the original geometric inverse. -/
@[simp] theorem boundedAboveFlatCoefficientPolynomialIso_hom_app (a : Under R) :
    ((boundedAboveFlatCoefficientPolynomialIso P).hom.app a).unop.hom =
      (polynomialIso P a).inv := rfl

/-- The forward opposite Laurent component is exactly the original geometric inverse. -/
@[simp] theorem boundedAboveFlatCoefficientLaurentIso_hom_app (a : Under R) :
    ((boundedAboveFlatCoefficientLaurentIso P).hom.app a).unop.hom =
      (laurentIso P a).inv := rfl

/-- The exact original positive square required by two-chart contraction transport. -/
@[reassoc] theorem boundedAboveFlatCoefficientPolynomialLaurentIso_plus (a : Under R) :
    (boundedAboveFlatCoefficientQuasiCompactRow P).map ((underToLaurent R).app a) ≫
        (boundedAboveFlatCoefficientLaurentIso P).hom.app a =
      (boundedAboveFlatCoefficientPolynomialIso P).hom.app a ≫
        (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus).app
          ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentIso P a).inv ≫ laurentPlus P a =
    (AlgebraicGeometry.Scheme.Products.baseProductTransformation _ _
      (PolynomialLaurent.laurentToPolynomial
        (CommRingCat.of (ULift.{u} ℤ)))
      (PolynomialLaurent.laurentToPolynomial_projection
        (CommRingCat.of (ULift.{u} ℤ)))).app
        (space (op P, a)) ≫ (polynomialIso P a).inv
  apply (cancel_mono (polynomialIso P a).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [polynomialLaurentIso_plus P a, Iso.inv_hom_id_assoc]

/-- The exact original inverse-coordinate square required by the same transport. -/
@[reassoc] theorem boundedAboveFlatCoefficientPolynomialLaurentIso_minus (a : Under R) :
    (boundedAboveFlatCoefficientQuasiCompactRow P).map ((underToLaurentInvert R).app a) ≫
        (boundedAboveFlatCoefficientLaurentIso P).hom.app a =
      (boundedAboveFlatCoefficientPolynomialIso P).hom.app a ≫
        (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus).app
          ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentIso P a).inv ≫ laurentMinus P a =
    (AlgebraicGeometry.Scheme.Products.baseProductTransformation _ _
      (PolynomialLaurent.laurentMinus
        (CommRingCat.of (ULift.{u} ℤ)))
      (PolynomialLaurent.laurentMinus_projection
        (CommRingCat.of (ULift.{u} ℤ)))).app
        (space (op P, a)) ≫ (polynomialIso P a).inv
  apply (cancel_mono (polynomialIso P a).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [polynomialLaurentIso_minus P a, Iso.inv_hom_id_assoc]

/-- Genuine original two-chart cokernel transport on the existing native coefficient row. -/
def boundedAboveFlatCoefficientContractionTransportIso
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    KTheory.Bass.TwoChart.contraction (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientQuasiCompactRow P ⋙ F) ≅
      boundedAboveFlatCoefficientQuasiCompactRow P ⋙
        KTheory.Bass.TwoChart.contraction (NatTrans.op
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
          (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F :=
  KTheory.Bass.TwoChart.contractionTransportIso
    (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientQuasiCompactRow P)
    (boundedAboveFlatCoefficientPolynomialIso P) (boundedAboveFlatCoefficientLaurentIso P)
    (boundedAboveFlatCoefficientPolynomialLaurentIso_plus P)
    (boundedAboveFlatCoefficientPolynomialLaurentIso_minus P) F

/-- The same transport retains the original native Laurent quotient representative. -/
@[reassoc] theorem boundedAboveFlatCoefficientContractionTransportIso_π
    (F : AlgebraicGeometry.Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (a : Under R) :
    (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedAboveFlatCoefficientQuasiCompactRow P ⋙ F)).app a ≫
        (boundedAboveFlatCoefficientContractionTransportIso P F).hom.app a =
      F.map ((boundedAboveFlatCoefficientLaurentIso P).hom.app a) ≫
        (KTheory.Bass.TwoChart.contractionπ (NatTrans.op
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus)
          (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus) F).app
            ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a) :=
  KTheory.Bass.TwoChart.contractionTransportIso_π
    (NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus) (NatTrans.op
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus)
    (underToLaurent R) (underToLaurentInvert R)
    (boundedAboveFlatCoefficientQuasiCompactRow P)
    (boundedAboveFlatCoefficientPolynomialIso P) (boundedAboveFlatCoefficientLaurentIso P)
    (boundedAboveFlatCoefficientPolynomialLaurentIso_plus P)
    (boundedAboveFlatCoefficientPolynomialLaurentIso_minus P) F a

end AlgebraicGeometry.Scheme.Modules
