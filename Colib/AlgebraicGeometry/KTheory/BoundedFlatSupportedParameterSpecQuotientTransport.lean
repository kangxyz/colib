/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Scheme.QuasiCompactPolynomialLaurent
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseSpecSquare
public import Colib.KTheory.Bass.DiagramTransport
public import Colib.KTheory.Bass.TwoChartDoubleDescent

/-!
# The supported parameter quotient on the actual integral Spec row

The actual integral Spec parameter row carries the original polynomial and Laurent
chart isomorphisms. These give the two successive quotient transports, with both
original Laurent Spec comparison maps in the representative equation. This is a
comparison of parameter domains, independent of the chosen support pair.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
SupportedParameterSpecQuotientTransport.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent KTheory.Bass.TwoChart
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative AlgebraicGeometry.Scheme.Products
universe u w
namespace AlgebraicGeometry.Scheme.Modules.SupportedParameterSpecQuotientTransport
local notation "R" => CommRingCat.of (ULift ℤ)
local notation "p" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.plus
local notation "m" => NatTrans.op AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.minus
local notation "L" => AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.laurentFunctor.op

/-- Integral coefficients give the actual affine quasi-compact parameter row. -/
def specRow : Under R ⥤ Scheme.QuasiCompactSchemes.{u}ᵒᵖ where
  obj a := op ⟨Spec a.right, inferInstanceAs (CompactSpace (Spec a.right))⟩
  map f := (ObjectProperty.homMk (Spec.map f.right)).op
  map_id a := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact Spec.map_id a.right
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    exact Spec.map_comp f.right g.right

/-- The original polynomial Spec isomorphism on this actual parameter row. -/
def polynomialIso : polynomialUnderFunctor R ⋙ specRow ≅
    specRow ⋙ AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.polynomialFunctor.op :=
  NatIso.ofComponents
    (fun a => (quasiCompactScheme.isoMk (polynomialSpecIso a.right)).symm.op) (by
      intro a b g
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      change (polynomialSpecIso b.right).inv ≫
          Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom g.right.hom)) =
        (baseProductFunctor (PolynomialLaurent.polynomialProjection R)).map (Spec.map g.right) ≫
          (polynomialSpecIso a.right).inv
      apply (cancel_mono (polynomialSpecIso a.right).hom).1
      rw [Category.assoc, polynomialSpecIso_naturality]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id])

/-- The original Laurent Spec isomorphism on this actual parameter row. -/
def laurentIso : laurentUnderFunctor R ⋙ specRow ≅ specRow ⋙ L :=
  NatIso.ofComponents
    (fun a => (quasiCompactScheme.isoMk (laurentSpecIso a.right)).symm.op) (by
      intro a b g
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      change (laurentSpecIso b.right).inv ≫
          Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ g.right.hom)) =
        (baseProductFunctor (PolynomialLaurent.laurentProjection R)).map (Spec.map g.right) ≫
          (laurentSpecIso a.right).inv
      apply (cancel_mono (laurentSpecIso a.right).hom).1
      rw [Category.assoc, laurentSpecIso_naturality]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id])

/-- The positive chart keeps its original integral Spec square. -/
theorem plus_square (a : Under R) :
    specRow.map ((underToLaurent R).app a) ≫ laurentIso.hom.app a =
      polynomialIso.hom.app a ≫ (p).app (specRow.obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentSpecIso a.right).inv ≫ PolynomialLaurent.laurentToPolynomial a.right =
    (baseProductTransformation _ _ (PolynomialLaurent.laurentToPolynomial R)
      (PolynomialLaurent.laurentToPolynomial_projection R)).app (Spec a.right) ≫
        (polynomialSpecIso a.right).inv
  apply (cancel_mono (polynomialSpecIso a.right).hom).1
  rw [Category.assoc, polynomialLaurentSpecIso_plus]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse-coordinate chart keeps its original integral Spec square. -/
theorem minus_square (a : Under R) :
    specRow.map ((underToLaurentInvert R).app a) ≫ laurentIso.hom.app a =
      polynomialIso.hom.app a ≫ (m).app (specRow.obj a) := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  change (laurentSpecIso a.right).inv ≫ PolynomialLaurent.laurentMinus a.right =
    (baseProductTransformation _ _ (PolynomialLaurent.laurentMinus R)
      (PolynomialLaurent.laurentMinus_projection R)).app (Spec a.right) ≫
        (polynomialSpecIso a.right).inv
  apply (cancel_mono (polynomialSpecIso a.right).hom).1
  rw [Category.assoc, polynomialLaurentSpecIso_minus]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- One actual parameter quotient transported along the original integral Spec diagram. -/
def contractionIso (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    contraction (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F) ≅
      specRow ⋙ contraction p m F :=
  contractionTransportIso p m (underToLaurent R) (underToLaurentInvert R)
    specRow polynomialIso laurentIso plus_square minus_square F

/-- The original single quotient representative retains its Laurent Spec map. -/
@[reassoc]
theorem contractionIso_π (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (a : Under R) :
    (contractionπ (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F)).app a ≫
      (contractionIso F).hom.app a =
    F.map (laurentIso.hom.app a) ≫ (contractionπ p m F).app (specRow.obj a) :=
  contractionTransportIso_π p m (underToLaurent R) (underToLaurentInvert R)
    specRow polynomialIso laurentIso plus_square minus_square F a

/-- Both original Laurent Spec isomorphisms, in the actual qc parameter category. -/
def doubleLaurentIso (a : Under R) :
    specRow.obj ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) ≅
      (L).obj ((L).obj (specRow.obj a)) :=
  laurentIso.app ((laurentUnderFunctor R).obj a) ≪≫ (L).mapIso (laurentIso.app a)

/-- Both actual parameter quotients transported along the original integral Spec diagram. -/
def doubleContractionIso (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    contraction (underToLaurent R) (underToLaurentInvert R)
        (contraction (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F)) ≅
      specRow ⋙ contraction p m (contraction p m F) :=
  (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
      (contractionIso F) ≪≫ contractionIso (contraction p m F)

/-- The two original quotient projections retain both actual Laurent Spec maps. -/
@[reassoc]
theorem doubleContractionIso_π (F : Scheme.QuasiCompactSchemes.{u}ᵒᵖ ⥤ AddCommGrpCat.{w})
    (a : Under R) :
    doubleContractionπ (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F) a ≫
      (doubleContractionIso F).hom.app a =
    F.map (laurentIso.hom.app ((laurentUnderFunctor R).obj a) ≫
        (L).map (laurentIso.hom.app a)) ≫ doubleContractionπ p m F (specRow.obj a) := by
  simp only [doubleContractionIso, Iso.trans_hom, Functor.mapIso_hom,
    NatTrans.comp_app, doubleContractionπ, Category.assoc]
  change (contractionπ (underToLaurent R) (underToLaurentInvert R)
      (specRow ⋙ F)).app ((laurentUnderFunctor R).obj a) ≫
    (contractionπ (underToLaurent R) (underToLaurentInvert R)
      (contraction (underToLaurent R) (underToLaurentInvert R) (specRow ⋙ F))).app a ≫
      (contractionMap (underToLaurent R) (underToLaurentInvert R)
        (contractionIso F).hom).app a ≫ _ = _
  rw [contractionMap_π_assoc, ← Category.assoc, contractionIso_π]
  rw [Category.assoc, contractionIso_π]
  have hn := (contractionπ p m F).naturality (laurentIso.hom.app a)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  simpa only [Functor.comp_obj, Functor.map_comp, Category.assoc] using
    congrArg (fun k => F.map (laurentIso.hom.app ((laurentUnderFunctor R).obj a)) ≫
      k ≫ (contractionπ p m (contraction p m F)).app (specRow.obj a)) hn.symm

end AlgebraicGeometry.Scheme.Modules.SupportedParameterSpecQuotientTransport
