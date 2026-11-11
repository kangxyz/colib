module
import Colib.AlgebraicGeometry.Scheme.IntegerBaseLaurentCoefficient

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.Relative
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.BaseChange.Coefficients.IntegerRow
universe u
noncomputable section

example {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPushout f (CommRingCat.ofHom Polynomial.C) (CommRingCat.ofHom Polynomial.C)
      (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) :=
  CommRingCat.PolynomialLaurent.polynomial_isPushout f

example {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPushout f (CommRingCat.ofHom LaurentPolynomial.C)
      (CommRingCat.ofHom LaurentPolynomial.C)
      (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom)) :=
  CommRingCat.PolynomialLaurent.laurent_isPushout f

example (R : CommRingCat.{u}) :
    (polynomialSpecIso R).hom ≫ pullback.fst _ _ =
      AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection R :=
  polynomialSpecIso_hom_fst R

example (R : CommRingCat.{u}) :
    AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus R ≫ (polynomialSpecIso R).hom =
      (laurentSpecIso R).hom ≫
        (baseProductTransformation _ _
          (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus (.of (ULift.{u} ℤ)))
          (laurentMinus_projection (.of (ULift.{u} ℤ)))).app (Spec R) :=
  polynomialLaurentSpecIso_minus R

example : specUnder.{u} ⋙ GlobalIndex.squareFunctor ≅
    CommRingCat.PolynomialLaurent.laurentUnderSquareFunctor (.of (ULift.{u} ℤ)) ⋙
      specUnder.mapArrow.mapArrow :=
  specSquare

variable (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
  (a : Under (CommRingCat.of (ULift.{u} ℤ)))

example : specUnder ⋙ (baseProductFunctor (specULiftZIsTerminal.from Q.left)).op ≅
    row Q ⋙ AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor
      (CommRingCat.of (ULift.{u} ℤ)) :=
  canonicalParameterRowIso Q

example (v : (Γ(Spec a.right, ⊤))ˣ) :
    Units.map (canonicalRowIso Q a).hom.appTop.hom.toMonoidHom
      (Units.map (pullback.fst (specULiftZIsTerminal.from (Spec a.right))
        (specULiftZIsTerminal.from Q.left)).appTop.hom.toMonoidHom v) =
      Units.map (coefficientProjection (op Q, a)).appTop.hom.toMonoidHom v :=
  canonicalRowIso_unit Q a v

example : (laurentParameterIso Q a).hom ≫
    (baseProductFunctor (specULiftZIsTerminal.from Q.left)).map
      ((baseProductProjection
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
          (.of (ULift.{u} ℤ)))).app (Spec a.right)) =
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.laurentProjection Q a ≫
      (canonicalRowIso Q a).hom :=
  laurentParameterIso_coefficient Q a

example (R : CommRingCat.{u}) :
    Units.map (laurentSpecIso R).hom.appTop.hom.toMonoidHom
      (Units.map (pullback.snd (specULiftZIsTerminal.from (Spec R))
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
          (.of (ULift.{u} ℤ)))).appTop.hom.toMonoidHom
            (laurentCoordinate (.of (ULift.{u} ℤ)))) = laurentCoordinate R :=
  nativeLaurentUnit_spec R
