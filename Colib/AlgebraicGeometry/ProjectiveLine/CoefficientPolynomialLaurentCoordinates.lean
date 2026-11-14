/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.CoefficientPolynomialLaurentProduct
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateUnitProjection

/-! # Coordinates of the actual coefficient polynomial and Laurent fibers -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent CommRingCat.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients

variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left] (a : Under R)

/-- The compact native fiber at the given coefficient. -/
def compactFiber : QuasiCompactSchemes.{u} :=
  ⟨space (op P, a), compactSpace_space (op P, a)⟩

/-- The polynomial coefficient fiber is the original relative affine line. -/
def compactFiberPolynomialIso :
    (compactFiber P ((polynomialUnderFunctor R).obj a)).obj ≅
      (Relative.polynomialFunctor.obj (compactFiber P a)).obj :=
  polynomialIso P a

/-- The Laurent coefficient fiber is the original relative Laurent scheme. -/
def compactFiberLaurentIso :
    (compactFiber P ((laurentUnderFunctor R).obj a)).obj ≅
      (Relative.laurentFunctor.obj (compactFiber P a)).obj :=
  laurentIso P a

/-- The source polynomial leg is the unchanged relative projection. -/
theorem compactFiberPolynomialIso_projection :
    (compactFiberPolynomialIso P a).hom ≫
        (Relative.polynomialProjection.app (compactFiber P a)).hom =
      polynomialProjection P a :=
  polynomialIso_hom_fst P a

/-- The source Laurent leg is the unchanged relative projection. -/
theorem compactFiberLaurentIso_projection :
    (compactFiberLaurentIso P a).hom ≫ (Relative.laurentProjection.app (compactFiber P a)).hom =
      laurentProjection P a :=
  laurentIso_hom_fst P a

/-- Both original chart diagrams use the actual specified coordinate maps. -/
theorem compactFiberLaurentIso_charts :
    laurentPlus P a ≫ (compactFiberPolynomialIso P a).hom =
      (compactFiberLaurentIso P a).hom ≫ (Relative.plus.app (compactFiber P a)).hom ∧
    laurentMinus P a ≫ (compactFiberPolynomialIso P a).hom =
      (compactFiberLaurentIso P a).hom ≫ (Relative.minus.app (compactFiber P a)).hom :=
  ⟨polynomialLaurentIso_plus P a, polynomialLaurentIso_minus P a⟩

/-- The relative integral Laurent coordinate pulls back to the actual coefficient Laurent unit. -/
theorem compactFiberLaurentIso_coordinate :
    Units.map (compactFiberLaurentIso P a).hom.appTop.hom.toMonoidHom
        (ProjectiveLine.relativeLaurentCoordinateUnit (compactFiber P a)) =
      Units.map (coefficientProjection (op P, (laurentUnderFunctor R).obj a)).appTop.hom.toMonoidHom
        (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentCoordinate a.right) :=
  laurentIso_globalUnit P a

end AlgebraicGeometry.Scheme.BaseChange.Coefficients
