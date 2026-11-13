/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.PolynomialCoordinateProduct
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MarkedGraphGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.GraphNeighborhood
public import Colib.AlgebraicGeometry.Divisors.PolynomialEvaluationFrame
public import Colib.AlgebraicGeometry.Divisors.FrameTransport
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# The global marked graph frame on the entire polynomial line

The parameter open is the whole original polynomial spectrum. The actual
evaluation ideal, not a pointwise frame, supplies the native divisor frame.
Its coordinate is the specified polynomial difference with its original sign.
This construction works over arbitrary commutative rings, including nilpotents.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Divisors
universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)

/-- The whole marked product is the actual inverse image of polynomial evaluation. -/
theorem wholePolynomialBoundaryGraph_isPullback :
    IsPullback (𝟙 (Spec (.of B)))
      (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z))
      (evaluationGraph B (z X)) (markedCoordinateProductIso R B z).inv := by
  apply IsPullback.of_horiz_isIso
  constructor
  rw [Category.id_comp]
  change evaluationGraph B (z X) =
    coordinateMarkGraph R B z ≫ (markedCoordinateProductIso R B z).inv
  rw [← evaluation_markedCoordinateProductIso R B z]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Equality of full inverse-image ideals, before selecting any parameter neighborhood. -/
theorem wholePolynomialBoundaryGraph_comap :
    (evaluationGraphIdeal B (z X)).comap (markedCoordinateProductIso R B z).inv =
      (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker :=
  (ker_eq_comap_of_cartesian (wholePolynomialBoundaryGraph_isPullback R B z).flip).symm

instance wholePolynomialBoundaryGraph_isEffectiveCartierDivisor :
    IsEffectiveCartierDivisor
      (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker := by
  rw [← wholePolynomialBoundaryGraph_comap R B z]
  exact isPullbackDefined_of_flat (markedCoordinateProductIso R B z).inv
    (evaluationGraphIdeal B (z X)) inferInstance

/-- The global frame required by the no-further-shrink signed-pencil producer. -/
def wholePolynomialBoundaryFrame :
    divisorSheaf
      (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker ≅
        SheafOfModules.unit
          (pullback (coordinateLineProjection R)
            (coordinateMark R B z ≫ coordinateLineProjection R)).ringCatSheaf :=
  (divisorComapEqIso (markedCoordinateProductIso R B z).inv
    (evaluationGraphIdeal B (z X))
    (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker
    (wholePolynomialBoundaryGraph_comap R B z)).symm ≪≫
      Modules.framePullback (markedCoordinateProductIso R B z).inv
        (evaluationGraphDivisorFrame B (z X))

/-- The exact global graph equation is the pullback of `X - C (z X)`. -/
theorem wholePolynomialBoundaryFrame_coordinate :
    (wholePolynomialBoundaryFrame R B z).hom.app ⊤
      (divisorSheafGlobalSection
        (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker) =
      (markedCoordinateProductIso R B z).inv.appTop (evaluationGraphEquation B (z X)) := by
  let E := (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker
  let D := evaluationGraphIdeal B (z X)
  let f := (markedCoordinateProductIso R B z).inv
  let e := divisorComapEqIso f D E (wholePolynomialBoundaryGraph_comap R B z)
  have he : e.inv.app ⊤ (divisorSheafGlobalSection E) =
      pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D) := by
    have hh : e.hom.app ⊤
        (pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D)) =
          divisorSheafGlobalSection E :=
      divisorComapEqIso_canonicalSection f D E (wholePolynomialBoundaryGraph_comap R B z)
    have h := congrArg (fun m => m.app ⊤
      (pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D))) e.hom_inv_id
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app,
      CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
    exact (congrArg (e.inv.app ⊤) hh).symm.trans h
  change (Modules.framePullback f (evaluationGraphDivisorFrame B (z X))).hom.app ⊤
    (e.inv.app ⊤ (divisorSheafGlobalSection E)) = _
  rw [he, Modules.framePullback_coordinate, evaluationGraphDivisorFrame_coordinate]

/-- Any whole-scheme base restriction retains the same exact signed coordinate. -/
theorem wholePolynomialBoundaryFrame_pullback_coordinate {T : Scheme.{u}}
    (a : T ⟶ pullback (coordinateLineProjection R)
      (coordinateMark R B z ≫ coordinateLineProjection R)) :
    (Modules.framePullback a (wholePolynomialBoundaryFrame R B z)).hom.app ⊤
      (pullbackGlobalSections a _
        (divisorSheafGlobalSection
          (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker)) =
      a.appTop ((markedCoordinateProductIso R B z).inv.appTop
        (evaluationGraphEquation B (z X))) := by
  rw [Modules.framePullback_coordinate, wholePolynomialBoundaryFrame_coordinate]

end AlgebraicGeometry.Scheme.RelativeCurvePencil
