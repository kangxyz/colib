/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.PolynomialCoordinateProduct
public import Colib.AlgebraicGeometry.Divisors.PolynomialEvaluationFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CanonicalBoundaryFrame
public import Colib.AlgebraicGeometry.Divisors.FrameTransport

/-!
# The genuine polynomial scalar unit on the correction source

The correction source is independent of the retained source curve. Its map to
the coordinate line misses the whole marked subscheme. The actual polynomial
coordinate map therefore misses the whole evaluation graph, and its canonical
section produces an invertible scalar. No lift to the retained curve is needed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
  {A : Scheme.{u}} (a : A ⟶ Spec (.of R[X]))

/-- The independent correction source, times the entire marked coefficient scheme. -/
def correctionCoordinateProductMap :
    pullback (a ≫ coordinateLineProjection R) (coordinateMark R B z ≫ coordinateLineProjection R) ⟶
      pullback (coordinateLineProjection R) (coordinateMark R B z ≫ coordinateLineProjection R) :=
  pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _) (by
    simpa only [Category.assoc] using (pullback.condition
      (f := a ≫ coordinateLineProjection R)
      (g := coordinateMark R B z ≫ coordinateLineProjection R)))

/-- Its literal polynomial coordinate map, including the marked coefficient ring. -/
def correctionPolynomialMap :
    pullback (a ≫ coordinateLineProjection R) (coordinateMark R B z ≫ coordinateLineProjection R) ⟶
      Spec (.of B[X]) :=
  correctionCoordinateProductMap R B z a ≫ (markedCoordinateProductIso R B z).inv

@[reassoc (attr := simp)]
theorem correctionPolynomialMap_coordinate :
    correctionPolynomialMap R B z a ≫ (markedCoordinateProductIso R B z).hom ≫
      pullback.fst _ _ = pullback.fst _ _ ≫ a := by
  simp [correctionPolynomialMap, correctionCoordinateProductMap]

/-- Disjointness of the original source and whole mark implies disjointness from
its full evaluation graph. This assertion is not limited to rational points. -/
theorem correctionPolynomialMap_disjoint_evaluationGraph
    (ha : Disjoint (Set.range a) (Set.range (coordinateMark R B z))) :
    Disjoint (Set.range (correctionPolynomialMap R B z a))
      ((evaluationGraphIdeal B (z X)).support : Set (Spec (.of B[X]))) := by
  rw [evaluationGraphIdeal, Scheme.Hom.support_ker,
    (IsClosedImmersion.isClosedEmbedding (evaluationGraph B (z X))).isClosed_range.closure_eq]
  apply Set.disjoint_left.2
  rintro t ⟨w, rfl⟩ ⟨v, hv⟩
  apply Set.disjoint_left.1 ha ⟨pullback.fst _ _ w, rfl⟩
  refine ⟨v, ?_⟩
  have h := congrArg (fun x => (pullback.fst _ _)
    ((markedCoordinateProductIso R B z).hom x)) hv
  simpa only [← Scheme.Hom.comp_apply, Category.assoc,
    correctionPolynomialMap_coordinate, evaluationGraph,
    evaluation_markedCoordinateProductIso_assoc, coordinateMarkGraph,
    pullback.lift_fst] using h

/-- The actual scalar on the independent correction source. -/
def correctionBoundaryCoordinate :=
  (correctionPolynomialMap R B z a).appTop (evaluationGraphEquation B (z X))

/-- Its entire zero ideal is the unit ideal; no reduction or dense-open replacement is used. -/
theorem zeroScheme_correctionBoundaryCoordinate
    (ha : Disjoint (Set.range a) (Set.range (coordinateMark R B z))) :
    zeroScheme _ (SheafOfModules.unit
      (pullback (a ≫ coordinateLineProjection R)
        (coordinateMark R B z ≫ coordinateLineProjection R)).ringCatSheaf)
      (correctionBoundaryCoordinate R B z a) = ⊤ := by
  rw [correctionBoundaryCoordinate, ← evaluationGraphDivisorFrame_coordinate,
    ← Modules.framePullback_coordinate, zeroScheme_congr_iso,
    zeroScheme_pullback, zeroScheme_canonicalSection]
  exact divisor_comap_eq_top_of_disjoint _ _
    (correctionPolynomialMap_disjoint_evaluationGraph R B z a ha)

/-- Multiplication by the prescribed coordinate is the required unit automorphism. -/
def correctionBoundaryUnit
    (ha : Disjoint (Set.range a) (Set.range (coordinateMark R B z))) :
    SheafOfModules.unit
      (pullback (a ≫ coordinateLineProjection R)
        (coordinateMark R B z ≫ coordinateLineProjection R)).ringCatSheaf ≅
      SheafOfModules.unit
        (pullback (a ≫ coordinateLineProjection R)
          (coordinateMark R B z ≫ coordinateLineProjection R)).ringCatSheaf := by
  letI := isIso_sectionUnitHom_of_zeroScheme_eq_top _
    (correctionBoundaryCoordinate R B z a) (zeroScheme_correctionBoundaryCoordinate R B z a ha)
  exact asIso (sectionUnitHom _ (correctionBoundaryCoordinate R B z a))

@[simp]
theorem correctionBoundaryUnit_coordinate
    (ha : Disjoint (Set.range a) (Set.range (coordinateMark R B z))) :
    (correctionBoundaryUnit R B z a ha).hom.app ⊤ 1 = correctionBoundaryCoordinate R B z a :=
  sectionUnitHom_app_one _ _

end AlgebraicGeometry.Scheme.RelativeCurvePencil
