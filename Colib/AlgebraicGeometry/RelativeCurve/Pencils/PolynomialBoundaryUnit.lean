/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.PolynomialCoordinateProduct
public import Colib.AlgebraicGeometry.Divisors.PolynomialEvaluationFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryCoordinateUnit
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

local notation "V" => pullback (a ≫ coordinateLineProjection R)
  (coordinateMark R B z ≫ coordinateLineProjection R)
local notation "W" => pullback (coordinateLineProjection R)
  (coordinateMark R B z ≫ coordinateLineProjection R)

/-- The independent correction source, times the entire marked coefficient scheme. -/
def correctionCoordinateProductMap : V ⟶ W :=
  pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _) (by
    simpa only [Category.assoc] using (pullback.condition
      (f := a ≫ coordinateLineProjection R)
      (g := coordinateMark R B z ≫ coordinateLineProjection R)))

/-- Its literal polynomial coordinate map, including the marked coefficient ring. -/
def correctionPolynomialMap : V ⟶ Spec (.of B[X]) :=
  correctionCoordinateProductMap R B z a ≫ (markedCoordinateProductIso R B z).inv

@[reassoc (attr := simp)]
theorem correctionPolynomialMap_coordinate :
    correctionPolynomialMap R B z a ≫ (markedCoordinateProductIso R B z).hom ≫
      pullback.fst _ _ = pullback.fst _ _ ≫ a := by
  change (correctionCoordinateProductMap R B z a ≫ (markedCoordinateProductIso R B z).inv) ≫
    (markedCoordinateProductIso R B z).hom ≫ pullback.fst _ _ = _
  rw [Category.assoc, Iso.inv_hom_id_assoc]
  exact pullback.lift_fst _ _ _

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
  let j : V ⟶ A := pullback.fst _ _
  let p : W ⟶ Spec (.of R[X]) := pullback.fst _ _
  let e := markedCoordinateProductIso R B z
  apply Set.disjoint_left.1 ha ⟨j w, rfl⟩
  refine ⟨v, ?_⟩
  have h := congrArg (fun x => p (e.hom x)) hv
  change (evaluationGraph B (z X) ≫ e.hom ≫ p) v =
    (correctionPolynomialMap R B z a ≫ e.hom ≫ p) w at h
  have hl : evaluationGraph B (z X) ≫ e.hom ≫ p = coordinateMark R B z :=
    (evaluation_markedCoordinateProductIso_assoc R B z p).trans (pullback.lift_fst _ _ _)
  have hr : correctionPolynomialMap R B z a ≫ e.hom ≫ p = j ≫ a :=
    correctionPolynomialMap_coordinate R B z a
  exact (congrArg (fun f => f v) hl).symm.trans (h.trans (congrArg (fun f => f w) hr))

/-- The actual scalar on the independent correction source. -/
def correctionBoundaryCoordinate : Γ(V, ⊤) :=
  (correctionPolynomialMap R B z a).appTop (evaluationGraphEquation B (z X))

/-- Its entire zero ideal is the unit ideal; no reduction or dense-open replacement is used. -/
theorem zeroScheme_correctionBoundaryCoordinate
    (ha : Disjoint (Set.range a) (Set.range (coordinateMark R B z))) :
    zeroScheme V (SheafOfModules.unit (V).ringCatSheaf)
      (correctionBoundaryCoordinate R B z a) = ⊤ := by
  let f := correctionPolynomialMap R B z a
  let D := evaluationGraphIdeal B (z X)
  let e := Modules.framePullback f (evaluationGraphDivisorFrame B (z X))
  let s := pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D)
  let U : (V).Modules := SheafOfModules.unit (V).ringCatSheaf
  have hc : Modules.Hom.app e.hom ⊤ s = correctionBoundaryCoordinate R B z a :=
    (Modules.framePullback_coordinate f (evaluationGraphDivisorFrame B (z X))
      (divisorSheafGlobalSection D)).trans
        (congrArg (fun c => f.appTop c) (evaluationGraphDivisorFrame_coordinate B (z X)))
  exact (congrArg (fun c : Γ(U, ⊤) => zeroScheme V U c) hc.symm).trans
    (zeroScheme_boundaryCoordinate_eq_top D f
      (correctionPolynomialMap_disjoint_evaluationGraph R B z a ha) e)

/-- Multiplication by the prescribed coordinate is the required unit automorphism. -/
def correctionBoundaryUnit
    (ha : Disjoint (Set.range a) (Set.range (coordinateMark R B z))) :
    SheafOfModules.unit (V).ringCatSheaf ≅ SheafOfModules.unit (V).ringCatSheaf := by
  let U : (V).Modules := SheafOfModules.unit (V).ringCatSheaf
  exact (@frameOfZeroSchemeTop V U (Stacks.Ample.isInvertibleModule_unit V)
    (correctionBoundaryCoordinate R B z a)
    (zeroScheme_correctionBoundaryCoordinate R B z a ha)).symm

@[simp]
theorem correctionBoundaryUnit_coordinate
    (ha : Disjoint (Set.range a) (Set.range (coordinateMark R B z))) :
    Modules.Hom.app (correctionBoundaryUnit R B z a ha).hom ⊤ (1 : Γ(V, ⊤)) =
      correctionBoundaryCoordinate R B z a :=
  @sectionUnitHom_app_one V (SheafOfModules.unit (V).ringCatSheaf)
    (correctionBoundaryCoordinate R B z a)

end AlgebraicGeometry.Scheme.RelativeCurvePencil
