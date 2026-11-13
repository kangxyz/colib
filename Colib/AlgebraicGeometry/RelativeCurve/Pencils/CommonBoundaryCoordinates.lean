/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.CommonBoundaryGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FullBoundaryCoordinates

/-!
# The actual common-boundary scalar equality

The complete mark square produces the first coordinate. The independent
correction-source map produces the second coordinate. Their equality is forced
by alpha composed with the polynomial map equalling beta composed with the
correction map. The infinity coordinates are both one. No scalar comparison,
section matching, or homotopy equation is added as a hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- Actual global regular functions on a coproduct are determined by their two
literal component restrictions. -/
theorem globalSections_coprod_ext {X Y : Scheme.{u}} {a b : Γ(X ⨿ Y, ⊤)}
    (hl : (coprod.inl : X ⟶ X ⨿ Y).appTop a = (coprod.inl : X ⟶ X ⨿ Y).appTop b)
    (hr : (coprod.inr : Y ⟶ X ⨿ Y).appTop a = (coprod.inr : Y ⟶ X ⨿ Y).appTop b) :
    a = b := by
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.coprodPresheafObjIso (⊤ : (X ⨿ Y).Opens)).hom).injective
  apply Concrete.limit_ext
  rintro ⟨c⟩
  cases c
  · have h := Scheme.coprodPresheafObjIso_hom_fst (X := X) (Y := Y) ⊤
    exact (congrArg (fun m => m a) h).trans (hl.trans (congrArg (fun m => m b) h).symm)
  · have h := Scheme.coprodPresheafObjIso_hom_snd (X := X) (Y := Y) ⊤
    exact (congrArg (fun m => m a) h).trans (hr.trans (congrArg (fun m => m b) h).symm)

private theorem appTop_coprod_map_inl {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (s : Γ(X' ⨿ Y', ⊤)) :
    (coprod.inl : X ⟶ X ⨿ Y).appTop ((coprod.map f g).appTop s) =
      f.appTop ((coprod.inl : X' ⟶ X' ⨿ Y').appTop s) :=
  congrArg (fun (m : X ⟶ X' ⨿ Y') => m.appTop s) (coprod.inl_map f g)

private theorem appTop_coprod_map_inr {X X' Y Y' : Scheme.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') (s : Γ(X' ⨿ Y', ⊤)) :
    (coprod.inr : Y ⟶ X ⨿ Y).appTop ((coprod.map f g).appTop s) =
      g.appTop ((coprod.inr : Y' ⟶ X' ⨿ Y').appTop s) :=
  congrArg (fun (m : Y ⟶ X' ⨿ Y') => m.appTop s) (coprod.inr_map f g)

variable (R K : Type u) [CommRing R] [CommRing K] (z : R[X] →+* K)
  {C Y A B D : Scheme.{u}} (π : C ⟶ Spec (.of R))
  (j : Y ⟶ C) (p : Y ⟶ Spec (.of R[X]))
  (hq : j ≫ π = p ≫ coordinateLineProjection R)
  (a : A ⟶ Spec (.of R[X])) (α : B ⟶ Y) (β : B ⟶ A)
  (h : α ≫ p = β ≫ a)
  (s : Spec (.of K) ⟶ Y) (hs : s ≫ p = coordinateMark R K z)

/-- The two independent zero-boundary maps have exactly the same polynomial
coordinate map, not merely the same closed-point values. -/
theorem commonZero_polynomialMap_eq :
    commonZeroToLambda π j α s ≫ markedPolynomialMap R K z π j p hq s hs =
      commonZeroToPsi (coordinateLineProjection R) π j p hq a α β h
        (coordinateMark R K z) s hs ≫ correctionPolynomialMap R K z a := by
  unfold markedPolynomialMap correctionPolynomialMap
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext
  · simp only [Category.assoc, markedCoordinateProductMap_fst,
      correctionCoordinateProductMap, pullback.lift_fst,
      commonZeroToLambda, retainedSourceChange_fst_assoc,
      commonZeroToPsi, pullback.lift_fst_assoc]
    simpa only [Category.assoc] using
      congrArg (fun m => pullback.fst (commonProjection π j α) (s ≫ j ≫ π) ≫ m) h
  · simp [commonZeroToLambda, commonZeroToPsi, markedCoordinateProductMap,
      correctionCoordinateProductMap, Category.assoc]

/-- Equality of the actual whole-zero-boundary scalars under those two maps. -/
theorem commonZero_coordinate_eq :
    (commonZeroToLambda π j α s).appTop (markedGraphCoordinate R K z π j p hq s hs) =
      (commonZeroToPsi (coordinateLineProjection R) π j p hq a α β h
        (coordinateMark R K z) s hs).appTop (correctionBoundaryCoordinate R K z a) := by
  unfold markedGraphCoordinate correctionBoundaryCoordinate
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    commonZero_polynomialMap_eq R K z π j p hq a α β h s hs]

variable [IsSeparated π] [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (H : IsPullback s (𝟙 (Spec (.of K))) p (coordinateMark R K z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))
  (ha : Disjoint (Set.range a) (Set.range (coordinateMark R K z)))

/-- The canonical graph coordinate and the independently constructed correction
unit agree on the entire common boundary. This is the actual geometric scalar
comparison consumed by the normalized pencil construction. -/
theorem commonBoundary_coordinate_eq :
    (commonBoundaryToLambda π j α s d).appTop
      (fullGraphCanonicalCoordinate R K z π j p hq s hs H d hd) =
    (commonBoundaryToPsi (coordinateLineProjection R) π j p hq a α β h
      (coordinateMark R K z) s hs d).appTop
        (correctionFullBoundaryCoordinate R K z π d a ha) := by
  let fL := constantInfinitySourceMap α (j ≫ π) π (commonProjection π j α) rfl d
  let fR := constantInfinitySourceMap β (a ≫ coordinateLineProjection R) π
    (commonProjection π j α)
    (commonProjection_fixed (coordinateLineProjection R) π j p hq a α β h) d
  let gL := commonZeroToLambda π j α s
  let gR := commonZeroToPsi (coordinateLineProjection R) π j p hq a α β h
    (coordinateMark R K z) s hs
  let cL := fullGraphCanonicalCoordinate R K z π j p hq s hs H d hd
  let cR := correctionFullBoundaryCoordinate R K z π d a ha
  apply globalSections_coprod_ext
  · have hL := (appTop_coprod_map_inl fL gL cL).trans
      (congrArg (fun u => fL.appTop u)
        (fullGraphCanonicalCoordinate_inl R K z π j p hq s hs H d hd))
    have hR := (appTop_coprod_map_inl fR gR cR).trans
      (congrArg (fun u => fR.appTop u) (correctionFullBoundaryCoordinate_inl R K z π d a ha))
    exact (hL.trans (map_one fL.appTop.hom)).trans (hR.trans (map_one fR.appTop.hom)).symm
  · have hL := (appTop_coprod_map_inr fL gL cL).trans
      (congrArg (fun u => gL.appTop u)
        (fullGraphCanonicalCoordinate_inr R K z π j p hq s hs H d hd))
    have hR := (appTop_coprod_map_inr fR gR cR).trans
      (congrArg (fun u => gR.appTop u) (correctionFullBoundaryCoordinate_inr R K z π d a ha))
    exact hL.trans ((commonZero_coordinate_eq R K z π j p hq a α β h s hs).trans hR.symm)

end AlgebraicGeometry.Scheme.RelativeCurvePencil
