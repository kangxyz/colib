/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FullGraphBoundaryFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryFrameCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.PolynomialBoundaryUnit

/-!
# Actual scalar coordinates on both independent whole boundaries

The graph coordinate is one at infinity and the original signed polynomial at
the mark. The correction source has its own polynomial scalar unit; gluing it
with the identity at infinity gives its whole-boundary automorphism. Neither a
frame nor either coordinate equation is supplied by the consumer.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

attribute [local instance] compactificationGraphIdeal_isEffectiveCartierDivisor

variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
  {C Y D A : Scheme.{u}} (q : C ⟶ Spec (.of R)) [IsSeparated q]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (p : Y ⟶ Spec (.of R[X])) (hq : j ≫ q = p ≫ coordinateLineProjection R)
  (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = coordinateMark R B z)
  (H : IsPullback s (𝟙 (Spec (.of B))) p (coordinateMark R B z))
  (d : D ⟶ C) (hd : Disjoint (Set.range j) (Set.range d))

/-- Literal restriction of the full graph coordinate to infinity. -/
@[simp]
theorem fullGraphCanonicalCoordinate_inl :
    (coprod.inl : pullback (pullback.snd (j ≫ q) q) d ⟶ _).appTop
      (fullGraphCanonicalCoordinate R B z q j p hq s hs H d hd) = 1 := by
  exact (boundaryCoprodFrame_inl_coordinate _ _ _ _ _
    (Classical.choose_spec (exists_fullGraphDivisorFrame R B z q j p hq s hs H d hd)).1
    (divisorSheafGlobalSection (compactificationGraph q j).ker)).trans
      (compactificationInfinityDivisorFrame_coordinate q j d hd)

/-- Literal restriction of the full graph coordinate to the unchanged mark product. -/
@[simp]
theorem fullGraphCanonicalCoordinate_inr :
    (coprod.inr : pullback (j ≫ q) (s ≫ j ≫ q) ⟶ _).appTop
      (fullGraphCanonicalCoordinate R B z q j p hq s hs H d hd) =
        markedGraphCoordinate R B z q j p hq s hs := by
  exact (boundaryCoprodFrame_inr_coordinate _ _ _ _ _
    (Classical.choose_spec (exists_fullGraphDivisorFrame R B z q j p hq s hs H d hd)).2
    (divisorSheafGlobalSection (compactificationGraph q j).ker)).trans
      (compactificationMarkedDivisorFrame_coordinate R B z q j p hq s hs H)

variable (a : A ⟶ Spec (.of R[X]))
  (ha : Disjoint (Set.range a) (Set.range (coordinateMark R B z)))

/-- The full boundary on the independent correction product. -/
abbrev correctionFullBoundary :=
  pullback (pullback.snd (a ≫ coordinateLineProjection R) q) d ⨿
    pullback (a ≫ coordinateLineProjection R) (coordinateMark R B z ≫ coordinateLineProjection R)

/-- The correction boundary scalar is constructed on its own source, not on a
pullback to the retained source curve. -/
def correctionFullBoundaryUnit :
    SheafOfModules.unit (correctionFullBoundary R B z q d a).ringCatSheaf ≅
      SheafOfModules.unit (correctionFullBoundary R B z q d a).ringCatSheaf :=
  Classical.choose (exists_boundaryCoprod_unitAutomorphism _ _
    (correctionBoundaryUnit R B z a ha))

include ha in
/-- Its actual global regular function. -/
def correctionFullBoundaryCoordinate : Γ(correctionFullBoundary R B z q d a, ⊤) :=
  Modules.Hom.app (X := correctionFullBoundary R B z q d a)
    (correctionFullBoundaryUnit R B z q d a ha).hom ⊤
    (1 : Γ(correctionFullBoundary R B z q d a, ⊤))

omit [IsSeparated q] in
@[simp]
theorem correctionFullBoundaryCoordinate_inl :
    (coprod.inl : pullback (pullback.snd (a ≫ coordinateLineProjection R) q) d ⟶ _).appTop
      (correctionFullBoundaryCoordinate R B z q d a ha) = 1 := by
  let g : pullback (pullback.snd (a ≫ coordinateLineProjection R) q) d ⟶
      correctionFullBoundary R B z q d a := coprod.inl
  apply unitAutomorphism_coordinate_of_restriction g
    (correctionFullBoundaryUnit R B z q d a ha) (Iso.refl _)
  have h := (Classical.choose_spec (exists_boundaryCoprod_unitAutomorphism
    (pullback (pullback.snd (a ≫ coordinateLineProjection R) q) d)
    (pullback (a ≫ coordinateLineProjection R)
      (coordinateMark R B z ≫ coordinateLineProjection R))
    (correctionBoundaryUnit R B z a ha))).1
  exact (congrArg (fun m => m ≫ (Modules.restrictUnitIso g).hom) h).trans
    ((Category.id_comp _).trans (Category.comp_id _).symm)

omit [IsSeparated q] in
@[simp]
theorem correctionFullBoundaryCoordinate_inr :
    (coprod.inr : pullback (a ≫ coordinateLineProjection R)
      (coordinateMark R B z ≫ coordinateLineProjection R) ⟶ _).appTop
      (correctionFullBoundaryCoordinate R B z q d a ha) =
        correctionBoundaryCoordinate R B z a := by
  exact (unitAutomorphism_coordinate_of_restriction _ _ _
    (Classical.choose_spec (exists_boundaryCoprod_unitAutomorphism _ _
      (correctionBoundaryUnit R B z a ha))).2).trans
        (correctionBoundaryUnit_coordinate R B z a ha)

end AlgebraicGeometry.Scheme.RelativeCurvePencil
