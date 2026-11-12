/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MarkedCoordinateSquare
public import Colib.AlgebraicGeometry.Divisors.FrameTransport

/-!
# The genuine marked-product frame of the compactification graph line

The compactification is separated, with a smooth retained open relative curve.
The complete Cartesian mark square identifies the marked graph ideal with the
pullback of the literal polynomial evaluation ideal. Both ideals are Cartier,
so the native ideal comparison is an isomorphism, compatible with inclusions.

The frame of the native dual graph ideal is obtained from multiplication by
`X - C (z X)` in the polynomial evaluation kernel. The canonical graph section
has exactly the pulled-back signed polynomial difference as coordinate, even
on the graph intersection. No frame or target coordinate equation is supplied
as a hypothesis.

This is the native replacement of the marked component in
`Motivic/Aglib/AlgebraicGeometry/Modules/Invertible/Frames/RelativeCurve/
FullBoundaryFrames.lean` at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
  {C Y : Scheme.{u}} (q : C ⟶ Spec (.of R)) [IsSeparated q]
  (j : Y ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (p : Y ⟶ Spec (.of R[X])) (hq : j ≫ q = p ≫ coordinateLineProjection R)
  (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = coordinateMark R B z)
  (H : IsPullback s (𝟙 (Spec (.of B))) p (coordinateMark R B z))

/-- Exact transport of the compactification graph ideal to the full marked graph ideal. -/
def compactificationMarkedIdealIso :
    (Stacks.RingedSpace.pullbackFunctor (markedProductMap q j s).toLRSHom.toShHom).obj
      (Eta.idealSheaf (compactificationGraph q j).ker) ≅
        Eta.idealSheaf (markedProductGraph q j s).ker := by
  haveI := compactificationGraphIdeal_isEffectiveCartierDivisor q j
  exact idealComapEqIso (markedProductMap q j s) (compactificationGraph q j).ker
    (markedProductGraph q j s).ker (compactificationGraphIdeal_comap_markedProductMap q j s)

/-- Exact transport of the polynomial evaluation ideal to that same entire marked graph. -/
def polynomialMarkedIdealIso :
    (Stacks.RingedSpace.pullbackFunctor
      (markedPolynomialMap R B z q j p hq s hs).toLRSHom.toShHom).obj
        (Eta.idealSheaf (evaluationGraphIdeal B (z X))) ≅
          Eta.idealSheaf (markedProductGraph q j s).ker :=
  idealComapEqIso (markedPolynomialMap R B z q j p hq s hs)
    (evaluationGraphIdeal B (z X)) (markedProductGraph q j s).ker
    (markedPolynomialMap_comap_evaluationGraphIdeal R B z q j p hq s hs H)

/-- The polynomial ideal comparison is the native map preserving the actual ideal inclusion. -/
theorem polynomialMarkedIdealIso_hom_inclusion :
    (polynomialMarkedIdealIso R B z q j p hq s hs H).hom ≫
      Eta.idealSheafι (markedProductGraph q j s).ker =
        Stacks.IdealTorsion.Eta.pullbackIdealIncl
          (markedPolynomialMap R B z q j p hq s hs).toLRSHom.toShHom
          (Eta.idealSheaf (evaluationGraphIdeal B (z X)))
          (Eta.idealSheafι (evaluationGraphIdeal B (z X))) :=
  idealComapEqIso_hom_inclusion _ _ _ _

/-- The signed polynomial difference on the unchanged full marked product. -/
def markedGraphCoordinate : Γ(pullback (j ≫ q) (s ≫ j ≫ q), ⊤) :=
  (markedPolynomialMap R B z q j p hq s hs).appTop (evaluationGraphEquation B (z X))

/-- The native graph line acquires its actual polynomial coordinate frame on the full mark. -/
def compactificationMarkedDivisorFrame :
    (Scheme.Modules.pullback (markedProductMap q j s)).obj
      (divisorSheaf (compactificationGraph q j).ker) ≅
        SheafOfModules.unit (pullback (j ≫ q) (s ≫ j ≫ q)).ringCatSheaf := by
  haveI := compactificationGraphIdeal_isEffectiveCartierDivisor q j
  exact divisorComapEqIso (markedProductMap q j s) (compactificationGraph q j).ker
      (markedProductGraph q j s).ker
      (compactificationGraphIdeal_comap_markedProductMap q j s) ≪≫
    (divisorComapEqIso (markedPolynomialMap R B z q j p hq s hs)
      (evaluationGraphIdeal B (z X)) (markedProductGraph q j s).ker
      (markedPolynomialMap_comap_evaluationGraphIdeal R B z q j p hq s hs H)).symm ≪≫
    Scheme.Modules.framePullback (markedPolynomialMap R B z q j p hq s hs)
      (evaluationGraphDivisorFrame B (z X))

/-- The prescribed whole-mark coordinate of the native canonical graph section is the
literal pulled-back polynomial difference. It is allowed to vanish where the graph meets
the mark; the frame remains an isomorphism there. -/
theorem compactificationMarkedDivisorFrame_coordinate :
    (compactificationMarkedDivisorFrame R B z q j p hq s hs H).hom.app ⊤
      (pullbackGlobalSections (markedProductMap q j s)
        (divisorSheaf (compactificationGraph q j).ker)
        (divisorSheafGlobalSection (compactificationGraph q j).ker)) =
          markedGraphCoordinate R B z q j p hq s hs := by
  have := compactificationGraphIdeal_isEffectiveCartierDivisor q j
  let f := markedPolynomialMap R B z q j p hq s hs
  let D := evaluationGraphIdeal B (z X)
  let E := (markedProductGraph q j s).ker
  let h := markedPolynomialMap_comap_evaluationGraphIdeal R B z q j p hq s hs H
  let e := divisorComapEqIso f D E h
  have hinv : e.inv.app ⊤ (divisorSheafGlobalSection E) =
      pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D) := by
    let t := pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D)
    have hs : e.hom.app ⊤ t = divisorSheafGlobalSection E :=
      divisorComapEqIso_canonicalSection f D E h
    have he := congrArg (fun m => m.app ⊤ t) e.hom_inv_id
    exact (congrArg (fun x => e.inv.app ⊤ x) hs).symm.trans he
  change (Scheme.Modules.framePullback f (evaluationGraphDivisorFrame B (z X))).hom.app ⊤
    (e.inv.app ⊤ ((divisorComapEqIso (markedProductMap q j s)
      (compactificationGraph q j).ker E
      (compactificationGraphIdeal_comap_markedProductMap q j s)).hom.app ⊤
        (pullbackGlobalSections (markedProductMap q j s)
          (divisorSheaf (compactificationGraph q j).ker)
          (divisorSheafGlobalSection (compactificationGraph q j).ker)))) = _
  rw [divisorComapEqIso_canonicalSection, hinv, Scheme.Modules.framePullback_coordinate,
    evaluationGraphDivisorFrame_coordinate]
  rfl

end AlgebraicGeometry.Scheme.RelativeCurvePencil
