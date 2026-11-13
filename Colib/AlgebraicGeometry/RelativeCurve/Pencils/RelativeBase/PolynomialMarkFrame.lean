/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.FrameTransport
public import Colib.AlgebraicGeometry.Divisors.PolynomialEvaluationFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MarkedGraphGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.PolynomialCoordinateProduct
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.GraphNeighborhood
public import Colib.AlgebraicGeometry.Scheme.AffinePullbackSections

/-!
# The graph frame on the whole marked polynomial product

The marked coordinate comparison identifies the actual graph with
polynomial evaluation at the original mark. Its global frame therefore
exists on the whole polynomial line over the full marked scheme.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.Modules Polynomial

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable (R B : Type u) [CommRing R] [CommRing B] (z : Polynomial R →+* B)

private theorem polynomialMark_comap_graphIdeal :
    (evaluationGraphIdeal B (z X)).comap (markedCoordinateProductIso R B z).inv =
      (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker := by
  have he : evaluationGraph B (z X) ≫ (markedCoordinateProductIso R B z).hom =
      relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z) :=
    evaluation_markedCoordinateProductIso R B z
  have h : IsPullback
      (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z))
      (𝟙 _) (markedCoordinateProductIso R B z).inv (evaluationGraph B (z X)) :=
    IsPullback.of_vert_isIso ⟨by rw [← he, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]⟩
  exact (ker_eq_comap_of_cartesian h).symm

/-- The native marked graph frame on the entire polynomial line, with the
original full mark. -/
@[no_expose]
def polynomialRelativeBoundaryGraphFrame :
    divisorSheaf (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker ≅
      SheafOfModules.unit (pullback (coordinateLineProjection R)
        (coordinateMark R B z ≫ coordinateLineProjection R)).ringCatSheaf := by
  let D := evaluationGraphIdeal B (z X)
  let E := (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B z)).ker
  let m := (markedCoordinateProductIso R B z).inv
  have h : D.comap m = E := polynomialMark_comap_graphIdeal R B z
  let : IsEffectiveCartierDivisor E := by
    rw [← h]
    exact isPullbackDefined_of_flat m D inferInstance
  exact (divisorComapEqIso m D E h).symm ≪≫
    framePullback m (evaluationGraphDivisorFrame B (z X))

/-- The graph frame over the original affine marked scheme. -/
@[no_expose]
def affineMarkPolynomialBoundaryGraphFrame (R : Type u) [CommRing R]
    {Z : Scheme.{u}} [IsAffine Z] (z : Z ⟶ Spec (.of (Polynomial R))) :
    divisorSheaf (relativeBoundaryGraph (coordinateLineProjection R) z).ker ≅
      SheafOfModules.unit (pullback (coordinateLineProjection R)
        (z ≫ coordinateLineProjection R)).ringCatSheaf := by
  let B : Type u := Γ(Z, ⊤)
  let ζ : Polynomial R →+* B := specSectionsMap z
  let q := coordinateLineProjection R
  let z' := coordinateMark R B ζ
  let eZ : Spec (.of B) ≅ Z := Z.isoSpec.symm
  have hcoord : z' = eZ.hom ≫ z := Spec_map_specSectionsMap z
  have h : IsPullback (pullback.fst q (z' ≫ q))
      (pullback.snd q (z' ≫ q) ≫ eZ.hom) q (z ≫ q) := by
    refine (IsPullback.of_hasPullback q (z' ≫ q)).of_iso
      (Iso.refl _) (Iso.refl _) eZ (Iso.refl _) (by simp) (by simp) (by simp) ?_
    rw [Iso.refl_hom, Category.comp_id, hcoord, Category.assoc]
  let e := h.isoPullback
  have hg : relativeBoundaryGraph q z' ≫ e.hom = eZ.hom ≫ relativeBoundaryGraph q z := by
    apply pullback.hom_ext
    · simp only [Category.assoc, e, IsPullback.isoPullback_hom_fst,
        relativeBoundaryGraph_fst, hcoord]
    · simp only [Category.assoc, e, IsPullback.isoPullback_hom_snd,
        relativeBoundaryGraph_snd_assoc, relativeBoundaryGraph_snd, Category.comp_id]
  have H : IsPullback (relativeBoundaryGraph q z) eZ.inv e.inv
      (relativeBoundaryGraph q z') := by
    apply IsPullback.of_vert_isIso
    constructor
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc, hg,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  let D := (relativeBoundaryGraph q z').ker
  let E := (relativeBoundaryGraph q z).ker
  have hD : IsEffectiveCartierDivisor D := by
    change IsEffectiveCartierDivisor
      (relativeBoundaryGraph (coordinateLineProjection R) (coordinateMark R B ζ)).ker
    rw [← polynomialMark_comap_graphIdeal R B ζ]
    exact isPullbackDefined_of_flat _ _ inferInstance
  have hker : D.comap e.inv = E := (ker_eq_comap_of_cartesian H).symm
  have hE : IsEffectiveCartierDivisor E := by
    rw [← hker]
    exact isPullbackDefined_of_flat _ _ hD
  exact (divisorComapEqIso e.inv D E hker).symm ≪≫
    framePullback e.inv (polynomialRelativeBoundaryGraphFrame R B ζ)

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
