/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# The actual affine-line product and its evaluation graph

The polynomial spectrum is identified with the full product by its actual ring
maps. The evaluation graph is carried to the graph of the supplied coordinate
map, with the original coefficient scheme unchanged.

Adapted from `Motivic/Aglib/AlgebraicGeometry/EffectiveCartierDivisor/
CoordinateGraphIdeal.lean:81-132` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable (R B : Type u) [CommRing R] [CommRing B]

/-- The polynomial base-change square, at the literal coefficient homomorphism. -/
theorem polynomialCoordinate_isPushout (f : R →+* B) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (C : R →+* R[X]))
      (CommRingCat.ofHom (C : B →+* B[X])) (CommRingCat.ofHom (mapRingHom f)) := by
  let : Algebra R B := f.toAlgebra
  let : Algebra R[X] B[X] := Polynomial.algebra R B
  have : IsScalarTower R R[X] B[X] :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change C (f r) = mapRingHom f (C r)
      simp
  exact CommRingCat.isPushout_of_isPushout R B R[X] B[X]

/-- The full polynomial product, with both projections specified. -/
def polynomialCoordinateProductIso (f : R →+* B) :
    Spec (.of B[X]) ≅ pullback
      (Spec.map (CommRingCat.ofHom (C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (polynomialCoordinate_isPushout R B f)).flip.isoPullback

@[reassoc (attr := simp)]
theorem polynomialCoordinateProductIso_hom_fst (f : R →+* B) :
    (polynomialCoordinateProductIso R B f).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (mapRingHom f)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (polynomialCoordinate_isPushout R B f)).flip.isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem polynomialCoordinateProductIso_hom_snd (f : R →+* B) :
    (polynomialCoordinateProductIso R B f).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (C : B →+* B[X])) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (polynomialCoordinate_isPushout R B f)).flip.isoPullback_hom_snd

/-- The affine line projection used by the marked coordinate map. -/
abbrev coordinateLineProjection : Spec (.of R[X]) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (C : R →+* R[X]))

/-- The unchanged coordinate map of the full mark scheme. -/
abbrev coordinateMark (z : R[X] →+* B) : Spec (.of B) ⟶ Spec (.of R[X]) :=
  Spec.map (CommRingCat.ofHom z)

/-- The product in the composed scheme-morphism spelling of the marked geometry. -/
def markedCoordinateProductIso (z : R[X] →+* B) :
    Spec (.of B[X]) ≅ pullback (coordinateLineProjection R)
      (coordinateMark R B z ≫ coordinateLineProjection R) :=
  polynomialCoordinateProductIso R B (z.comp C) ≪≫
    pullback.congrHom rfl (by rw [← Spec.map_comp]; rfl)

@[reassoc (attr := simp)]
theorem markedCoordinateProductIso_hom_fst (z : R[X] →+* B) :
    (markedCoordinateProductIso R B z).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (mapRingHom (z.comp C))) := by
  rw [markedCoordinateProductIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]
  exact polynomialCoordinateProductIso_hom_fst R B (z.comp C)

@[reassoc (attr := simp)]
theorem markedCoordinateProductIso_hom_snd (z : R[X] →+* B) :
    (markedCoordinateProductIso R B z).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (C : B →+* B[X])) := by
  rw [markedCoordinateProductIso, Iso.trans_hom, Category.assoc,
    pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
  exact polynomialCoordinateProductIso_hom_snd R B (z.comp C)

/-- The literal graph of the mark in the affine-line product. -/
def coordinateMarkGraph (z : R[X] →+* B) :
    Spec (.of B) ⟶ pullback (coordinateLineProjection R)
      (coordinateMark R B z ≫ coordinateLineProjection R) :=
  pullback.lift (coordinateMark R B z) (𝟙 _) (by simp)

/-- Evaluation at the original marked coordinate is exactly the original graph. -/
@[reassoc]
theorem evaluation_markedCoordinateProductIso (z : R[X] →+* B) :
    Spec.map (CommRingCat.ofHom (evalRingHom (z X))) ≫
      (markedCoordinateProductIso R B z).hom = coordinateMarkGraph R B z := by
  apply pullback.hom_ext
  · simp only [Category.assoc, markedCoordinateProductIso_hom_fst, coordinateMarkGraph,
      pullback.lift_fst, coordinateMark, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  · simp only [Category.assoc, markedCoordinateProductIso_hom_snd, coordinateMarkGraph,
      pullback.lift_snd, ← Spec.map_comp]
    rw [← Spec.map_id]
    congr 1
    ext r
    simp

end AlgebraicGeometry.Scheme.RelativeCurvePencil
