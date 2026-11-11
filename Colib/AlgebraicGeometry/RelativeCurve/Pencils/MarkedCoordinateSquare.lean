/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.MarkedGraphGeometry
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.PolynomialCoordinateProduct
public import Colib.AlgebraicGeometry.Divisors.PolynomialEvaluationFrame

/-!
# Transport of the complete marked graph to the polynomial evaluation ideal

The full Cartesian mark condition is essential. The induced square of graph
schemes is proved by its universal property, then composed with the actual
polynomial product isomorphism. The equality is of ideal-sheaf data, including
nilpotents, rather than only of supports.

The graph-square argument is adapted from
`Motivic/Aglib/AlgebraicGeometry/EffectiveCartierDivisor/DiagonalBoundary.lean:149-173`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.Divisors

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

variable (R B : Type u) [CommRing R] [CommRing B] (z : R[X] →+* B)
  {C Y : Scheme.{u}} (q : C ⟶ Spec (.of R)) (j : Y ⟶ C)
  (p : Y ⟶ Spec (.of R[X])) (hq : j ≫ q = p ≫ coordinateLineProjection R)
  (s : Spec (.of B) ⟶ Y) (hs : s ≫ p = coordinateMark R B z)

/-- The original structural map of the mark is unchanged by the coordinate presentation. -/
theorem markedStructure_eq :
    s ≫ j ≫ q = coordinateMark R B z ≫ coordinateLineProjection R := by
  rw [hq, ← Category.assoc, hs]

/-- The actual map from the whole marked product to its polynomial coordinate product. -/
def markedCoordinateProductMap :
    pullback (j ≫ q) (s ≫ j ≫ q) ⟶
      pullback (coordinateLineProjection R) (coordinateMark R B z ≫ coordinateLineProjection R) :=
  pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _) (by
    rw [Category.assoc, ← hq, ← markedStructure_eq R B z q j p hq s hs]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem markedCoordinateProductMap_fst :
    markedCoordinateProductMap R B z q j p hq s hs ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ p := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem markedCoordinateProductMap_snd :
    markedCoordinateProductMap R B z q j p hq s hs ≫ pullback.snd _ _ =
      pullback.snd _ _ := pullback.lift_snd _ _ _

/-- The complete mark square induces a Cartesian square of the two literal graph schemes. -/
theorem markedCoordinateGraph_isPullback
    (H : IsPullback s (𝟙 (Spec (.of B))) p (coordinateMark R B z)) :
    IsPullback (𝟙 (Spec (.of B))) (markedProductGraph q j s)
      (coordinateMarkGraph R B z) (markedCoordinateProductMap R B z q j p hq s hs) where
  w := by
    apply pullback.hom_ext <;>
      simp [markedProductGraph, coordinateMarkGraph, markedCoordinateProductMap, hs]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t => by
    have hc : (t.snd ≫ pullback.fst (j ≫ q) (s ≫ j ≫ q)) ≫ p =
        t.fst ≫ coordinateMark R B z := by
      have ht := congrArg (fun v => v ≫ pullback.fst (coordinateLineProjection R)
        (coordinateMark R B z ≫ coordinateLineProjection R)) t.condition
      simpa [coordinateMarkGraph, markedCoordinateProductMap] using ht.symm
    have hy : t.fst ≫ s = t.snd ≫ pullback.fst (j ≫ q) (s ≫ j ≫ q) := by
      have he := H.lift_snd (t.snd ≫ pullback.fst (j ≫ q) (s ≫ j ≫ q)) t.fst hc
      simp only [Category.comp_id] at he
      rw [← he]
      exact H.lift_fst _ _ hc
    refine ⟨t.fst, by simp, ?_, ?_⟩
    · apply pullback.hom_ext
      · simpa [markedProductGraph] using hy
      · have ht := congrArg (fun v => v ≫ pullback.snd (coordinateLineProjection R)
          (coordinateMark R B z ≫ coordinateLineProjection R)) t.condition
        simpa [markedProductGraph, coordinateMarkGraph, markedCoordinateProductMap] using ht
    · intro v hv _
      simpa using hv)⟩

/-- The actual coordinate map to `Spec B[X]`, with its unchanged marked coefficient ring. -/
def markedPolynomialMap : pullback (j ≫ q) (s ≫ j ≫ q) ⟶ Spec (.of B[X]) :=
  markedCoordinateProductMap R B z q j p hq s hs ≫ (markedCoordinateProductIso R B z).inv

/-- The original marked graph is the full inverse image of the polynomial evaluation graph. -/
theorem markedPolynomialGraph_isPullback
    (H : IsPullback s (𝟙 (Spec (.of B))) p (coordinateMark R B z)) :
    IsPullback (𝟙 (Spec (.of B))) (markedProductGraph q j s)
      (evaluationGraph B (z X)) (markedPolynomialMap R B z q j p hq s hs) := by
  have Hiso : IsPullback (𝟙 (Spec (.of B))) (coordinateMarkGraph R B z)
      (evaluationGraph B (z X)) (markedCoordinateProductIso R B z).inv :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.id_comp, ← evaluation_markedCoordinateProductIso R B z]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl⟩
  simpa only [Category.comp_id, markedPolynomialMap] using
    (markedCoordinateGraph_isPullback R B z q j p hq s hs H).paste_horiz Hiso

/-- The equality of the actual graph ideals, with no reduction or ideal-module shortcut. -/
theorem markedPolynomialMap_comap_evaluationGraphIdeal
    (H : IsPullback s (𝟙 (Spec (.of B))) p (coordinateMark R B z)) :
    (evaluationGraphIdeal B (z X)).comap (markedPolynomialMap R B z q j p hq s hs) =
      (markedProductGraph q j s).ker :=
  (ker_eq_comap_of_cartesian
    (markedPolynomialGraph_isPullback R B z q j p hq s hs H).flip).symm

end AlgebraicGeometry.Scheme.RelativeCurvePencil
