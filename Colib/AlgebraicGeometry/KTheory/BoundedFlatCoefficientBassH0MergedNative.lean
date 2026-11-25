/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0ReindexedSupport

/-!
# Native evaluation in the common Bass 62-simplex

Evaluation agrees pointwise with the original positive and inverse charts,
the realized bottom product, and the full H₀ cylinder face. This does not
identify the separate H₀ top comparison or construct the remaining cube.
Adapted from `BassH0MergedNative.lean` and `BassH0MergedFaces.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite Convexity Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Native evaluation is unchanged on every supported old face, at every original level. -/
theorem old_family_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋44⦌)
    (h : Monotone (oldIndex ∘ α.toOrderHom)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map oldIndex (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (BoundedFlatCoefficientBassReferenceMerge.simplex P u v) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map (oldFace α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, old_face, prespectrumSimplexFamily_face]

/-- The same value preservation holds on every supported original H0 face. -/
theorem h0_family_face {k : ℕ} (α : ⦋k⦌ ⟶ ⦋30⦌)
    (h : Monotone (h0Index ∘ α.toOrderHom)) (n : ℕ)
    (z : StdSimplex ℝ (Fin (k + 1)))
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n
      (StdSimplex.map h0Index (StdSimplex.map α.toOrderHom z), x) =
    prespectrumSimplexFamily (BoundedFlatCoefficientBassH0Merge.simplex P u v) n
      (StdSimplex.map α.toOrderHom z, x) := by
  rw [← StdSimplex.map_comp]
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map (h0Face α h).toOrderHom z, x) = _
  rw [prespectrumSimplexFamily_face, h0_face, prespectrumSimplexFamily_face]

/-- Every actual positive chart value is retained through its original supported triple face. -/
theorem plus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (plusParameter (r, s), x) =
      (boundedAboveFlatCoefficientBassCompositionPlusChart P u v).level n
        (r, (s, (K (polynomialProjection P a)).map n x)) := by
  calc
    _ = prespectrumSimplexFamily (BoundedFlatCoefficientBassReferenceMerge.simplex P u v) n
        (BoundedFlatCoefficientBassReferenceMerge.plusParameter (r, s), x) := by
      obtain ⟨i, y, hy⟩ := map_supported
        (BoundedFlatCoefficientBassOverlap.plusFace ≫
          BoundedFlatCoefficientBassReferenceMerge.chartFace)
        (paused_chart_in (r, s))
      have hp : BoundedFlatCoefficientBassReferenceMerge.plusParameter (r, s) =
          StdSimplex.map (rectangleFace i ≫ (BoundedFlatCoefficientBassOverlap.plusFace ≫
            BoundedFlatCoefficientBassReferenceMerge.chartFace)).toOrderHom y := by
        refine Eq.trans ?_ hy.symm
        change StdSimplex.map BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
          (StdSimplex.map BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom _) =
          StdSimplex.map (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom ∘
            BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom) _
        rw [StdSimplex.map_comp]
      change prespectrumSimplexFamily (simplex P u v) n
        (StdSimplex.map oldIndex (BoundedFlatCoefficientBassReferenceMerge.plusParameter
          (r, s)), x) = _
      rw [hp]
      exact old_family_face P u v _ (oldPlus_monotone i) n y x
    _ = _ := BoundedFlatCoefficientBassReferenceMerge.plus_native P u v n r s x

/-- Every actual inverse chart value is retained, including its distinct original chart maps. -/
theorem minus_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (minusParameter (r, s), x) =
      (boundedAboveFlatCoefficientBassCompositionMinusChart P u v).level n
        (r, (s, (K (polynomialProjection P a)).map n x)) := by
  calc
    _ = prespectrumSimplexFamily (BoundedFlatCoefficientBassReferenceMerge.simplex P u v) n
        (BoundedFlatCoefficientBassReferenceMerge.minusParameter (r, s), x) := by
      obtain ⟨i, y, hy⟩ := map_supported
        (BoundedFlatCoefficientBassOverlap.minusFace ≫
          BoundedFlatCoefficientBassReferenceMerge.chartFace)
        (paused_chart_in (r, s))
      have hp : BoundedFlatCoefficientBassReferenceMerge.minusParameter (r, s) =
          StdSimplex.map (rectangleFace i ≫ (BoundedFlatCoefficientBassOverlap.minusFace ≫
            BoundedFlatCoefficientBassReferenceMerge.chartFace)).toOrderHom y := by
        refine Eq.trans ?_ hy.symm
        change StdSimplex.map BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
          (StdSimplex.map BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom _) =
          StdSimplex.map (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom ∘
            BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom) _
        rw [StdSimplex.map_comp]
      change prespectrumSimplexFamily (simplex P u v) n
        (StdSimplex.map oldIndex (BoundedFlatCoefficientBassReferenceMerge.minusParameter
          (r, s)), x) = _
      rw [hp]
      exact old_family_face P u v _ (oldMinus_monotone i) n y x
    _ = _ := BoundedFlatCoefficientBassReferenceMerge.minus_native P u v n r s x

/-- The whole prescribed original bottom remains the actual independently varying product family. -/
theorem bottom_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (bottomParameter.{u} (r, t), x) =
      (Homotopy.precomp (boundedAboveFlatCoefficientBassSquareComparison P a)
        (boundedAboveFlatCoefficientLaurentCompositionHomotopy P u v)).level n
        (r, HomotopyPushout.cylinder
          (K (polynomialProjection P a))
          (K (polynomialProjection P a)) n (t, x)) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map oldIndex
      (StdSimplex.map BoundedFlatCoefficientBassReferenceMerge.bottomFace.toOrderHom
        (BoundedFlatCoefficientBassLaurentBottomFace.parameter (r, t))), x) = _
  rw [old_family_face P u v BoundedFlatCoefficientBassReferenceMerge.bottomFace bottom_monotone]
  exact BoundedFlatCoefficientBassReferenceMerge.bottom_native P u v n r t x

/-- Original H0 values retain their exact pasted parameters via the six actual triple supports. -/
theorem h0_family (n : ℕ) (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (h0Parameter z, x) =
      prespectrumSimplexFamily (BoundedFlatCoefficientBassH0Merge.simplex P u v) n
        (BoundedFlatCoefficientBassH0Diagram.parameter z, x) := by
  change prespectrumSimplexFamily (simplex P u v) n
    (StdSimplex.map h0Index (BoundedFlatCoefficientBassH0Diagram.parameter z), x) = _
  obtain ⟨α, hα, i, y, hy⟩ := h0_support z
  rw [← hy]
  rcases Set.mem_insert_iff.mp hα with hα | hα
  · subst α
    exact h0_family_face P u v _ (h0Plus_monotone i) n y x
  · have hα' := Set.mem_singleton_iff.mp hα
    subst α
    exact h0_family_face P u v _ (h0Minus_monotone i) n y x

/-- The complete original H0 cylinder face is now evaluated in the same actual common simplex. -/
theorem h0_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (W (space (op P, a)))).space n) :
    prespectrumSimplexFamily (simplex P u v) n (h0Parameter (s, t), x) =
      (boundedAboveFlatCoefficientBassComparisonHomotopy P (u ≫ v)).level n
        (s, HomotopyPushout.cylinder
          (K (polynomialProjection P a))
          (K (polynomialProjection P a)) n (t, x)) := by
  rw [h0_family, BoundedFlatCoefficientBassH0Merge.simplex_original]
  exact BoundedFlatCoefficientBassH0Diagram.composition_H0 P u v n s t x

/-- The genuine common family fixes the original basepoint at every scalar parameter. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 63)) :
    prespectrumSimplexFamily (simplex P u v) n
      (z, (originalPrespectrum (W (space (op P, a)))).point n) =
      (originalPrespectrum (W
        (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  prespectrumSimplexFamily_point (simplex P u v) n z

/-- The independent native structure time remains separate from every scalar face parameter. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 63))
    (x : (originalPrespectrum (W (space (op P, a)))).space n)
    (t : unitInterval) :
    prespectrumSimplexFamily (simplex P u v) (n + 1)
      (z, (originalPrespectrum
        (W (space (op P, a)))).structureMap n x t) =
    (originalPrespectrum (W
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (simplex P u v) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex P u v) n z x t

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Merged
