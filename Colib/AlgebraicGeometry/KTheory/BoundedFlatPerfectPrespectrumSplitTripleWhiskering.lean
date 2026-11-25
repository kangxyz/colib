/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleEvaluation
public import Colib.KTheory.Waldhausen.Iterated.CompositionHomotopyNaturality
public import Colib.Topology.Prespectrum.RelativeHomotopyWhiskering

/-!
# Whiskered faces of the split pullback comparison

The second face in each route evaluates the original binary comparison after
exact whiskering. The simplex lift retains both comparison times, including
at the based-loop level zero.

Adapted from Quillen `BoundedFlat/SplitTripleNative.lean:38-86` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex

open BoundedFlatPerfectTripleSimplex (left right target)

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "K" => boundedAboveFlatPerfectPullbackPrespectrumMap
local notation "NE" => boundedAboveFlatPerfectNormalizedPullback_exact
local notation "NZ" => boundedAboveFlatPerfectNormalizedPullback_obj_zero

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

set_option maxHeartbeats 400000 in
-- Identifying the chosen-zero composite with its exact whiskering uses concrete functor data.
/-- The full second left face is the literal postcomposition of the original binary track. -/
theorem leftSecond_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n
        (StdSimplex.map (triangleFace 2 3 7 (by decide) (by decide)).toOrderHom
          (TheoremB.compositionTriangleHomotopy (r, s)), x) =
      ((boundedAboveFlatPerfectNormalizedCompTrackComparison g h).postcomp (K f)).level n
        (r, (s, x)) := by
  let J : asSmallCategory (W Y) ⟶ asSmallCategory (W X) :=
    asSmallCategoryMap (W Y) (W X) (NE f) (NZ f)
  rw [prespectrumSimplexFamily_face, left_second_face, prespectrumSimplexFamily_triangle]
  have hp := prespectrumTransformationCompositionHomotopy_postcomp_level
    (F := BoundedFlatPerfectBinarySimplex.sourceMap g h)
    (G := BoundedFlatPerfectBinarySimplex.intermediateMap g h)
    (H := BoundedFlatPerfectBinarySimplex.targetMap g h)
    (BoundedFlatPerfectBinarySimplex.first g h).hom
    (BoundedFlatPerfectBinarySimplex.second g h).hom
    (fun _ ↦ (W Y).asSmall.weq_iso _ inferInstance)
    (fun _ ↦ (W Y).asSmall.weq_iso _ inferInstance) J n r s x
  have hNative := congrArg ((K f).map n)
    (BoundedFlatPerfectBinarySimplex.native_apply g h n r s x).symm
  refine Eq.trans ?_ hNative
  exact hp

/-- The full second right face is the literal precomposition of the original binary track. -/
theorem rightSecond_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n
        (StdSimplex.map (triangleFace 5 6 7 (by decide) (by decide)).toOrderHom
          (TheoremB.compositionTriangleHomotopy (r, s)), x) =
      (Homotopy.RelHomotopy.precomp (K h)
        (boundedAboveFlatPerfectNormalizedCompTrackComparison f g)).level n (r, (s, x)) := by
  let J : asSmallCategory (W T) ⟶ asSmallCategory (W Z) :=
    asSmallCategoryMap (W T) (W Z) (NE h) (NZ h)
  let S : ModelSimplex (asSmallCategory (W T)) (asSmallCategory (W X)) 2 :=
    (simplex f g h).face (triangleFace 5 6 7 (by decide) (by decide))
  let z : StdSimplex ℝ (Fin 3) := TheoremB.compositionTriangleHomotopy (r, s)
  have hf : prespectrumSimplexFamily (simplex f g h) n
      (StdSimplex.map (triangleFace 5 6 7 (by decide) (by decide)).toOrderHom z, x) =
      prespectrumSimplexFamily S n (z, x) := by
    rw [prespectrumSimplexFamily_face]
  have ht : prespectrumSimplexFamily S n (z, x) =
      (prespectrumTransformationCompositionHomotopy
        (F := right f g h) (G := rightSecondMap f g h) (H := target f g h)
        (rightSecondGeometric f g h).hom (rightSecondNormalization f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)).level n (r, (s, x)) := by
    dsimp only [S, z]
    rw [right_second_face, prespectrumSimplexFamily_triangle]
  have hp := prespectrumTransformationCompositionHomotopy_precomp_level
    (F := BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (G := BoundedFlatPerfectBinarySimplex.intermediateMap f g)
    (H := BoundedFlatPerfectBinarySimplex.targetMap f g)
    (BoundedFlatPerfectBinarySimplex.first f g).hom
    (BoundedFlatPerfectBinarySimplex.second f g).hom
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
    (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance) J n r s x
  exact hf.trans (ht.trans (hp.trans (BoundedFlatPerfectBinarySimplex.native_apply f g n r s
    ((K h).map n x)).symm))

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex
