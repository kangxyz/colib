/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleSimplex
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumUnitTracks

/-!
# Full evaluation on the first binary faces of a split pullback triple

The two original scalar parameters are used without reparameterization. The left
first face gives the actual normalized binary comparison. The right first face gives
the native small-model triangle with the original scheme associativity transport.

Adapted from `BoundedFlat/NativeBinaryComparison.lean:28-46` and
`BoundedFlat/SplitTripleNative.lean:29-36` in Quillen at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "PE" => boundedAboveFlatPerfectPullback_isExact

namespace BoundedFlatPerfectBinarySimplex

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The actual original binary comparison evaluates to the literal small-model triangle. -/
theorem native_apply (n : ℕ) (r s : unitInterval) (x : (originalPrespectrum (W Z)).space n) :
    (boundedAboveFlatPerfectNormalizedCompTrackComparison f g).level n (r, (s, x)) =
      (prespectrumTransformationCompositionHomotopy (F := sourceMap f g)
        (G := intermediateMap f g) (H := targetMap f g) (first f g).hom (second f g).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)).level n (r, (s, x)) := by
  change (exactNormalizationCompTrackComparison (PE (f ≫ g)) (PE g) (PE f)
    (boundedAboveFlatPerfectPullbackCompIso f g)).level n (r, (s, x)) = _
  have he := DFunLike.congr_fun
    (exactNormalizationCompTrackComparison_level (PE (f ≫ g)) (PE g) (PE f)
      (boundedAboveFlatPerfectPullbackCompIso f g) n) (r, (s, x))
  exact he

end BoundedFlatPerfectBinarySimplex

namespace BoundedFlatPerfectSplitTripleSimplex

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The full first left face agrees with the original native binary comparison at every level. -/
theorem leftFirst_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n
        (StdSimplex.map (triangleFace 0 1 2 (by decide) (by decide)).toOrderHom
          (TheoremB.compositionTriangleHomotopy (r, s)), x) =
      (boundedAboveFlatPerfectNormalizedCompTrackComparison f (g ≫ h)).level n
        (r, (s, x)) := by
  rw [prespectrumSimplexFamily_face, left_first_face, prespectrumSimplexFamily_triangle]
  exact (BoundedFlatPerfectBinarySimplex.native_apply f (g ≫ h) n r s x).symm

/-- The full first right face retains the chosen source-association transport in its triangle. -/
theorem rightFirst_scalar (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n
        (StdSimplex.map (triangleFace 0 4 5 (by decide) (by decide)).toOrderHom
          (TheoremB.compositionTriangleHomotopy (r, s)), x) =
      (prespectrumTransformationCompositionHomotopy
        (F := BoundedFlatPerfectTripleSimplex.source f g h)
        (G := rightFirstMap f g h) (H := BoundedFlatPerfectTripleSimplex.right f g h)
        (rightFirstGeometric f g h).hom (rightFirstNormalization f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)).level n (r, (s, x)) := by
  rw [prespectrumSimplexFamily_face, right_first_face]
  exact prespectrumSimplexFamily_triangle _ _ _ _ n r s x

end BoundedFlatPerfectSplitTripleSimplex

end AlgebraicGeometry.Scheme.Modules
