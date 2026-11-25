/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitUnitFaces

/-! The six original split-unit triangles evaluate to their actual native
normalization comparisons at every level. Adapted from `OriginalUnitSquareSimplex.lean`
at Quillen `c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Convexity Topology
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem rightFirstParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightFirstParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy
        (rightFirstGeometric f).hom (rightFirstNormalization f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (right_first_face f) n r t x

theorem rightSecondParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (rightSecondParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy
        (rightSecondGeometric f).hom (rightSecondNormalization f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (right_second_face f) n r t x

theorem normalizedRightParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (normalizedRightParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy (rightFirst f).hom (rightSecond f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (right_normalized_face f) n r t x

theorem leftFirstParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftFirstParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy
        (leftFirstGeometric f).hom (leftFirstNormalization f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (left_first_face f) n r t x

theorem leftSecondParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (leftSecondParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy
        (leftSecondGeometric f).hom (leftSecondNormalization f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (left_second_face f) n r t x

theorem normalizedLeftParameter_lift (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (W Y)).space n) :
    prespectrumSimplexFamily (simplex f) n (normalizedLeftParameter (r, t), x) =
      (prespectrumTransformationCompositionHomotopy (leftFirst f).hom (leftSecond f).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _
          inferInstance)).level n (r, (t, x)) :=
  triangle_lift _ _ _ _ _ _ (left_normalized_face f) n r t x

/-- Every common-simplex parameter fixes the actual original chosen point, including level zero. -/
theorem family_point (n : ℕ) (z : StdSimplex ℝ (Fin 8)) :
    prespectrumSimplexFamily (simplex f) n
      (z, (originalPrespectrum (W Y)).point n) =
      (originalPrespectrum (W X)).point n :=
  prespectrumSimplexFamily_point (simplex f) n z

/-- The entire common family retains a structure coordinate independent of its scalar parameters. -/
theorem family_structure (n : ℕ) (z : StdSimplex ℝ (Fin 8))
    (x : (originalPrespectrum (W Y)).space n) (t : unitInterval) :
    prespectrumSimplexFamily (simplex f) (n + 1)
      (z, (originalPrespectrum (W Y)).structureMap n x t) =
      (originalPrespectrum (W X)).structureMap n
        (prespectrumSimplexFamily (simplex f) n (z, x)) t :=
  prespectrumSimplexFamily_structure (simplex f) n z x t

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectOriginalUnitSquareSimplex
