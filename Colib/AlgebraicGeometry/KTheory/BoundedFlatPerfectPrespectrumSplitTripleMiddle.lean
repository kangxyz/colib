/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumAssociativity
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleParameters
public import Colib.KTheory.Waldhausen.Iterated.NormalizationPasting

/-!
# The two normalized middle faces of a split pullback triple

The common simplex realizes the actual normalized composition homotopy by traversing
its middle left face in reverse and its middle right face forwards. Both time parameters
are independent, including at level zero.

Adapted from Quillen `SplitTripleParameters.lean`, `NormalizedPullbackCoherence.lean` and
`NormalizedMiddleNative.lean` at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex

open SimplexParameters BoundedFlatPerfectSplitTripleParameters

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "N" => boundedAboveFlatPerfectNormalizedPullback
local notation "NE" => boundedAboveFlatPerfectNormalizedPullback_exact
local notation "NZ" => boundedAboveFlatPerfectNormalizedPullback_obj_zero
local notation "NC" => boundedAboveFlatPerfectNormalizedPullbackCompIso

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The actual normalized left branch retains the functor associator. -/
def normalizedMiddleLeftIso :
    N (g ≫ h) ⋙ N f ≅ N h ⋙ N g ⋙ N f :=
  isoWhiskerRight (NC g h) (N f) ≪≫ Functor.associator (N h) (N g) (N f)

/-- The actual normalized right branch retains the scheme associativity transport. -/
def normalizedMiddleRightIso :
    N (f ≫ g ≫ h) ≅ N h ⋙ N (f ≫ g) :=
  eqToIso (congrArg N (Category.assoc f g h).symm) ≪≫ NC (f ≫ g) h

/-- Both original normalized routes compare by the native relative prespectrum pasting. -/
abbrev normalizedMiddlePasting :=
  boundedAboveFlatPerfectNormalizedTriplePasting f g h

/-- The actual normalized left face at every level and both independent time coordinates. -/
theorem normalizedLeftParameter_lift (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (normalizedLeftParameter (r, s), x) =
      (prespectrumTransformationCompositionHomotopy
        (BoundedFlatPerfectTripleSimplex.leftFirst f g h).hom
        (BoundedFlatPerfectTripleSimplex.leftSecond f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)).level n (r, (s, x)) :=
  triangle_lift _ _ _ _ _ _ (normalized_left_face f g h) n r s x

/-- The actual normalized right face at every level and both independent time coordinates. -/
theorem normalizedRightParameter_lift (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (normalizedRightParameter (r, s), x) =
      (prespectrumTransformationCompositionHomotopy
        (BoundedFlatPerfectTripleSimplex.rightFirst f g h).hom
        (BoundedFlatPerfectTripleSimplex.rightSecond f g h).hom
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)
        (fun _ ↦ (W X).asSmall.weq_iso _ inferInstance)).level n (r, (s, x)) :=
  triangle_lift _ _ _ _ _ _ (normalized_right_face f g h) n r s x

/-- The actual normalized comparison retains the reversed left face, then the right face. -/
theorem normalized_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (W T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n
      ((normalizedLeftParameter.symm.trans normalizedRightParameter) (r, s), x) =
      (normalizedMiddlePasting f g h).level n (r, (s, x)) := by
  unfold normalizedMiddlePasting boundedAboveFlatPerfectNormalizedTriplePasting
  rw [originalPrespectrumPastingHomotopy_whole_level, Path.Homotopy.trans_apply]
  split
  · exact normalizedLeftParameter_lift f g h n _ s x
  · exact normalizedRightParameter_lift f g h n _ s x

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/NormalizedMiddleNative.lean:22-38"
  "adaptation" "The actual normalized left reversal and right traversal at every level."]
  normalized_native

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectSplitTripleSimplex
