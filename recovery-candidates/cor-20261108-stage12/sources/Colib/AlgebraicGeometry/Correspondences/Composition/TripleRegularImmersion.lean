/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleStalkModules
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Composition

/-!+# Regularity of the actual successive middle diagonals

The first middle diagonal is a flat pullback of the smooth Y diagonal. The second is a flat
pullback of the smooth Z diagonal on the actual first-diagonal scheme, not on a replacement
coefficient module. Native stability of regular immersions under composition proves regularity
of the genuine combined fourfold inclusion. In particular, two separately regular ambient
lists are not being mistaken for a jointly regular concatenation.

The actual morphisms and squares come from `TripleDiagonal`. The proof uses native Stacks
067R (smooth sections), 067P (flat base change), and 067Q (composition). The geometric order
agrees with motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/Aglib/AlgebraicGeometry/Intersection/Triple/CombinedRegularity.lean,
Git blob 621566dc66d48431f958a13640d8a637c1ef45a5. Unlike that implementation, this file
uses native regular immersions rather than adding a regular-sequence composition theorem.
There are no assumptions on the support coefficients, no field restriction, and no reduction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

instance flat_correspondenceMiddlePair [Flat f] [Flat h] :
    Flat (correspondenceMiddlePair f g h) := by
  unfold correspondenceMiddlePair
  exact MorphismProperty.pullbackMap (P := @Flat)
    (inferInstanceAs (Flat (pullback.snd f g)))
    (inferInstanceAs (Flat (pullback.fst g h))) rfl rfl

instance flat_correspondenceSixfoldFirstMiddlePair [Flat f] [Flat h] [Flat i] :
    Flat (correspondenceSixfoldFirstMiddlePair f g h i) := by
  dsimp only [correspondenceSixfoldFirstMiddlePair]
  infer_instance

instance flat_correspondenceTripleTarget [Flat f] [Flat g] :
    Flat (correspondenceTripleTarget f g h) := by
  dsimp only [correspondenceTripleTarget]
  infer_instance

/-- The remaining original middle pair on the genuine first-diagonal scheme. -/
def correspondenceFirstDiagonalSecondMiddlePair :
    correspondenceFirstDiagonal f g h i ⟶ pullback h h :=
  pullback.map _ _ h h (correspondenceTripleTarget f g h) (pullback.fst h i) (𝟙 S)
    (by simp) (by simp)

instance flat_correspondenceFirstDiagonalSecondMiddlePair [Flat f] [Flat g] [Flat i] :
    Flat (correspondenceFirstDiagonalSecondMiddlePair f g h i) := by
  unfold correspondenceFirstDiagonalSecondMiddlePair
  exact MorphismProperty.pullbackMap (P := @Flat)
    (inferInstanceAs (Flat (correspondenceTripleTarget f g h)))
    (inferInstanceAs (Flat (pullback.fst h i))) rfl rfl

/-- Restriction keeps the literal second pair from the original sixfold ambient. -/
@[reassoc]
theorem correspondenceFirstDiagonal_secondMiddlePair :
    correspondenceFirstDiagonalInclusion f g h i ≫
      correspondenceSixfoldSecondMiddlePair f g h i =
        correspondenceFirstDiagonalSecondMiddlePair f g h i := by
  apply pullback.hom_ext <;>
    simp [correspondenceSixfoldSecondMiddlePair, correspondenceFirstDiagonalSecondMiddlePair,
      pullback.map, correspondenceTripleTarget, correspondenceAmbientTarget]

/-- The second diagonal is Cartesian over the smooth Z diagonal after the first cut. -/
theorem correspondenceSecondDiagonal_isPullback :
    IsPullback
      (pullback.fst (correspondenceTripleTarget f g h) (pullback.fst h i) ≫
        correspondenceTripleTarget f g h)
      (correspondenceSecondDiagonalInclusion f g h i)
      (pullback.diagonal h) (correspondenceFirstDiagonalSecondMiddlePair f g h i) :=
  pullback_map_diagonal_isPullback (correspondenceTripleTarget f g h) (pullback.fst h i) h

/-- The first actual middle inclusion is regular by flat base change of the Y diagonal. -/
theorem isRegularImmersion_correspondenceFirstDiagonal [Flat f] [Smooth g] [IsSeparated g]
    [Flat h] [Flat i] :
    IsRegularImmersion (correspondenceFirstDiagonalInclusion f g h i) :=
  Stacks.AlgebraicGeometry.isRegularImmersion_of_isPullback_of_flat
    (correspondenceSixfoldFirstDiagonal_isPullback f g h i).flip
    (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
      (pullback.fst g g) (pullback.diagonal g) (pullback.diagonal_fst g))

/-- The second actual inclusion is regular on the full first-diagonal scheme. -/
theorem isRegularImmersion_correspondenceSecondDiagonal [Flat f] [Flat g] [Smooth h]
    [IsSeparated h] [Flat i] :
    IsRegularImmersion (correspondenceSecondDiagonalInclusion f g h i) :=
  Stacks.AlgebraicGeometry.isRegularImmersion_of_isPullback_of_flat
    (correspondenceSecondDiagonal_isPullback f g h i).flip
    (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
      (pullback.fst h h) (pullback.diagonal h) (pullback.diagonal_fst h))

/-- The actual combined diagonal is regular by genuine successive regular immersions. -/
theorem isRegularImmersion_correspondenceFourfoldDiagonal [Flat f] [Smooth g] [IsSeparated g]
    [Smooth h] [IsSeparated h] [Flat i] :
    IsRegularImmersion (correspondenceFourfoldDiagonalInclusion f g h i) :=
  Stacks.AlgebraicGeometry.isRegularImmersion_comp
    (correspondenceSecondDiagonalInclusion f g h i)
    (correspondenceFirstDiagonalInclusion f g h i)
    (isRegularImmersion_correspondenceSecondDiagonal f g h i)
    (isRegularImmersion_correspondenceFirstDiagonal f g h i)

end Stacks.Chow
