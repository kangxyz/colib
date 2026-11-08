/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.TripleAmbient

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

noncomputable section

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

-- Neither finite correspondence nor a field hypothesis is required by the geometry.
example : IsPullback (correspondenceIncidenceInclusion f g h z w)
    (correspondenceIncidenceToSupportProduct f g h z w)
    (correspondenceTripleInclusion f g h) (correspondenceSupportProductInclusion f g h z w) :=
  isPullback_correspondenceAmbientIncidence f g h z w

example : IsPullback (correspondenceSecondDiagonalInclusion f g h i)
    (correspondenceFourfoldToSecondAmbient f g h i)
    (correspondenceFirstDiagonalInclusion f g h i)
    (correspondenceSecondAmbientInclusion f g h i) :=
  correspondenceFourfold_diagonals_isPullback f g h i

example : IsPullback (correspondenceTripleIncidenceFourfoldInclusion f g h i z w v)
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v ≫
      correspondenceLeftIntermediateToTripleSupport f g h i z w v)
    (correspondenceSecondDiagonalInclusion f g h i ≫
      correspondenceFirstDiagonalInclusion f g h i)
    (correspondenceTripleSupportProductInclusion f g h i z w v) :=
  correspondenceTripleIncidence_sixfold_isPullback f g h i z w v

example : correspondenceTripleIncidenceFourfoldInclusion f g h i z w v ≫
    pullback.snd (correspondenceTripleTarget f g h) (pullback.fst h i) =
      correspondenceTripleIncidenceSnd f g h i z w v ≫ (integralComponentAt v).subschemeι :=
  correspondenceTripleIncidenceFourfoldInclusion_snd f g h i z w v

example : IsClosedImmersion (correspondenceTripleSupportProductInclusion f g h i z w v) :=
  inferInstance

example [IsSeparated g] [IsSeparated h] :
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v).ker =
      (correspondenceFirstDiagonalInclusion f g h i).ker ⊔
        ((correspondenceSecondAmbientInclusion f g h i).ker ⊔
          (correspondenceTripleSupportProductInclusion f g h i z w v).ker) :=
  correspondenceTripleIncidenceSixfoldInclusion_ker_eq_threeIdeals f g h i z w v

example [IsSeparated g] [IsSeparated h] :
    correspondenceTripleIncidence f g h i z w v ≅
      ((correspondenceFirstDiagonalInclusion f g h i).ker ⊔
        ((correspondenceSecondAmbientInclusion f g h i).ker ⊔
          (correspondenceTripleSupportProductInclusion f g h i z w v).ker)).subscheme :=
  correspondenceTripleIncidenceThreeIdealIso f g h i z w v

example [IsSeparated g] :
    (correspondenceFirstDiagonalInclusion f g h i).ker =
      (pullback.diagonal g).ker.comap (correspondenceSixfoldFirstMiddlePair f g h i) :=
  ker_correspondenceFirstDiagonal f g h i

example [IsSeparated h] :
    (correspondenceSecondAmbientInclusion f g h i).ker =
      (pullback.diagonal h).ker.comap (correspondenceSixfoldSecondMiddlePair f g h i) :=
  ker_correspondenceSecondDiagonal f g h i
