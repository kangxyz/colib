/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageGeometry

/-! Consumers of the actual Z-first intersection. No correspondence is transposed. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example : IsPullback (correspondenceSixfoldFirstFactorProjection f g h i)
    (correspondenceSixfoldRightPairProjection f g h i)
    (pullback.snd f g ≫ g) (correspondenceAmbientSource g h i ≫ g) :=
  correspondenceSixfold_right_isPullback f g h i

example : IsPullback (correspondenceSecondAmbientFirstFactorProjection f g h i)
    (correspondenceSecondAmbientRightPairProjection f g h i)
    (pullback.snd f g ≫ g) (correspondenceTripleSource g h i ≫ g) :=
  correspondenceSecondAmbient_right_isPullback f g h i

example : IsPullback (correspondenceTripleSupportFirstProjection f g h i z w v)
    (correspondenceTripleSupportRightProjection f g h i z w v)
    (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
    (correspondenceSupportProductSource g h i w v ≫ g) :=
  correspondenceTripleSupport_right_isPullback f g h i z w v

example : IsPullback (correspondenceRightIntermediateSupportInclusion f g h i z w v)
    (correspondenceRightIntermediateToTripleSupport f g h i z w v)
    (correspondenceSecondAmbientInclusion f g h i)
    (correspondenceTripleSupportProductInclusion f g h i z w v) :=
  correspondenceRightIntermediate_ambient_isPullback f g h i z w v

example [IsSeparated h] :
    (correspondenceRightIntermediateAmbientInclusion f g h i z w v).ker =
      (correspondenceSecondAmbientInclusion f g h i).ker ⊔
        (correspondenceTripleSupportProductInclusion f g h i z w v).ker :=
  correspondenceRightIntermediateAmbientInclusion_ker f g h i z w v

example : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v ≫
      correspondenceRightIntermediateToTripleSupport f g h i z w v =
    correspondenceTripleIncidenceToTripleSupport f g h i z w v :=
  correspondenceTripleIncidenceToRightSupportProduct_support f g h i z w v

example : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v ≫
      correspondenceRightIntermediateAmbientInclusion f g h i z w v =
    correspondenceTripleIncidenceSixfoldInclusion f g h i z w v :=
  correspondenceTripleIncidenceToRightSupportProduct_ambient f g h i z w v

example : IsClosedImmersion (correspondenceRightIntermediateSupportInclusion f g h i z w v) :=
  inferInstance
