/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidencePushPull

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

example : IsFinite (exteriorIncidenceProductOuter X Z T Y z w) :=
  exteriorIncidenceProductOuter_isFinite X Z T Y z w hz hw

example : IsClosedImmersion (exteriorOuterDiagonal X Z T) := inferInstance

example (p : exteriorIncidenceProduct X Y Z T z w) :
    (correspondenceIncidenceMap (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)).residueDegree
        ((nativeExteriorIncidenceIso X Y Z T z w hz hw).hom p) =
      (exteriorIncidenceProductOuter X Z T Y z w).residueDegree p :=
  nativeExteriorIncidenceMap_residueDegree X Y Z T z w hz hw p

example (c d : AlgebraicCycle (exteriorOuterProduct X Z T) ℤ)
    (h : finiteCyclePushforward (exteriorOuterDiagonal X Z T) c =
      finiteCyclePushforward (exteriorOuterDiagonal X Z T) d) : c = d :=
  finiteCyclePushforward_injective_of_isClosedImmersion (exteriorOuterDiagonal X Z T) h

#check exteriorIncidenceProductOuter_isPullback
#check exteriorIncidence_fixedLabel_pushPull
#check nativeExteriorIncidence_pushforward_flatPullback
