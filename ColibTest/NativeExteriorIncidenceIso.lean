/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceIso

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow

noncomputable section

universe u
variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

-- The result targets the original native incidence expression directly.
example : pullback (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) T.hom ≅
    correspondenceIncidence (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
      (nativeExteriorPoint Y Z T w hw) :=
  nativeExteriorIncidenceIso X Y Z T z w hz hw

example : IsPullback (nativeExteriorIncidenceOriginal X Y Z T z w hz hw)
    (nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.snd _ _)
    (correspondenceIncidenceLeft X.hom Y.hom Z.hom z w ≫ X.hom) T.hom :=
  nativeExteriorIncidenceOriginal_isPullback X Y Z T z w hz hw

example : Smooth (nativeExteriorIncidenceOriginal X Y Z T z w hz hw) := inferInstance
