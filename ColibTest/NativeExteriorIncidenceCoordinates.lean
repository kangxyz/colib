/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceCoordinates

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow

universe u
variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

example : nativeExteriorIncidenceOriginal X Y Z T z w hz hw ≫ pullback.fst _ _ =
    nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫ pullback.fst _ _ :=
  nativeExteriorIncidenceOriginal_fst X Y Z T z w hz hw

-- The two parameter coordinates agree as scheme morphisms, not only on points.
example : nativeExteriorIncidenceFirst X Y Z T z w hz hw ≫
      pullback.snd (exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom)
        T.hom =
    nativeExteriorIncidenceSecond X Y Z T z w hz hw ≫
      pullback.snd (exteriorSupportSourceProjection Y Z (integralComponentAt w) ≫ Y.hom)
        T.hom :=
  nativeExteriorIncidence_parameter X Y Z T z w hz hw
