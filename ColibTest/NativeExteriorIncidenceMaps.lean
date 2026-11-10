/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceMaps

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow

universe u
variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

example : (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
    correspondenceIncidenceMap (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
      (nativeExteriorPoint Y Z T w hw) = exteriorIncidenceProductMap X Y Z T z w :=
  nativeExteriorIncidenceIso_hom_map X Y Z T z w hz hw

example : IsFinite (exteriorIncidenceProductMap X Y Z T z w) :=
  exteriorIncidenceProductMap_isFinite X Y Z T z w hz hw

example : (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
    correspondenceIncidenceInclusion (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw) =
    exteriorIncidenceProductInclusion X Y Z T z w :=
  nativeExteriorIncidenceIso_hom_inclusion X Y Z T z w hz hw

example : IsClosedImmersion (exteriorIncidenceProductInclusion X Y Z T z w) :=
  exteriorIncidenceProductInclusion_isClosedImmersion X Y Z T z w hz hw

-- A direct coordinate consumer: the finite map carries precisely the original source coordinate.
example : (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫
    correspondenceIncidenceMap (SmoothSite.product X T).hom (SmoothSite.product Y T).hom
      (SmoothSite.product Z T).hom (nativeExteriorPoint X Y T z hz)
      (nativeExteriorPoint Y Z T w hw) ≫
    pullback.fst (SmoothSite.product X T).hom (SmoothSite.product Z T).hom ≫
    pullback.fst X.hom T.hom =
    pullback.fst _ _ ≫ correspondenceIncidenceLeft X.hom Y.hom Z.hom z w := by
  exact (congrArg (fun f => (nativeExteriorIncidenceIso X Y Z T z w hz hw).hom ≫ f)
    (correspondenceIncidenceMap_fst_assoc (SmoothSite.product X T).hom
      (SmoothSite.product Y T).hom (SmoothSite.product Z T).hom
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
      (pullback.fst X.hom T.hom))).trans
    ((nativeExteriorIncidenceIso_hom_source_assoc X Y Z T z w hz hw
      (pullback.fst X.hom T.hom)).trans (exteriorIncidenceProductSource_fst X Y Z T z w))
