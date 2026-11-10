/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidenceGenerics

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow

noncomputable section
universe u

variable {k : Type u} [Field k] (X Y Z T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)
  (η : genericPoints (correspondenceIncidence X.hom Y.hom Z.hom z w))

example : exteriorIncidenceProductProjection X Y Z T z w
    (exteriorIncidenceProductGenericsEquiv X Y Z T z w η).val = η.val :=
  exteriorIncidenceProductGenericsEquiv_projection X Y Z T z w η

example : nativeExteriorIncidenceOriginal X Y Z T z w hz hw
    (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val = η.val :=
  nativeExteriorIncidenceGenericsEquiv_original X Y Z T z w hz hw η

example : (nativeExteriorIncidenceIso X Y Z T z w hz hw).inv
    (nativeExteriorIncidenceGenericsEquiv X Y Z T z w hz hw η).val =
      (exteriorIncidenceProductGenericsEquiv X Y Z T z w η).val :=
  nativeExteriorIncidenceIso_inv_generics X Y Z T z w hz hw η
