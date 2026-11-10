/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Correspondences.Exterior.Generics

/-!
# In-package checks for native exterior Generics
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
noncomputable section
variable {S : Scheme.{u}} (X T : SmoothSite S) [GeometricallyIntegral T.hom]

example : genericPoints X.left ≃ genericPoints (SmoothSite.product X T).left :=
  exteriorSourceGenericsEquiv X T
example (t : genericPoints X.left) :
    (pullback.fst X.hom T.hom) (exteriorSourceGenericsEquiv X T t).val = t.val :=
  exteriorSourceGenericsEquiv_fst X T t
example (t : genericPoints X.left) :
    closure ({(exteriorSourceGenericsEquiv X T t).val} :
      Set (SmoothSite.product X T).left) =
      (pullback.fst X.hom T.hom) ⁻¹' closure ({t.val} : Set X.left) :=
  exteriorSourceGenericsEquiv_closure X T t
