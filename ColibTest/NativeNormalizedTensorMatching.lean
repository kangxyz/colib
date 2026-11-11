/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.NormalizedTensorMatching
open CategoryTheory AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
example {X : Scheme.{u}} (F T : X.Modules)
    (e : F ≅ SheafOfModules.unit X.ringCatSheaf) (s : Γ(F, ⊤)) (b : Γ(T, ⊤)) :
    (frameTensorContraction F T e).hom.app ⊤ (tensorSection F T ⊤ s b) = e.hom.app ⊤ s • b :=
  frameTensorContraction_tensorSection F T e s b
#check tensorSection_matching_of_normalizations
#check nestedPullbackTensorIso_product
#check boundary_tensorSection_matching
