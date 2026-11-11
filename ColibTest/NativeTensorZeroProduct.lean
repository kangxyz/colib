/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.TensorZeroProduct
open CategoryTheory AlgebraicGeometry Stacks.Divisors
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
variable {X : Scheme.{u}} (M N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
example (a : Γ(M, ⊤)) (b : Γ(N, ⊤)) :
    zeroScheme X (tensorModules M N) (tensorSection M N ⊤ a b) =
      zeroScheme X M a * zeroScheme X N b :=
  zeroScheme_tensorSection_eq_mul M N a b
example (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (b : Γ(M, ⊤)) (d : Γ(N, ⊤)) :
    zeroScheme X (tensorModules (tensorModules (divisorSheaf D) M) N)
      (tensorSection (tensorModules (divisorSheaf D) M) N ⊤
        (tensorSection (divisorSheaf D) M ⊤ (divisorSheafGlobalSection D) b) d) =
          (D * zeroScheme X M b) * zeroScheme X N d :=
  zeroScheme_graph_tensor_poles M N D b d
#check zeroScheme_tensorSection_triple
#check tensorSection_whole_support_subset
#check finite_relativeCartier_tensorSection
