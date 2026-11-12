/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRegularGeneric
import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRegularPullback

/-! The original positive meromorphic power has the literal ordinary-power generic germ. -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.SheafOfModules (schemeTensorPower)

universe u

noncomputable section

attribute [local instance] AlgebraicGeometry.positiveRegularGenericInvertible
  AlgebraicGeometry.positiveRegularGenericPowerInvertible
  AlgebraicGeometry.positiveRegularGenericPowerQuasicoherent
  AlgebraicGeometry.positiveRegularGenericQuasicoherent
  AlgebraicGeometry.positiveRegularGenericTensorEquivalence

variable (X : Scheme.{u}) [IsIntegral X] (L P : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
  [P.IsQuasicoherent]

example (s : MeromorphicSection X.sheaf L) (hs : IsRegularMeromorphicSection X.sheaf L s)
    (U : X.Opens) (hU : genericPoint X ∈ U) (m : Γ(L, U))
    (hm : meromorphicGenericValue X L s = L.presheaf.germ U (genericPoint X) hU m)
    (k : ℕ) (α : schemeTensorPower X L hL (k + 1) ≅ P) :
    meromorphicGenericValue X P
      (mapMeromorphicSection (show X.Modules from schemeTensorPower X L hL (k + 1)) P
        α.hom (positiveTensorPowerMeromorphicSection X L s hs k).val) =
      P.presheaf.germ U (genericPoint X) hU
        (Hom.app α.hom U (natTensorPowerRegularSection X L U m (k + 1))) :=
  meromorphicGenericValue_rootImage_eq_germ_natTensorPowerRegularSection
    X L P s hs U hU m hm k α

#print axioms AlgebraicGeometry.meromorphicGenericValue_positiveTensorPower_eq_germ_natTensorPowerRegularSection
#print axioms AlgebraicGeometry.meromorphicGenericValue_rootImage_eq_germ_natTensorPowerRegularSection
