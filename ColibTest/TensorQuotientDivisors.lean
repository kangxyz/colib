/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Divisors.Meromorphic.TensorPowerRatio

/-!
# Tests of actual tensor quotients and their signed principal correction

The exponent-one and composite-exponent tests use native tensor powers and the literal
correcting rational unit. They do not assume a target Weil-divisor identity or a boundary
normalization. The ambient scheme is explicitly integral and locally Noetherian.
-/

open CategoryTheory AlgebraicGeometry
open Stacks.SheafOfModules (schemeTensorPower)

universe u

attribute [local instance] AlgebraicGeometry.isQuasicoherentOfIsInvertible
  AlgebraicGeometry.isInvertibleTensorObj

noncomputable section

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
  (L N P : X.Modules)
  [hL : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf L]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property P]

local instance : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
  hL.toAlgebraicGeometry

variable (a : MeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N))
  (b : MeromorphicSection X.sheaf N)
  (ha : IsRegularMeromorphicSection X.sheaf (Scheme.Modules.tensorObj L N) a)
  (hb : IsRegularMeromorphicSection X.sheaf N b)
  (c : MeromorphicSection X.sheaf P) (hc : IsRegularMeromorphicSection X.sheaf P c)

/-- The quotient really multiplies by the original denominator to recover the numerator. -/
example : tensorMeromorphicSection X L N (quotientTensorMeromorphicSection X L N a b hb) b = a :=
  tensorMeromorphicSection_quotientTensorMeromorphicSection X L N a b hb

/-- The literal denominator divisor has a minus sign. -/
example : weilDivisorOfMeromorphicSection X L (quotientTensorMeromorphicSection X L N a b hb)
      (isRegularMeromorphicSection_quotientTensorMeromorphicSection X L N a b ha hb) =
    weilDivisorOfMeromorphicSection X (Scheme.Modules.tensorObj L N) a ha -
      weilDivisorOfMeromorphicSection X N b hb :=
  weilDivisorOfMeromorphicSection_quotientTensorMeromorphicSection X L N a b ha hb

/-- Exponent one retains the native first tensor power and the plus-principal orientation. -/
example (α : schemeTensorPower X L hL 1 ≅ P) :
    let m := quotientTensorMeromorphicSection X L N a b hb
    let hm := isRegularMeromorphicSection_quotientTensorMeromorphicSection X L N a b ha hb
    weilDivisorOfMeromorphicSection X P c hc =
      (weilDivisorOfMeromorphicSection X (Scheme.Modules.tensorObj L N) a ha -
        weilDivisorOfMeromorphicSection X N b hb) +
      principalDivisor X (tensorPowerCorrectionRatio X L P m hm 0 α c hc) := by
  simpa only [zero_add, one_smul] using
    weilDivisor_eq_smul_sub_add_principal_tensorQuotientPower X L P N a b ha hb 0 α c hc

/-- The same producer handles composite exponents without a primality assumption. -/
example (α : schemeTensorPower X L hL 6 ≅ P) :
    let m := quotientTensorMeromorphicSection X L N a b hb
    let hm := isRegularMeromorphicSection_quotientTensorMeromorphicSection X L N a b ha hb
    weilDivisorOfMeromorphicSection X P c hc =
      6 • (weilDivisorOfMeromorphicSection X (Scheme.Modules.tensorObj L N) a ha -
        weilDivisorOfMeromorphicSection X N b hb) +
      principalDivisor X (tensorPowerCorrectionRatio X L P m hm 5 α c hc) :=
  weilDivisor_eq_smul_sub_add_principal_tensorQuotientPower X L P N a b ha hb 5 α c hc

#print axioms AlgebraicGeometry.tensorMeromorphicSection_quotientTensorMeromorphicSection
#print axioms AlgebraicGeometry.isRegularMeromorphicSection_quotientTensorMeromorphicSection
#print axioms AlgebraicGeometry.weilDivisorOfMeromorphicSection_quotientTensorMeromorphicSection
#print axioms AlgebraicGeometry.positiveTensorPowerMeromorphicSection
#print axioms AlgebraicGeometry.weilDivisor_eq_smul_sub_add_principal_tensorQuotientPower
