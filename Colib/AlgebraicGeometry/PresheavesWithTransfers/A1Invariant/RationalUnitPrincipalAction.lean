/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.DenseOpenBoundaryFactor

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.PrincipalAction
public import Colib.AlgebraicGeometry.Correspondences.Divisors.FiniteFlat

/-! # The original boundary-normalized rational unit acts trivially -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow TopologicalSpace
open Scheme AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u v

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- The original dense-open representative gives exactly the original function-field element. -/
theorem curveRationalFunction_denseOpen {C : Scheme.{u}} [IsIntegral C]
    (W : DenseOpen C) [Nonempty W.val] (s : Γ(C, W.val)) :
    curveRationalFunction W.val.ι (W.val.topIso.inv s) =
      (rationalFunctionsEquivFunctionField C).val (ofSection C W s) := by
  rw [(rationalFunctionsEquivFunctionField C).property W s
    (((genericPoint_spec C).mem_open_set_iff W.val.isOpen).mpr (by simpa using ‹Nonempty W.val›))]
  simp only [curveRationalFunction, Opens.ι_appIso, Iso.refl_inv,
    Opens.topIso_inv]
  exact ConcreteCategory.congr_hom (C.presheaf.germ_res _ _ _) s

/-- The exact original rational unit restricts to the same principal cycle used
by the polynomial family, with the original outer map unchanged. -/
theorem pushforward_principalDivisor_denseUnit {C V Z : Scheme.{u}}
    [IsIntegral C] [IsIntegral V] [IsNoetherian V]
    (j : V ⟶ C) [IsOpenImmersion j] [IsDominant j] (r : V ⟶ Z)
    (W : DenseOpen C) [Nonempty W.val] (u : Γ(C, W.val)ˣ)
    (F : (rationalFunctions C)ˣ)
    (hF : Units.map (ofSectionRingHom C W).toMonoidHom u = F) :
    AlgebraicGeometry.WeilDivisor.pushforwardCycle r
        (AlgebraicGeometry.principalDivisor V (rationalFunctionsUnitsMulEquivOfOpenImmersion j F)) =
      noetherianCyclePushforward r (principalCycle V
        (j.functionFieldMap (curveRationalFunction W.val.ι (W.val.topIso.inv u.val)))) := by
  change noetherianCyclePushforward r
    (AlgebraicGeometry.WeilDivisor.toAlgebraicCycle _) = _
  rw [AlgebraicGeometry.WeilDivisor.toAlgebraicCycle_principalDivisor,
    rationalFunctionsUnitsMulEquivOfOpenImmersion_coe,
    rationalFunctionsEquivFunctionField_rationalFunctionsRingEquivOfOpenImmersion,
    functionFieldEquiv_openImmersion_eq_schemeFunctionFieldMap,
    curveRationalFunction_denseOpen]
  have hh := congrArg Units.val hF
  change (ofSectionRingHom C W) u.val = F.val at hh
  rw [ofSectionRingHom_apply] at hh
  rw [hh]

end AlgebraicGeometry.PrincipalFamilyUnitOpen
