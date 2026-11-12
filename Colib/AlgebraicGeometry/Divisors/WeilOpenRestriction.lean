/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.WeilFundamental
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.Length.RingEquiv

/-!
# Restricting the original Cartier multiplicities to an open subscheme

The original stalk quotient is transported by the open immersion's actual local-ring
isomorphism. Consequently native Weil restriction agrees with the whole scheme-theoretic
inverse image of a Cartier divisor, retaining all lengths and nilpotents. The ambient Weil
construction still requires integral Noetherian schemes; no such claim is made for arbitrary
nonreduced ambient schemes.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.OpenWeilRestriction

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The local quotient lengths of the original whole ideal are unchanged by open restriction. -/
theorem effectiveCartierMultiplicity_comap (I : X.IdealSheafData) (Z : PrimeDivisor U) :
    effectiveCartierMultiplicity (I.comap j) Z =
      effectiveCartierMultiplicity I (primeDivisorMap j Z) := by
  unfold effectiveCartierMultiplicity
  rw [genericPoint_primeDivisorMap, IdealSheafData.stalk_comap]
  let e := (asIso (j.stalkMap Z.genericPoint)).commRingCatIsoToRingEquiv
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
    (Module.quotient_length_eq_of_ringEquiv e
      (IdealSheafData.stalk I (j.base Z.genericPoint))).symm

/-- Native signed Weil restriction of a Cartier divisor is the divisor of its literal
scheme-theoretic inverse image, with unchanged whole quotient lengths. -/
@[colib_tag "COL-1072", stacks 02AR "Open restriction preserves whole Cartier stalk lengths",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/WeilDivisorClass/OpenRestriction.lean:103-118"
    "ingredient" "Native restriction of the original Weil coefficient family"]
theorem restrictWeil_effectiveCartierWeilDivisor
    [IsNoetherian X] [IsIntegral X] [IsNoetherian U] [IsIntegral U]
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    restrictWeil j (effectiveCartierWeilDivisor I hI) =
      effectiveCartierWeilDivisor (I.comap j)
        (Stacks.Divisors.isPullbackDefined_of_flat j I hI) := by
  refine Subtype.ext (funext fun Z => ?_)
  rw [restrictWeil_apply, effectiveCartierWeilDivisor_apply,
    effectiveCartierWeilDivisor_apply, effectiveCartierMultiplicity_comap]

end AlgebraicGeometry.OpenWeilRestriction
