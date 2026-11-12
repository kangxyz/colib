/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.NoetherianPushforward
public import Colib.AlgebraicGeometry.Chow.WeilFundamental

/-!
# Whole finite flat divisors as native finite correspondences

The map from the ambient curve to the source-target product is unchanged. Each actual closed
zero scheme is pushed through its original composite map. Finiteness and flatness of its whole
first projection prove admissibility; no flatness of reduced components is asserted. The Weil
comparison retains the original scheme lengths and all residue degrees, including collisions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.WeilDivisor

variable {C Z : Scheme.{u}} [IsNoetherian C]

/-- The same Weil coefficients pushed through the original ambient map, as native cycles. -/
def pushforwardCycle (r : C ⟶ Z) : WeilDivisor C →+ AlgebraicCycle Z ℤ :=
  (Stacks.Chow.noetherianCyclePushforward r).comp WeilDivisor.toAlgebraicCycle

end AlgebraicGeometry.WeilDivisor

namespace Stacks.Chow

variable {C X Y S : Scheme.{u}} [IsNoetherian C]
  (p : X ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
  (r : C ⟶ pullback p t)

local instance finiteFlatDivisorNoetherian (I : C.IdealSheafData) : IsNoetherian I.subscheme :=
  { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace I.subschemeι }

variable (I : C.IdealSheafData)
  [IsFinite ((I.subschemeι ≫ r) ≫ pullback.fst p t)]
  [Flat ((I.subschemeι ≫ r) ≫ pullback.fst p t)]

local instance divisorMapFinite : IsFinite (I.subschemeι ≫ r) :=
  IsFinite.of_comp _ (pullback.fst p t)

/-- The native correspondence of the whole finite flat closed zero scheme. -/
@[colib_tag "COL-1051"]
def finiteFlatDivisorCorrespondence : finiteCorrespondences p t :=
  finiteFlatSpanFundamental p t (I.subschemeι ≫ r)

/-- The correspondence is the genuine fundamental cycle of the whole scheme pushed by the
original source-target map. -/
@[simp] theorem finiteFlatDivisorCorrespondence_val :
    (finiteFlatDivisorCorrespondence p t r I).val =
      finiteCyclePushforward (I.subschemeι ≫ r)
        (AlgebraicCycle.fundamentalCycle I.subscheme) := rfl

/-- At every target point all original generic lengths and finite residue degrees contribute.
Distinct components with equal image are summed, rather than identified before weighting. -/
theorem finiteFlatDivisorCorrespondence_val_apply (z : (pullback p t : Scheme.{u})) :
    (finiteFlatDivisorCorrespondence p t r I).val z =
      letI := (AlgebraicCycle.fundamentalCycle_genericPoints_finite I.subscheme).fintype
      ∑ x : genericPoints I.subscheme,
        if z = (I.subschemeι ≫ r) x.val then
          ((Module.length (I.subscheme.presheaf.stalk x.val)
            (I.subscheme.presheaf.stalk x.val)).toNat : ℤ) *
              ((I.subschemeι ≫ r).residueDegree x.val : ℤ)
        else 0 := by
  exact finiteCyclePushforward_ofGenericCoefficients_apply _ _ _ z

/-- Literal effective Cartier divisors give exactly the existing whole finite flat
correspondences, with no change of ambient map, multiplicities, or target. -/
@[colib_tag "COL-1051"]
theorem pushforwardCycle_effectiveCartierWeilDivisor [IsIntegral C]
    (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) :
    AlgebraicGeometry.WeilDivisor.pushforwardCycle r (effectiveCartierWeilDivisor I hI) =
      (finiteFlatDivisorCorrespondence p t r I).val := by
  change noetherianCyclePushforward r
    (AlgebraicGeometry.WeilDivisor.toAlgebraicCycle (effectiveCartierWeilDivisor I hI)) = _
  rw [toAlgebraicCycle_effectiveCartierWeilDivisor,
    ← noetherianCyclePushforward_eq_finiteCyclePushforward I.subschemeι,
    noetherianCyclePushforward_comp_apply,
    noetherianCyclePushforward_eq_finiteCyclePushforward (I.subschemeι ≫ r)]
  rfl

end Stacks.Chow
