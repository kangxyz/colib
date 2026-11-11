/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionDegree
import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MilnorSymbol
import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PolynomialNormComparisonAll
import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.SymbolFieldChange
import Colib.FieldTheory.RatFunc.FrobeniusParameter
import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenInseparableTrace
import Mathlib.Algebra.Field.ZMod

/-!
# Diagonal motivic symbols in positive characteristic

The ordered tuple of the parameter and its complement gives the literal
Steinberg graph in characteristics two and three. Power substitution in
characteristic three tests the degree-three transfer law and the norm
comparison in every weight.
-/

noncomputable section

open AlgebraicGeometry.MotivicCohomology Stacks.Chow
open DiagonalCorestriction DiagonalCycleSymbols DiagonalFieldChange
open DiagonalMilnorSymbol DiagonalPolynomialNormComparisonAll DiagonalSteinbergBound
open DiagonalSymbolFieldChange
open scoped RatFunc

namespace ColibTest.NativeMotivicPositiveCharacteristic

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def parameterUnit (k : Type) [Field k] : (RatFunc k)ˣ :=
  Units.mk0 RatFunc.X (by
    rw [← RatFunc.algebraMap_X]
    exact (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).2
      Polynomial.X_ne_zero)

private def complementUnit (k : Type) [Field k] : (RatFunc k)ˣ :=
  Units.mk0 (1 - RatFunc.X) (by
    have hX : (Polynomial.X : Polynomial k) ≠ 1 := by
      simpa only [Polynomial.C_1, sub_ne_zero] using Polynomial.X_sub_C_ne_zero (1 : k)
    have h := (map_ne_zero_iff (algebraMap (Polynomial k) (RatFunc k))
      (IsFractionRing.injective (Polynomial k) (RatFunc k))).2 (sub_ne_zero.mpr hX.symm)
    simpa only [map_sub, map_one, RatFunc.algebraMap_X] using h)

private abbrev parameterTuple (k : Type) [Field k] : Fin 2 → (RatFunc k)ˣ :=
  ![parameterUnit k, complementUnit k]

example : graphSymbol (RatFunc (ZMod 2)) 2 (parameterTuple (ZMod 2)) = 0 :=
  graphSymbol_steinberg _ (parameterUnit (ZMod 2)) (complementUnit (ZMod 2)) rfl

example : graphSymbol (RatFunc (ZMod 3)) 2 (parameterTuple (ZMod 3)) = 0 :=
  graphSymbol_steinberg _ (parameterUnit (ZMod 3)) (complementUnit (ZMod 3)) rfl

example : rawSymbol (RatFunc (ZMod 2)) 2 (milnorKTupleSymbol (parameterTuple (ZMod 2))) = 0 := by
  rw [rawSymbol_symbol]
  exact graphSymbol_steinberg _ (parameterUnit (ZMod 2)) (complementUnit (ZMod 2)) rfl

example : rawSymbol (RatFunc (ZMod 3)) 2 (milnorKTupleSymbol (parameterTuple (ZMod 3))) = 0 := by
  rw [rawSymbol_symbol]
  exact graphSymbol_steinberg _ (parameterUnit (ZMod 3)) (complementUnit (ZMod 3)) rfl

section PurelyInseparable

local notation "K" => RatFunc (ZMod 3)

-- Both fields have the same carrier. Select the substitution action and its module.
local instance (priority := 10000) parameterAlgebra : Algebra K K :=
  RatFunc.frobeniusParameterAlgebra (ZMod 3) 3 (by decide)

local instance (priority := 10000) : Module K K := parameterAlgebra.toModule

local instance : Module.Finite K K :=
  RatFunc.finite_frobeniusParameterAlgebra (ZMod 3) 3 (by decide)

local instance : IsPurelyInseparable K K :=
  RatFunc.isPurelyInseparable_frobeniusParameterAlgebra (ZMod 3) 3 (by decide)

private theorem parameterDegree : Module.finrank K K = 3 :=
  RatFunc.finrank_frobeniusParameterAlgebra (ZMod 3) 3 (by decide)

example : algebraMap K K (RatFunc.X : K) = RatFunc.X ^ 3 :=
  RatFunc.frobeniusParameter_X (ZMod 3) 3 (by decide)

example :
    let x := graphSymbol K 1 ![parameterUnit (ZMod 3)]
    corestriction (k := K) (E := K) 1 (fieldChange (algebraMap K K) 1 x) = (3 : ℤ) • x := by
  dsimp only
  rw [corestriction_fieldChange, parameterDegree]
  rfl

example (q : ℕ) (x : MilnorKTheory K q) :
    rawSymbol K q (milnorKNorm K K q x) =
      corestriction (k := K) (E := K) q (rawSymbol K q x) :=
  rawSymbol_milnorKNorm (k := K) (E := K) q x

example (q : ℕ) (x : MilnorKTheory K q) :
    fieldChange (algebraMap K K) q (corestriction (k := K) (E := K) q (rawSymbol K q x)) =
      (3 : ℤ) • rawSymbol K q x := by
  have hTrace : milnorKTheoryMap (algebraMap K K) q (milnorKNorm K K q x) =
      (Module.finrank K K : ℤ) • x :=
    milnorKTheoryMap_milnorKNorm_of_isPurelyInseparable q x
  rw [← rawSymbol_milnorKNorm (k := K) (E := K) q x, rawSymbol_fieldChange, hTrace, map_zsmul,
    parameterDegree]
  rfl

end PurelyInseparable

end ColibTest.NativeMotivicPositiveCharacteristic
