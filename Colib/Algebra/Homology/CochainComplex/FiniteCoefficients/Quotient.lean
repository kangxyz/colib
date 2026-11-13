/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# The canonical map from finite coefficients to the coefficient quotient

The original multiplication cone maps to the actual categorical cokernel of
multiplication. The quotient is strictly annihilated by the coefficient level.
This does not assert that the map is a quasi-isomorphism without a monomorphism
hypothesis, or identify the integral cone with a complex of `ZMod` modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex.finiteCoefficients

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual cokernel of multiplication on the original cochain complex. -/
def quotient (K : CochainComplex C ℤ) (n : ℕ) : CochainComplex C ℤ :=
  cokernel (n • 𝟙 K)

/-- The original complex maps to its coefficient quotient. -/
def quotientπ (K : CochainComplex C ℤ) (n : ℕ) : K ⟶ quotient K n :=
  cokernel.π (n • 𝟙 K)

/-- The native cone-to-cokernel map, with the original integral coordinate. -/
@[colib_tag "COL-1225",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/Algebra/Homology/HomotopyCategory/ShortExact.lean:53-57,138-154" "specialization"
    "Native cone-to-cokernel map; quasi-isomorphism requires multiplication to be mono"]
def toQuotient (K : CochainComplex C ℤ) (n : ℕ) :
    finiteCoefficients K n ⟶ quotient K n :=
  mappingCone.descShortComplex (ShortComplex.cokernelSequence (n • 𝟙 K))

/-- The cone comparison retains the actual integral reduction map. -/
@[reassoc (attr := simp)]
theorem integral_toQuotient (K : CochainComplex C ℤ) (n : ℕ) :
    integral K n ≫ toQuotient K n = quotientπ K n :=
  mappingCone.inr_descShortComplex (ShortComplex.cokernelSequence (n • 𝟙 K))

/-- The coefficient quotient, unlike its cone presentation, is strictly killed by `n`. -/
theorem nsmul_id_quotient (K : CochainComplex C ℤ) (n : ℕ) :
    n • 𝟙 (quotient K n) = 0 := by
  change n • 𝟙 (cokernel (n • 𝟙 K)) = 0
  apply (cancel_epi (cokernel.π (n • 𝟙 K))).1
  simpa only [Preadditive.comp_nsmul, Category.comp_id, Preadditive.nsmul_comp,
    Category.id_comp, comp_zero] using cokernel.condition (n • 𝟙 K)

/-- Every actual term of the quotient is killed by the coefficient level. -/
theorem nsmul_id_quotient_X (K : CochainComplex C ℤ) (n : ℕ) (i : ℤ) :
    n • 𝟙 ((quotient K n).X i) = 0 := by
  have h := congrArg (fun f => f.f i) (nsmul_id_quotient K n)
  simpa using h

/-- When multiplication is mono, the original coefficient cone computes the quotient. -/
theorem quasiIso_toQuotient (K : CochainComplex C ℤ) (n : ℕ)
    [Mono (n • 𝟙 K)] : QuasiIso (toQuotient K n) := by
  unfold toQuotient
  apply mappingCone.quasiIso_descShortComplex
  exact ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _)
    (by change Mono (n • 𝟙 K); infer_instance) inferInstance

end CochainComplex.finiteCoefficients
