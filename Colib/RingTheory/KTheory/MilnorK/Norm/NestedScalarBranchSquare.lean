/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.NestedTowerFactor
public import Colib.RingTheory.KTheory.MilnorK.Norm.BranchFactorNativeSquare

/-!
# A native norm identity for one actual matched scalar-factor branch

The actual nested-factor index selects the lower and relative polynomials.
Accepted canonical-factor comparisons and the original quotient-map square
specialize the atomic native branch-square theorem. The result retains the
original source quotient, top quotient, coefficient maps and Milnor element.

This module proves one branch identity, not the complete restricted sum or
unrestricted tower. A finite Galois p-group overfield and actual top-factor
embedding are explicit inputs. The overfield has an independent universe.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field

attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The actual matched branch norm respects the original coefficient-factor square. -/
theorem simpleMilnorNorm_nestedScalarFactor_pGroup_square
    {k K : Type u} [Field k] [Field K] [CharZero K]
    (φ : k →+* K) {d e : ℕ}
    (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
    (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))
    (s : {s : Σ a : ℕ, MonicIrreducibleOfDegree K a //
      poly s.2 ∣ (poly h).map φ})
    {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
    (j : AdjoinRoot (poly s.1.2) →ₐ[K] Ω)
    (x : MilnorKRing (AdjoinRoot (poly (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2))) :
    simpleMilnorNorm (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1.1.2
      (simpleMilnorNorm (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2.1.2
      (milnorKRingMap (AdjoinRoot.map (AdjoinRoot.map φ (poly p) (poly
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1.1.2)
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1.2) (poly
      (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (poly
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2.1.2)
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2.2) x)) =
      simpleMilnorNorm s.1.2 (milnorKRingMap (AdjoinRoot.map φ (poly h) (poly s.1.2) s.2)
      (milnorKRingMap ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom) x)) := by
  exact simpleMilnorNorm_pGroup_tower_of_native_factor_square
    ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).1).1.2
    s.1.2
    (AdjoinRoot.nestedScalarFactorLowerAlgHom φ (poly p) (poly h) f s)
    ((AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2).1.2
    (AdjoinRoot.nestedScalarFactorTowerRingEquiv φ (poly p) (poly h) f s)
    (AdjoinRoot.nestedScalarFactorQuotientEquiv φ (poly p) (poly h) f s).toRingEquiv
    (AdjoinRoot.nestedScalarFactor_towerFactor_poly_eq_map_id φ (poly p) (poly h) f s)
    (AdjoinRoot.nestedScalarFactor_towerFactor_dvd_map_id φ (poly p) (poly h) f s)
    (AdjoinRoot.nestedScalarFactorTowerRingEquiv_toRingHom φ (poly p) (poly h) f s)
    (AdjoinRoot.nestedScalarFactorTowerRingEquiv_comp_towerFactorRingEquiv
      φ (poly p) (poly h) f s)
    ℓ hG j
    (AdjoinRoot.map (AdjoinRoot.map φ (poly p) (poly (AdjoinRoot.nestedScalarFactorIndexEquiv φ
      (poly p) (poly h) f s).1.1.2) (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f
      s).1.2) (poly (AdjoinRoot.towerFactor (poly p) (poly h) f).1.2) (poly
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2.1.2)
      (AdjoinRoot.nestedScalarFactorIndexEquiv φ (poly p) (poly h) f s).2.2)
    ((AdjoinRoot.towerFactorRingEquiv (poly p) (poly h) f).toRingHom)
    (AdjoinRoot.map φ (poly h) (poly s.1.2) s.2)
    (AdjoinRoot.nestedScalarFactorQuotientEquiv_maps φ (poly p) (poly h) f s).2.2 x

end Stacks.Chow
end
