/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.BranchFactorNativeTransportSeparable

/-!
# A native p-group branch tower along a proved ring-hom square

Only polynomial identity and literal quotient-map compatibility are inputs.
There is no norm comparison hypothesis and no selected scalar-factor index.
-/

@[expose] public noncomputable section

open Polynomial

universe u v

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- An actual quotient comparison and a proved restriction square give the native branch law. -/
theorem simpleMilnorNorm_pGroup_tower_of_native_factor_square_of_isGalois
    {K : Type u} [Field K]
    {Ω : Type v} [Field Ω] [Algebra K Ω] [FiniteDimensional K Ω] [IsGalois K Ω]
    {Q H : Type u} [Field Q] [Field H]
    {d e m : ℕ} (r : MonicIrreducibleOfDegree K d) (s : MonicIrreducibleOfDegree K e)
    (i : AdjoinRoot (poly r) →ₐ[K] AdjoinRoot (poly s))
    (t : MonicIrreducibleOfDegree (AdjoinRoot (poly r)) m)
    (c : AdjoinRoot (poly t) ≃+* AdjoinRoot (poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2))
    (ε : AdjoinRoot (poly t) ≃+* AdjoinRoot (poly s))
    (hpoly : poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2 = (poly t).map (RingHom.id
      (AdjoinRoot (poly r))))
    (hdiv : poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2 ∣
      (poly t).map (RingHom.id (AdjoinRoot (poly r))))
    (hc : c.toRingHom = AdjoinRoot.map (RingHom.id (AdjoinRoot (poly r)))
      (poly t) (poly (AdjoinRoot.towerFactor (poly r) (poly s) i).1.2) hdiv)
    (hcomp : (AdjoinRoot.towerFactorRingEquiv (poly r) (poly s) i).toRingHom.comp c.toRingHom =
      ε.toRingHom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hG : IsPGroup ℓ (Ω ≃ₐ[K] Ω))
    (j : AdjoinRoot (poly s) →ₐ[K] Ω)
    (ρ : Q →+* AdjoinRoot (poly t)) (θ₀ : Q →+* H)
    (σ : H →+* AdjoinRoot (poly s))
    (hsquare : ε.toRingHom.comp ρ = σ.comp θ₀) (x : MilnorKRing Q) :
    simpleMilnorNorm r (simpleMilnorNorm t (milnorKRingMap ρ x)) =
      simpleMilnorNorm s (milnorKRingMap σ (milnorKRingMap θ₀ x)) := by
  have hnorm := simpleMilnorNorm_pGroup_tower_of_native_factor_comparison_of_isGalois
    r s i t c ε hpoly hdiv hc hcomp ℓ hG j (milnorKRingMap ρ x)
  have hleft := milnorKRingMap_comp_apply ρ ε.toRingHom x
  have hright := milnorKRingMap_comp_apply θ₀ σ x
  have hsquareApply := congrArg
    (fun ψ : Q →+* AdjoinRoot (poly s) => milnorKRingMap ψ x) hsquare
  have hmaps := hleft.trans (hsquareApply.trans hright.symm)
  have htop := congrArg (simpleMilnorNorm s) hmaps
  exact hnorm.trans htop

end Stacks.Chow
end
