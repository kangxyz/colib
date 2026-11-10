/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRCompletePGroupDescent
public import Colib.FieldTheory.SylowFixedField
public import Colib.FieldTheory.AdjoinRootSplitBranchEmbedding

/-!
# General complete-DVR norm-residue compatibility

Actual Sylow coefficient extensions annihilate the local defect by coprime
field degrees. All upper branches and ramification factors are supplied by
the proved complete integral-closure descent theorem.

Adapted from `Aglib/KTheory/MilnorK/Norm/Polynomial/Complete.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`. The original
residue-characteristic-zero assumptions, actual coefficient fields and
integral closures are retained. All norm maps are the existing native chosen norms.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open Polynomial MonicIrreducibleOfDegree AdjoinRoot IsLocalRing
open IsDiscreteValuationRing.CompleteExtension

attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

universe u

/-- The actual chosen norm on every monic irreducible quotient satisfies the complete-DVR
residue square in every positive source degree. The target degree includes zero. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_complete_adjoinRoot
    (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d)
    (n : ℕ) (x : MilnorKTheory (AdjoinRoot (poly p)) (n + 1)) :
    let _ := (AdjoinRoot.powerBasis' (monic p)).finite
    let _ := integralClosure_isDiscreteValuationRing R F (AdjoinRoot (poly p))
    let _ := integralClosure_isLocalHom R F (AdjoinRoot (poly p))
    let _ := IsIntegralClosure.isFractionRing_of_finite_extension R F (AdjoinRoot (poly p))
      (integralClosure R (AdjoinRoot (poly p)))
    let _ := integralClosure_residue_finite R F (AdjoinRoot (poly p))
    dvrMilnorTameSymbol' R F n (milnorKNorm F (AdjoinRoot (poly p)) (n + 1) x) =
      milnorKNorm (ResidueField R)
          (ResidueField (integralClosure R (AdjoinRoot (poly p)))) n
          (dvrMilnorTameSymbol' (integralClosure R (AdjoinRoot (poly p)))
            (AdjoinRoot (poly p)) n x) := by
  classical
  dsimp only
  apply sub_eq_zero.mp
  apply AddMonoid.addOrderOf_eq_one_iff.mp
  by_contra h
  obtain ⟨ℓ, hℓ, hdiv⟩ := Nat.exists_prime_and_dvd h
  let : Fact ℓ.Prime := ⟨hℓ⟩
  let Ω := (poly p).SplittingField
  let : IsGalois F Ω := ⟨⟩
  let P : Sylow ℓ (Ω ≃ₐ[F] Ω) := Classical.arbitrary _
  let L := IntermediateField.fixedField (P : Subgroup (Ω ≃ₐ[F] Ω))
  let : Algebra R L := (algebraMap F L).comp (algebraMap R F) |>.toAlgebra
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let g (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap F L)}) :
      AdjoinRoot (poly r.1.2) →ₐ[L] Ω := Classical.choice
    (nonempty_algHom_branch_of_splits (L := L) (Ω := Ω)
      (poly p) (ne_zero p) (SplittingField.splits (poly p))
      (poly r.1.2) (irreducible r.1.2) r.2).1
  have hz := finrank_smul_norm_residue_difference_complete_of_pGroup_branches
    R F L p Ω ℓ (IntermediateField.isPGroup_aut_over_sylow_fixedField ℓ P) g n x
  exact (hℓ.coprime_iff_not_dvd.mp
    (IntermediateField.coprime_finrank_sylow_fixedField ℓ P))
    (hdiv.trans (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz))

end Stacks.Chow

end
