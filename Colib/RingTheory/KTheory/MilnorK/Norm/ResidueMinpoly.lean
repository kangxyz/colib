/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.WeightedBranches
public import Colib.FieldTheory.AdjoinRoot.ResidueMinpoly

/-!
# Native chosen norms through actual residue minimal-polynomial fibers

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/ResidueMinpoly.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 27–123.
The original embedding factors through its literal quotient. Native norm
transitivity and norm–restriction degree then compute the actual contribution.
The second theorem groups the complete finite sum by these actual fibers.
-/

@[expose] public noncomputable section

open Polynomial AdjoinRoot

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree
attribute [local instance] Ideal.Quotient.field
attribute [local instance] AdjoinRoot.instFactIrreduciblePolynomialPoly_colib

/-- The chosen norm along the original residue embedding has the actual relative
residue degree as its multiplicity in the literal minimal-polynomial branch. -/
theorem milnorKNorm_minpolyScalarBranch
    {k A M V : Type u} [Field k] [Field A] [Field M] [CharZero M] [Field V]
    [Algebra k A] [Algebra k M] [Algebra M V] [Algebra k V]
    [IsScalarTower k M V] [FiniteDimensional M V]
    (B : PowerBasis k A) (φ : A →ₐ[k] V) (n : ℕ) (x : MilnorKTheory A n) :
    let _ : FiniteDimensional M
        (AdjoinRoot (poly (minpolyScalarBranch (M := M) B φ).1.2)) :=
      (AdjoinRoot.powerBasis' (monic (minpolyScalarBranch (M := M) B φ).1.2)).finite
    milnorKNorm M V n (milnorKTransport φ.toRingHom n x) =
      Module.finrank (IntermediateField.adjoin M {φ B.gen}) V •
        milnorKNorm M (AdjoinRoot (poly (minpolyScalarBranch (M := M) B φ).1.2)) n
          (milnorKTransport
            ((AdjoinRoot.map (algebraMap k M) (minpoly k B.gen)
              (poly (minpolyScalarBranch (M := M) B φ).1.2)
              (minpolyScalarBranch (M := M) B φ).2).comp
                (powerBasisMinpolyEquiv B).symm.toRingHom) n x) := by
  intro hFinite
  let q := minpolyScalarBranch (M := M) B φ
  let W := AdjoinRoot (poly q.1.2)
  let f := minpolyScalarBranchLift (M := M) B φ
  -- The branch action is its actual root-evaluation ring map.
  let branchAlgebra : Algebra W V := f.toRingHom.toAlgebra
  have : IsScalarTower M W V := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : FiniteDimensional W V := FiniteDimensional.right M W V
  have hdegree : Module.finrank (IntermediateField.adjoin M {φ B.gen}) V =
      Module.finrank W V := minpolyScalarBranch_finrank B φ
        (minpolyScalarBranchLift_root B φ)
  have hmap : milnorKTransport φ.toRingHom n x =
      milnorKTransport (algebraMap W V) n
        (milnorKTransport
          ((AdjoinRoot.map (algebraMap k M) (minpoly k B.gen) (poly q.1.2) q.2).comp
            (powerBasisMinpolyEquiv B).symm.toRingHom) n x) := by
    rw [milnorKTransport_comp_apply]
    have hm := minpolyScalarBranchLift_comp_presentation_symm (M := M) B φ
    change milnorKTransport φ.toRingHom n x = milnorKTransport
      (f.toRingHom.comp ((AdjoinRoot.map (algebraMap k M) (minpoly k B.gen)
        (poly q.1.2) q.2).comp (powerBasisMinpolyEquiv B).symm.toRingHom)) n x
    rw [← RingHom.comp_assoc, hm]
  rw [hmap, ← milnorKNorm_tower (k := M) (M := W),
    milnorKNorm_milnorKTransport, map_zsmul, natCast_zsmul, hdegree]

open scoped Classical in
/-- A count on the literal minimal-polynomial fibers gives the original weighted
residue norm sum, retaining each original residue embedding. -/
theorem milnorKNorm_map_eq_weighted_residue_sum
    {k A M : Type u} [Field k] [CharZero k] [Field A] [Field M] [CharZero M]
    [Algebra k A] [FiniteDimensional k A] [Algebra k M]
    {ι : Type u} [Fintype ι] (V : ι → Type u)
    [∀ i, Field (V i)] [∀ i, Algebra M (V i)] [∀ i, Algebra k (V i)]
    [∀ i, IsScalarTower k M (V i)] [∀ i, FiniteDimensional M (V i)]
    (B : PowerBasis k A) (φ : ∀ i, A →ₐ[k] V i) (b : ι → ℕ) (a : ℕ)
    (hcount : ∀ q : {r : Σ d : ℕ, MonicIrreducibleOfDegree M d //
        poly r.2 ∣ (minpoly k B.gen).map (algebraMap k M)},
      (∑ i, if minpoly M (φ i B.gen) = poly q.1.2 then
        b i * Module.finrank (IntermediateField.adjoin M {φ i B.gen}) (V i) else 0) = a)
    (n : ℕ) (x : MilnorKTheory A n) :
    a • milnorKTransport (algebraMap k M) n (milnorKNorm k A n x) =
      ∑ i, b i • milnorKNorm M (V i) n (milnorKTransport (φ i).toRingHom n x) := by
  classical
  let p := minpolyOfDegree k B.isIntegral_gen
  let ε : A ≃ₐ[k] AdjoinRoot (poly p) := (powerBasisMinpolyEquiv B).symm
  let J := {r : Σ d : ℕ, MonicIrreducibleOfDegree M d //
    poly r.2 ∣ (poly p).map (algebraMap k M)}
  -- Enumerate the actual full scalar-factor subtype.
  let branchFintype : Fintype J := coefficientFactorFintype (algebraMap k M) (poly p) (ne_zero p)
  have : ∀ r : J, FiniteDimensional M (AdjoinRoot (poly r.1.2)) :=
    fun r => (AdjoinRoot.powerBasis' (monic r.1.2)).finite
  let q : ι → J := fun i => minpolyScalarBranch (M := M) B (φ i)
  let d := fun i => Module.finrank (IntermediateField.adjoin M {φ i B.gen}) (V i)
  let t := fun r : J => milnorKNorm M (AdjoinRoot (poly r.1.2)) n
    (milnorKTransport
      ((AdjoinRoot.map (algebraMap k M) (poly p) (poly r.1.2) r.2).comp ε.toRingHom) n x)
  have hindex (i : ι) (r : J) :
      (minpoly M (φ i B.gen) = poly r.1.2) ↔ q i = r := by
    constructor
    · intro h
      exact Subtype.ext (sigma_poly_injective h)
    · intro h
      exact congrArg (fun j : J => poly j.1.2) h
  have hcount' (r : J) : (∑ i, if q i = r then b i * d i else 0) = a := by
    simpa only [hindex] using hcount r
  have hterm (i : ι) : milnorKNorm M (V i) n (milnorKTransport (φ i).toRingHom n x) =
      d i • t (q i) := milnorKNorm_minpolyScalarBranch B (φ i) n x
  rw [milnorKNorm_map_eq_sum_scalarFactors_of_algEquiv_of_fintype p ε]
  change a • (∑ r : J, t r) = _
  calc
    a • (∑ r : J, t r) = ∑ r : J, a • t r := Finset.smul_sum
    _ = ∑ r : J, (∑ i, if q i = r then b i * d i else 0) • t r := by
      simp_rw [hcount']
    _ = ∑ i, (b i * d i) • t (q i) := by
      simp_rw [Finset.sum_smul, ite_smul, zero_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single (q i)]
      · simp
      · intro r _ hr
        simp [Ne.symm hr]
      · simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hterm, smul_smul]

end Stacks.Chow

end
