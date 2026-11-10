/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRSquareEquiv
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Native norm-residue compatibility for a degree-one field extension

Adapted from `Aglib/KTheory/MilnorK/Norm/FiniteExtension/CompleteDegreeOne.lean`
at revision `4f65be4eafa8964bd1f7a83682e99aa8165bd418`. This concerns field
extension degree one in every Milnor degree, not merely the map from K₁ to K₀.
The actual integral closure and original fraction maps are retained. Completeness
is not assumed; characteristic-zero hypotheses are preserved from the source.
-/

@[expose] public noncomputable section

namespace Stacks.Chow

open IsLocalRing

universe u v

/-- A degree-one field extension satisfies the native residue square in every degree. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_of_finrank_eq_one
    (R S : Type v) (F E : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero (ResidueField R)]
    [Field F] [CharZero F] [Algebra R F] [IsFractionRing R F]
    [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra R E] [IsScalarTower R F E]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [IsLocalHom (algebraMap R S)]
    [Algebra S E] [IsScalarTower R S E] [IsFractionRing S E]
    [IsIntegralClosure S R E]
    (hd : Module.finrank F E = 1) (n : ℕ) (x : MilnorKTheory E (n + 1)) :
    dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField S) n (dvrMilnorTameSymbol' S E n x) := by
  let ε : F ≃ₐ[F] E := AlgEquiv.ofBijective (Algebra.ofId F E)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd)
  let j₀ : R ≃ₐ[R] integralClosure R F := IsIntegralClosure.equiv R R F _
  let j₁ : integralClosure R F ≃ₐ[R] integralClosure R E :=
    (ε.restrictScalars R).mapIntegralClosure
  let j₂ : integralClosure R E ≃ₐ[R] S := IsIntegralClosure.equiv R _ E S
  let j : R ≃ₐ[R] S := (j₀.trans j₁).trans j₂
  have hj (r : R) : ε (algebraMap R F r) = algebraMap S E (j r) := by
    dsimp only [j, AlgEquiv.trans_apply, j₂]
    rw [IsIntegralClosure.algebraMap_equiv]
    change ε (algebraMap R F r) = ε (algebraMap (integralClosure R F) F (j₀ r))
    rw [IsIntegralClosure.algebraMap_equiv]
  apply dvrMilnorTameSymbol'_milnorKNorm_of_algEquiv j ε hj n (fun y => ?_) x
  have hself : milnorKNorm F F (n + 1) y = y := by
    apply Subtype.ext
    rw [coe_milnorKNorm]
    have h := milnorKNormRing_milnorKRingMap (K := F) (L := F) (y : MilnorKRing F)
    change milnorKNormRing F F (milnorKRingMap (RingHom.id F) (y : MilnorKRing F)) =
      (Module.finrank F F : ℤ) • (y : MilnorKRing F) at h
    simpa only [milnorKRingMap_id_apply, Module.finrank_self, Nat.cast_one, one_smul] using h
  rw [hself]
  let : Algebra (ResidueField R) (ResidueField R) := ResidueField.instAlgebra
  have hid : algebraMap (ResidueField R) (ResidueField R) = RingHom.id _ := by
    ext a
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
    rfl
  have hbij : Function.Bijective (algebraMap (ResidueField R) (ResidueField R)) := by
    rw [hid]
    exact Function.bijective_id
  have hdegree := Module.finrank_of_bijective_algebraMap hbij
  apply Subtype.ext
  rw [coe_milnorKNorm]
  have h := milnorKNormRing_milnorKRingMap (K := ResidueField R) (L := ResidueField R)
    (dvrMilnorTameSymbol' R F n y : MilnorKRing (ResidueField R))
  rw [hid, milnorKRingMap_id_apply, hdegree, Nat.cast_one, one_smul] at h
  exact h.symm

end Stacks.Chow

end
