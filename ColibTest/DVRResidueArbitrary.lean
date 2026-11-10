/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Charpoly.DVRResidueArbitrary

/-! Actual characteristic-polynomial consumers, including explicitly finite residue fields. -/

@[expose] public noncomputable section

open Algebra Polynomial IsLocalRing

namespace ColibTest.DVRResidueArbitrary

/-- The native scalar characteristic-polynomial formula also applies over a finite base field. -/
theorem finite_local_algebra_charpoly
    {k B : Type*} [Field k] [Finite k] [CommRing B] [Algebra k B]
    [Module.Finite k B] [IsLocalRing B] (b : B) :
    (lmul k B b).charpoly =
      (lmul k (ResidueField B) (residue B b)).charpoly ^ (Module.length B B).toNat :=
  charpoly_lmul_eq_residue_charpoly_pow_length b

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]

/-- The original residue-minpoly formula, retaining all actual uniformizer data. -/
theorem actual_dvr_minpoly
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    (lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^
        (e * Module.finrank
          (IntermediateField.adjoin (ResidueField R) {residue S b}) (ResidueField S)) :=
  residue_charpoly_lmul_eq_minpoly_pow_arbitrary R S hπ hϖ u e he b

/-- The power-basis specialization over an explicitly finite residue field. -/
theorem finite_residue_powerBasis [Finite (ResidueField R)]
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S)
    (B : PowerBasis (ResidueField R) (ResidueField S)) (hB : B.gen = residue S b) :
    (lmul R S b).charpoly.map (residue R) =
      (minpoly (ResidueField R) (residue S b)) ^ e :=
  residue_charpoly_lmul_eq_minpoly_pow_of_powerBasis_arbitrary R S hπ hϖ u e he b B hB

end ColibTest.DVRResidueArbitrary
