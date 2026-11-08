/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRPrimeCharZero
public import StacksFrontier.RingTheory.DiscreteValuationRing.MonicResidueIrreducible
public import StacksFrontier.RingTheory.AdjoinRoot.FractionRing

/-!
# The chosen norm and residue in the actual monogenic unramified presentation

For a monic polynomial over a DVR with irreducible reduction, take the original
AdjoinRoot algebra and the actual root field after passing to the base fraction
field. The local DVR, finite module, fraction field and scalar tower structures
are constructed from the existing native comparison map. They are not assumed
as comparison data, and no normalization, norm or residue carrier is introduced.

If the generic root field is normal of prime degree and the base residue field
has characteristic zero, the native chosen norm commutes with the native DVR
residue. This is a concrete application of the established prime-Galois DVR
square, not the full rational finite-place branch sum or the prime norm diamond.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module

universe u

namespace Stacks.Chow

variable (R F : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  (p : R[X]) [Fact p.Monic] [Fact (Irreducible (p.map (residue R)))]

local instance : Fact (Irreducible (p.map (algebraMap R F))) :=
  ⟨AdjoinRoot.irreducible_map_algebraMap_of_irreducible_map_residue
    (Fact.out : p.Monic) (Fact.out : Irreducible (p.map (residue R)))⟩

local instance : IsDomain (AdjoinRoot p) :=
  AdjoinRoot.isDomain_of_irreducible_map_residue
    (Fact.out : p.Monic) (Fact.out : Irreducible (p.map (residue R)))

local instance : IsLocalRing (AdjoinRoot p) :=
  AdjoinRoot.isLocalRing_of_irreducible_map_residue
    (Fact.out : p.Monic) (Fact.out : Irreducible (p.map (residue R)))

local instance : IsDiscreteValuationRing (AdjoinRoot p) := by
  have hpos : 0 < p.natDegree := by
    have h := (Fact.out : Irreducible (p.map (residue R))).natDegree_pos
    rwa [(Fact.out : p.Monic).natDegree_map] at h
  exact AdjoinRoot.isDiscreteValuationRing (Fact.out : p.Monic)
    (Fact.out : Irreducible (p.map (residue R))) hpos

local instance : Module.Finite R (AdjoinRoot p) := (Fact.out : p.Monic).finite_adjoinRoot

local instance : Module.IsTorsionFree R (AdjoinRoot p) := by
  have hpos : 0 < p.natDegree := by
    have h := (Fact.out : Irreducible (p.map (residue R))).natDegree_pos
    rwa [(Fact.out : p.Monic).natDegree_map] at h
  exact AdjoinRoot.isTorsionFree_of_prime_of_degree_ne_zero
    (AdjoinRoot.prime_of_irreducible_map_residue (Fact.out : p.Monic)
      (Fact.out : Irreducible (p.map (residue R))))
    (ne_of_gt (natDegree_pos_iff_degree_pos.mp hpos))

local instance : IsLocalHom (algebraMap R (AdjoinRoot p)) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.isLocalHom_of_monic (Fact.out : p.Monic)

local instance : Algebra (AdjoinRoot p) (AdjoinRoot (p.map (algebraMap R F))) :=
  (Stacks.AdjoinRootFraction.toMapAdjoinRoot F (p := p) rfl).toAlgebra

local instance : IsScalarTower R (AdjoinRoot p) (AdjoinRoot (p.map (algebraMap R F))) := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change AdjoinRoot.of _ (algebraMap R F r) =
    Stacks.AdjoinRootFraction.toMapAdjoinRoot F rfl (AdjoinRoot.of p r)
  exact (Stacks.AdjoinRootFraction.toMapAdjoinRoot_of F rfl r).symm

local instance : IsFractionRing (AdjoinRoot p) (AdjoinRoot (p.map (algebraMap R F))) :=
  Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot F rfl (RingEquiv.refl _)
    (Fact.out : p.Monic) (by ext <;> rfl)

local instance : FiniteDimensional F (AdjoinRoot (p.map (algebraMap R F))) :=
  ((Fact.out : p.Monic).map _).finite_adjoinRoot

variable [CharZero (ResidueField R)] [Normal F (AdjoinRoot (p.map (algebraMap R F)))]

/-- The actual chosen norm commutes with the actual residue in the literal
monogenic fraction-field presentation. All local and fraction structures are
constructed above from monicity and irreducibility of the original reduction. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_adjoinRoot_of_monic_residue_prime
    (hprime : p.natDegree.Prime) (n : ℕ)
    (x : MilnorKTheory (AdjoinRoot (p.map (algebraMap R F))) (n + 1)) :
    dvrMilnorTameSymbol' R F n
        (milnorKNorm F (AdjoinRoot (p.map (algebraMap R F))) (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField (AdjoinRoot p)) n
        (dvrMilnorTameSymbol' (AdjoinRoot p) (AdjoinRoot (p.map (algebraMap R F))) n x) := by
  let : CharZero R := RingHom.charZero (residue R)
  let : CharZero F := IsFractionRing.charZero_of_isFractionRing R
  let : IsGalois F (AdjoinRoot (p.map (algebraMap R F))) :=
    { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hdegree : finrank F (AdjoinRoot (p.map (algebraMap R F))) = p.natDegree := by
    rw [AdjoinRoot.finrank_eq_natDegree ((Fact.out : p.Monic).map _),
      (Fact.out : p.Monic).natDegree_map]
  apply dvrMilnorTameSymbol'_milnorKNorm_of_prime_galois_of_charZero R (AdjoinRoot p)
    F (AdjoinRoot (p.map (algebraMap R F)))
  rwa [hdegree]

end Stacks.Chow
