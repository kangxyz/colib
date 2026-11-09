module

import Colib.RingTheory.KTheory.MilnorK.Norm.MonicResiduePrime

noncomputable section

open Polynomial IsLocalRing Module Stacks.Chow

universe u

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

example
    (hprime : p.natDegree.Prime) (n : ℕ)
    (x : MilnorKTheory (AdjoinRoot (p.map (algebraMap R F))) (n + 1)) :
    dvrMilnorTameSymbol' R F n
        (milnorKNorm F (AdjoinRoot (p.map (algebraMap R F))) (n + 1) x) =
      milnorKNorm (ResidueField R) (ResidueField (AdjoinRoot p)) n
        (dvrMilnorTameSymbol' (AdjoinRoot p) (AdjoinRoot (p.map (algebraMap R F))) n x) :=
  dvrMilnorTameSymbol'_milnorKNorm_adjoinRoot_of_monic_residue_prime R F p hprime n x
