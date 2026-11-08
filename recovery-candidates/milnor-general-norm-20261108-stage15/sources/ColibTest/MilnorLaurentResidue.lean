module

import Colib.RingTheory.KTheory.MilnorK.Norm.LaurentResidue

noncomputable section

open Polynomial IsLocalRing Module Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] {d : ℕ}

local instance (p : MonicIrreducibleOfDegree k d) : Fact (poly p).Monic :=
  ⟨monic p⟩

local instance (p : MonicIrreducibleOfDegree k d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ⟨(monic p).irreducible_map_laurentSeries_C (irreducible p)⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    IsDomain (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.isDomain_of_irreducible_map_residue ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))

local instance (p : MonicIrreducibleOfDegree k d) :
    IsLocalRing (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.isLocalRing_of_irreducible_map_residue ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))

local instance (p : MonicIrreducibleOfDegree k d) :
    IsDiscreteValuationRing
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) := by
  apply AdjoinRoot.isDiscreteValuationRing ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  ((monic p).map _).finite_adjoinRoot

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.IsTorsionFree (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) := by
  apply AdjoinRoot.isTorsionFree_of_prime_of_degree_ne_zero
    (AdjoinRoot.prime_of_irreducible_map_residue ((monic p).map _)
      ((monic p).irreducible_map_powerSeries_C_residue (irreducible p)))
  apply ne_of_gt
  apply natDegree_pos_iff_degree_pos.mp
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance (p : MonicIrreducibleOfDegree k d) : IsLocalHom
    (algebraMap (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.isLocalHom_of_monic ((monic p).map _)

local instance (p : MonicIrreducibleOfDegree k d) :
    Algebra (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  (Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl)).toAlgebra

local instance (p : MonicIrreducibleOfDegree k d) :
    IsScalarTower (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (Stacks.AdjoinRootFraction.toMapAdjoinRoot_of (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl) a).symm

local instance (p : MonicIrreducibleOfDegree k d) :
    IsFractionRing
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl) (RingEquiv.refl _) ((monic p).map _)
    (by ext <;> rfl)

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite k (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ((monic p).map _).finite_adjoinRoot

variable [CharZero k] (p : MonicIrreducibleOfDegree k d)
  [Normal k (AdjoinRoot (poly p))]

local instance : CharZero (ResidueField (PowerSeries k)) :=
  RingHom.charZero PowerSeries.residueFieldOfPowerSeries.toRingHom

local instance : CharZero (LaurentSeries k) :=
  charZero_of_injective_algebraMap (algebraMap k (LaurentSeries k)).injective

example (hp : d.Prime)
    (y : MilnorKRing
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))))) :
    milnorKRingMap PowerSeries.residueFieldOfPowerSeries.toRingHom
        (milnorKNormRing (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) y) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom y) :=
  milnorKNormRing_powerSeriesResidueEquiv p hp y

example (hp : d.Prime) (n : ℕ)
    (y : MilnorKTheory
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (milnorKNorm (ResidueField (PowerSeries k))
          (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) n y) =
      milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom n y) :=
  milnorKNorm_powerSeriesResidueEquiv p hp n y

example (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1)) :
    milnorKTheoryMap PowerSeries.residueFieldOfPowerSeries.toRingHom n
        (dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) n
          (milnorKNorm (LaurentSeries k)
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (n + 1) x)) =
      milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap (AdjoinRoot.powerSeriesResidueEquiv (poly p)).toRingHom n
          (dvrMilnorTameSymbol'
            (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
            (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) n x)) :=
  dvrMilnorTameSymbol'_milnorKNorm_laurentSeries p hp n x

example
    (a : AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :
    algebraMap
        (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
        (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) a =
      Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
        (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
        (q := (poly p).map (algebraMap k (LaurentSeries k)))
        (by rw [Polynomial.map_map]; rfl) a := rfl
