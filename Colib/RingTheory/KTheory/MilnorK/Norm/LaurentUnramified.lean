/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRMixed
public import Colib.RingTheory.KTheory.MilnorK.Symbols.QuadraticMixed
public import Colib.RingTheory.AdjoinRoot.PowerSeriesResidue
public import StacksFrontier.RingTheory.DiscreteValuationRing.MonicResidueIrreducible
public import StacksFrontier.RingTheory.AdjoinRoot.FractionRing
public import Colib.FieldTheory.AdjoinRoot.Separable

/-!
# The actual unramified Laurent norm-residue square on mixed and quadratic classes

The original constant monogenic power-series root algebra has ramification index
one. The proof uses its literal image of PowerSeries.X and the native local
AdjoinRoot theorem, without deducing tame ramification from generic separability.
This gives the existing chosen norm-residue square on the actual mixed span in
any degree and on every class for a quadratic constant extension, in arbitrary
characteristic. The residue and generic extensions are separately proved
separable from separability of the original defining polynomial.

No norm, field, residue carrier or coefficient map is replaced. The target
of the square is the actual residue field. The unrestricted all-symbol square
in higher prime degree is not asserted here.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing Module

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] {d : ℕ}

local instance laurentUnramified_factMonic (p : MonicIrreducibleOfDegree k d) :
    Fact (poly p).Monic :=
  ⟨monic p⟩

local instance laurentUnramified_factIrreducible (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance laurentUnramified_factIrreducibleLaurent (p : MonicIrreducibleOfDegree k d) :
    Fact (Irreducible ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ⟨(monic p).irreducible_map_laurentSeries_C (irreducible p)⟩

local instance laurentUnramified_isDomain (p : MonicIrreducibleOfDegree k d) :
    IsDomain (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.isDomain_of_irreducible_map_residue ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))

local instance laurentUnramified_isLocalRing (p : MonicIrreducibleOfDegree k d) :
    IsLocalRing (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  AdjoinRoot.isLocalRing_of_irreducible_map_residue ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))

local instance laurentUnramified_isDiscreteValuationRing (p : MonicIrreducibleOfDegree k d) :
    IsDiscreteValuationRing
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) := by
  apply AdjoinRoot.isDiscreteValuationRing ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance laurentUnramified_finitePowerSeries (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) :=
  ((monic p).map _).finite_adjoinRoot

local instance laurentUnramified_torsionFreePowerSeries (p : MonicIrreducibleOfDegree k d) :
    Module.IsTorsionFree (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) := by
  apply AdjoinRoot.isTorsionFree_of_prime_of_degree_ne_zero
    (AdjoinRoot.prime_of_irreducible_map_residue ((monic p).map _)
      ((monic p).irreducible_map_powerSeries_C_residue (irreducible p)))
  apply ne_of_gt
  apply natDegree_pos_iff_degree_pos.mp
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance laurentUnramified_isLocalHom (p : MonicIrreducibleOfDegree k d) : IsLocalHom
    (algebraMap (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.isLocalHom_of_monic ((monic p).map _)

/-- The canonical algebra from the power-series root ring to the Laurent root field. -/
local instance laurentUnramifiedAlgebra (p : MonicIrreducibleOfDegree k d) :
    Algebra (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  (Stacks.AdjoinRootFraction.toMapAdjoinRoot (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl)).toAlgebra

local instance laurentUnramified_isScalarTower (p : MonicIrreducibleOfDegree k d) :
    IsScalarTower (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (Stacks.AdjoinRootFraction.toMapAdjoinRoot_of (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl) a).symm

local instance laurentUnramified_isFractionRing (p : MonicIrreducibleOfDegree k d) :
    IsFractionRing
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot (LaurentSeries k)
    (p := (poly p).map (PowerSeries.C : k →+* PowerSeries k))
    (q := (poly p).map (algebraMap k (LaurentSeries k)))
    (by rw [Polynomial.map_map]; rfl) (RingEquiv.refl _) ((monic p).map _)
    (by ext <;> rfl)

local instance laurentUnramified_finiteConstant (p : MonicIrreducibleOfDegree k d) :
    Module.Finite k (AdjoinRoot (poly p)) := (monic p).finite_adjoinRoot

local instance laurentUnramified_finiteLaurent (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  ((monic p).map _).finite_adjoinRoot

variable (p : MonicIrreducibleOfDegree k d)

/-- The literal power-series parameter stays a uniformizer in the original
constant monogenic root DVR. No separability assumption is needed. -/
theorem irreducible_powerSeriesRoot_X :
    Irreducible (algebraMap (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) PowerSeries.X) := by
  apply AdjoinRoot.irreducible_algebraMap ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))
  · rw [(monic p).natDegree_map]
    exact (irreducible p).natDegree_pos
  · exact PowerSeries.X_irreducible

/-- The actual constant root DVR has ramification index one in every characteristic.
This is independent of whether the original residue-field extension is separable. -/
theorem ramificationIdx_powerSeriesRoot_eq_one :
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx (PowerSeries k)
      (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k))) = 1 := by
  apply AdjoinRoot.ramificationIdx_eq_one ((monic p).map _)
    ((monic p).irreducible_map_powerSeries_C_residue (irreducible p))
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

/-- The literal residue polynomial remains separable under the two actual
coefficient maps. This is a polynomial statement, not an inference from the
separability of a generic DVR extension. -/
theorem separable_powerSeriesRoot_residuePolynomial (hsep : (poly p).Separable) :
    (((poly p).map (PowerSeries.C : k →+* PowerSeries k)).map
      (residue (PowerSeries k))).Separable :=
  hsep.map.map

/-- The original constant root extension is separable when its polynomial is. -/
theorem isSeparable_powerSeriesRoot_constant (hsep : (poly p).Separable) :
    Algebra.IsSeparable k (AdjoinRoot (poly p)) :=
  AdjoinRoot.isSeparable_of_polynomial_separable (poly p) hsep

/-- Separability of the actual Laurent root field comes from the original
separable constant polynomial and its literal coefficient map. -/
theorem isSeparable_laurentSeriesRoot (hsep : (poly p).Separable) :
    Algebra.IsSeparable (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) :=
  AdjoinRoot.isSeparable_of_polynomial_separable _ hsep.map

/-- The actual residue extension is separable through the established residue
comparison, including its proved coefficient square. -/
theorem isSeparable_powerSeriesRoot_residue (hsep : (poly p).Separable) :
    Algebra.IsSeparable (ResidueField (PowerSeries k))
      (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) := by
  let : Algebra.IsSeparable k (AdjoinRoot (poly p)) :=
    isSeparable_powerSeriesRoot_constant p hsep
  apply (Algebra.IsSeparable.iff_of_equiv_equiv
    PowerSeries.residueFieldOfPowerSeries (AdjoinRoot.powerSeriesResidueEquiv (poly p)) ?_).mpr
      inferInstance
  ext a
  exact (AdjoinRoot.powerSeriesResidueEquiv_algebraMap (poly p) a).symm

/-- The native chosen Laurent norm commutes with actual residues on the original
mixed span. The original image of X gives exponent one with unit coefficient one. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_mem_mixedSpan
    (m : ℕ) (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1))
    (hx : x ∈ milnorKMixedSpan (algebraMap (LaurentSeries k)
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))) m) :
    dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) m
        (milnorKNorm (LaurentSeries k)
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1) x) =
      milnorKNorm (ResidueField (PowerSeries k))
        (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) m
        (dvrMilnorTameSymbol'
          (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x) := by
  exact dvrMilnorTameSymbol'_milnorKNorm_of_mem_mixedSpan_of_exponent_one
    (PowerSeries k)
    (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
    (LaurentSeries k)
    (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k))))
    PowerSeries.X_irreducible (irreducible_powerSeriesRoot_X p) 1
    (by simp only [Units.val_one, one_mul]) m x hx

/-- The complete degree-one norm-residue square for every constant extension,
with no degree, normality, characteristic or separability restriction. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_degree_one
    (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 1) :
    dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) 0
        (milnorKNorm (LaurentSeries k)
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 1 x) =
      milnorKNorm (ResidueField (PowerSeries k))
        (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) 0
        (dvrMilnorTameSymbol'
          (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) 0 x) :=
  dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_mem_mixedSpan p 0 x
    (mem_milnorKMixedSpan_zero _ x)

/-- In quadratic degree the actual mixed span contains every class, so the native
chosen norm-residue square holds in every degree and every characteristic. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_degree_le_two
    (hd : d ≤ 2) (m : ℕ) (x : MilnorKTheory
      (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1)) :
    dvrMilnorTameSymbol' (PowerSeries k) (LaurentSeries k) m
        (milnorKNorm (LaurentSeries k)
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) (m + 1) x) =
      milnorKNorm (ResidueField (PowerSeries k))
        (ResidueField (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))) m
        (dvrMilnorTameSymbol'
          (AdjoinRoot ((poly p).map (PowerSeries.C : k →+* PowerSeries k)))
          (AdjoinRoot ((poly p).map (algebraMap k (LaurentSeries k)))) m x) := by
  apply dvrMilnorTameSymbol'_milnorKNorm_laurentSeries_of_mem_mixedSpan p m x
  apply mem_milnorKMixedSpan_of_natDegree_le_two _ ((monic p).map _)
  rwa [(monic p).natDegree_map, natDegree_eq p]

end Stacks.Chow
